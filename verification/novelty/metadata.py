#!/usr/bin/env python3
"""Compare the citations of the literature search with the records of three catalogues.

Usage: python3 -I verification/novelty/metadata.py [answers folder]

The answers folder defaults to verification/review/codex-novelty. A citation is the field
`citation` of a source of an answer, one line of text with the authors, the title, the place of
publication and the year, as the model wrote it. The script looks for records of each different
citation in arXiv, Crossref and zbMATH and compares the citation with every record that it
finds, field by field.

Where a record comes from

  arxiv      the address or the citation holds an arXiv identifier, and the record is the
             answer of the arXiv interface for it
  doi        the Crossref record of a DOI that the address holds or that the arXiv record names
  search     Crossref is asked for the whole citation as free text, when no DOI gave a record,
             and an answer is taken whose title stands in the citation word for word and whose
             first author stands there too
  zbmath     zbMATH Open is asked for a title, first for the titles of the records found so
             far and then for each part of the citation between two commas, and an answer is
             taken by the same rule

A work can have several records in one catalogue, of the first printing and of reprints. The
script then takes the record with a year that the citation gives, if there is one. When it has
to take a record whose year and place both differ from the citation, and a record of another
catalogue confirms the year of the citation, the first record counts as a reprint and is not
held against the year, the place, the volume or the pages.

What is compared

  authors    every family name of the record stands in the part of the citation before the
             title, and that part holds as many names as the record has authors
  title      the words of the title of the record stand in the citation in order
  year       a year of the citation is one of the years of the record. A record of Crossref
             has up to three years, of the printed issue, of the online version and of the
             issue as catalogued. An arXiv record has the years of its first and its last
             version, and a zbMATH record the year of the volume or the book.
  place      the words of the journal or the book series of the record stand in the citation,
             in full or as initials
  volume     the volume of the record stands in the citation after the title
  pages      the pages that the citation gives are the pages of the record

Against one record a field gets one of four outcomes. `same` means that the citation agrees
with the record. `differs` means that the citation gives something else. `absent` means that
the citation does not give the field. `no data` means that the record does not give it. Over
all the records of a citation the field is `same` when it agrees with at least one record,
`differs` when it agrees with none and differs from at least one, and otherwise `absent` or
`no data`. The note of a field names the records that it differs from, also when another
record agrees.

A citation without a record in any catalogue cannot be compared by the script. The table READ
holds the outcome of a reading of such a citation against another source, and the script copies
it into the output.

The script keeps the answers of the catalogues in data/catalogue next to itself, which git
ignores, writes metadata.json into the answers folder and prints the counts. A citation that
agrees with its records is a correct description of that work. Whether the work says what the
answer takes from it is another question, which quotes.py approaches.
"""
import hashlib
import html
import json
import pathlib
import re
import subprocess
import sys
import time
import unicodedata
import urllib.parse
import xml.etree.ElementTree as ET

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "data" / "catalogue"
AGENT = "citation-metadata-check/1.0"
ARXIV = re.compile(r"arxiv\.org/(?:abs|pdf|html)/((?:[a-z\-]+/\d{7})|(?:\d{4}\.\d{4,5}))|arXiv:(\d{4}\.\d{4,5})", re.I)
DOI = re.compile(r"(10\.\d{4,9}/[^\s?#]+)")
SMALL = {"a", "an", "the", "of", "on", "and", "for", "in", "to", "de", "la", "le", "les", "des", "du", "sur", "et", "i", "series"}


def words(text):
    text = unicodedata.normalize("NFKD", text or "")
    text = "".join(c for c in text if not unicodedata.combining(c)).lower()
    text = text.replace("ß", "ss").replace("ø", "o").replace("ł", "l")
    text = re.sub(r"<[^>]+>|\$|\\[a-z]+", " ", text)
    return re.findall(r"[a-z0-9]+", text)


def fetch(url, good):
    """The answer of a catalogue for one address. An answer is kept only when it holds `good`."""
    CACHE.mkdir(parents=True, exist_ok=True)
    path = CACHE / hashlib.md5(url.encode()).hexdigest()[:12]
    for attempt in range(5):
        if path.exists() and good in path.read_text(errors="replace"):
            return path.read_text(errors="replace")
        # a pause before every call, longer for arXiv, whose interface asks for it
        time.sleep((4 if "arxiv.org" in url else 1) + 20 * attempt)
        subprocess.run(["curl", "-sL", "-m", "60", "-A", AGENT, "-o", str(path), url])
    text = path.read_text(errors="replace") if path.exists() else ""
    if good not in text:
        path.unlink(missing_ok=True)
        if "Resource not found" in text:
            return ""
        raise SystemExit("The catalogue gave no usable answer for " + url)
    return text


def crossref_record(item, how):
    year = lambda key: (item.get(key, {}).get("date-parts") or [[None]])[0][0]
    return {
        "how": how,
        "id": "doi:" + item.get("DOI", ""),
        "authors": [a.get("family") or a.get("name", "") for a in item.get("author", [])],
        "title": html.unescape((item.get("title") or [""])[0]),
        "kind": item.get("type", ""),
        "years": sorted({y for y in (year("published-print"), year("published-online"), year("issued")) if y}),
        "place": html.unescape((item.get("container-title") or [""])[0]),
        "places": [html.unescape(c) for c in item.get("container-title") or []],
        "volume": item.get("volume", ""),
        "pages": item.get("page", ""),
    }


def crossref_doi(doi, how="doi"):
    text = fetch("https://api.crossref.org/works/" + urllib.parse.quote(doi, safe="/"), '"status":"ok"')
    try:
        return crossref_record(json.loads(text)["message"], how)
    except (ValueError, KeyError):
        return None


def crossref_search(citation):
    text = fetch("https://api.crossref.org/works?rows=8&query.bibliographic=" + urllib.parse.quote(citation), '"status":"ok"')
    try:
        items = json.loads(text)["message"]["items"]
    except (ValueError, KeyError):
        return None
    cited_words = words(citation)
    cited = " " + " ".join(cited_words) + " "
    years = {int(y) for y in re.findall(r"\b(1[5-9]\d\d|20\d\d)\b", citation)}
    hits = []
    for item in items:
        record = crossref_record(item, "search")
        title = words(record["title"])
        family = words(record["authors"][0]) if record["authors"] else []
        if len(title) >= 3 and " " + " ".join(title) + " " in cited and family and set(family) <= set(cited_words):
            hits.append(record)
    # a work can have several records, of the first printing and of reprints
    for record in hits:
        if years & set(record["years"]):
            return record
    if hits:
        hits[0]["other_edition"] = True
        return hits[0]
    return None


def arxiv_record(ident):
    text = fetch("http://export.arxiv.org/api/query?id_list=" + ident, "<published>")
    ns = {"a": "http://www.w3.org/2005/Atom", "x": "http://arxiv.org/schemas/atom"}
    try:
        entry = ET.fromstring(text).find("a:entry", ns)
        title = " ".join(entry.find("a:title", ns).text.split())
    except (ET.ParseError, AttributeError):
        return None
    get = lambda tag: (entry.find(tag, ns).text if entry.find(tag, ns) is not None else "")
    return {
        "how": "arxiv",
        "id": "arXiv:" + ident,
        "authors": [a.find("a:name", ns).text.split()[-1] for a in entry.findall("a:author", ns)],
        "title": title,
        "years": sorted({int(get("a:published")[:4]), int(get("a:updated")[:4])}),
        "place": get("x:journal_ref"),
        "volume": "",
        "pages": "",
        "places": [],
        "doi": get("x:doi"),
    }


def zbmath_record(item):
    source = item.get("source") or {}
    series = source.get("series") or []
    books = source.get("book") or []
    years = {item.get("year")} | {s.get("year") for s in series} | {b.get("year") for b in books}
    pages = source.get("pages") or ""
    if not re.fullmatch(r"\d+\s*[-–]\s*\d+", pages.strip()):
        found = re.search(r"(\d+)-(\d+) \(\d{4}\)", source.get("source") or "")
        pages = found.group(1) + "-" + found.group(2) if found else ""
    code = (item.get("document_type") or {}).get("code")
    return {
        "how": "zbmath",
        "id": "Zbl " + item["identifier"] if item.get("identifier") else "zbMATH " + str(item.get("id")),
        "authors": [a["name"].split(",")[0] for a in item["contributors"]["authors"]],
        "title": item["title"]["title"] or "",
        "kind": {"j": "journal-article", "b": "book"}.get(code, "other"),
        "years": sorted({int(y) for y in years if y and str(y).isdigit()}),
        "place": series[0]["title"] if series else "",
        "places": [s[k] for s in series for k in ("title",) if s.get(k)],
        "volume": (series[0].get("volume") or "") if series else "",
        "pages": pages,
        "source": source.get("source") or "",
    }


def zbmath_search(citation, hints):
    cited_words = words(citation)
    cited = " " + " ".join(cited_words) + " "
    years = {int(y) for y in re.findall(r"\b(1[5-9]\d\d|20\d\d)\b", citation)}
    parts = [s.strip(" .“”\"") for s in citation.split(", ")]
    guesses = list(hints) + parts[1:] + [a + ", " + b for a, b in zip(parts[1:], parts[2:])]
    asked = set()
    for guess in guesses:
        guess = re.sub(r"[\"“”«»]", " ", guess).strip()
        key = " ".join(words(guess))
        if len(key.split()) < 3 or key in asked:
            continue
        asked.add(key)
        family = words(parts[0])[-1:] if parts and words(parts[0]) else []
        hits = []
        for query in ('ti:"' + guess + '"', " ".join(family + [re.sub(r"[^\w\s]", " ", guess)])):
            url = ("https://api.zbmath.org/v1/document/_search?results_per_page=10&search_string="
                   + urllib.parse.quote(query))
            try:
                items = json.loads(fetch(url, '"status"')).get("result") or []
            except ValueError:
                items = []
            for item in items:
                if str(item.get("identifier") or "").startswith("arXiv"):
                    continue  # a preprint entry, which the arXiv record covers
                record = zbmath_record(item)
                title = words(record["title"])
                author = words(record["authors"][0]) if record["authors"] else []
                if not author or not set(author) <= set(cited_words):
                    continue
                stands = " " + " ".join(title) + " " in cited
                longer = len(key.split()) >= 4 and title[:len(key.split())] == key.split()
                if (stands and len(title) >= 3) or longer or (stands and len(title) == 2 and years & set(record["years"])):
                    hits.append(record)
            if hits:
                break
        for record in hits:
            if years & set(record["years"]):
                return record
        if hits:
            hits[0]["other_edition"] = True
            return hits[0]
    return None


def find_records(citation, url):
    records = []
    m = ARXIV.search(url) or ARXIV.search(citation)
    if m:
        record = arxiv_record(m.group(1) or m.group(2))
        if record:
            records.append(record)
            journal = crossref_doi(record["doi"]) if record.get("doi") else None
            if journal:
                records.append(journal)
    if not any(r["how"] == "doi" for r in records):
        m = DOI.search(urllib.parse.unquote(url))
        record = crossref_doi(re.sub(r"(\.pdf|/pdf|/full)$", "", m.group(1))) if m else None
        if not record and not (records and "arxiv" in words(citation)):
            record = crossref_search(citation)
        if record:
            records.append(record)
    record = zbmath_search(citation, [r["title"] for r in records if r["title"]])
    if record:
        records.append(record)
    return records


def run_at(needle, hay):
    """Index of the first place where the list needle stands in the list hay, or -1."""
    for i in range(len(hay) - len(needle) + 1):
        if hay[i:i + len(needle)] == needle:
            return i
    return -1


def plain(text):
    """The text without accents, of the same length, so that an index holds in both."""
    return "".join(unicodedata.normalize("NFKD", c)[0] for c in text)


def place_stands(place, tail):
    """Whether the words of a journal or series stand in the list tail, also as initials."""
    full = words(place)
    if not full:
        return False
    main = [w for w in full if w not in SMALL]
    if all(w in tail for w in main):
        return True
    # a catalogue can add the series or the country to the name of a journal
    lead = 0
    while lead < len(main) and main[lead] in tail:
        lead += 1
    if lead >= 3 or (lead >= 2 and len(main) - lead <= 2 and len(main[0]) > 3):
        return True
    for i in range(len(full)):
        for j in range(i + 3, len(full) + 1):
            run = full[i:j]
            for letters in ("".join(w[0] for w in run), "".join(w[0] for w in run if w not in SMALL)):
                rest = [w for w in full[:i] + full[j:] if w not in SMALL]
                if letters in tail and all(w in tail for w in rest):
                    return True
    return False


def compare(citation, record, lead=None):
    """Outcome and note for each field of one citation against one record."""
    cited = words(citation)
    out = {}
    pub = record
    # the title, or the title of the book that holds the part
    at, used = -1, []
    part_of_book = False
    title = words(record["title"])
    if title and run_at(title, cited) >= 0:
        at, used = run_at(title, cited), title
    if at < 0:
        for place in pub.get("places", []):
            if len(words(place)) >= 2 and run_at(words(place), cited) >= 0:
                at, used, part_of_book = run_at(words(place), cited), words(place), True
                break
    # a catalogue can add a remark in brackets to a title, such as the edition
    bare = words(re.sub(r"\([^)]*\)", " ", record["title"]))
    added = False
    if at < 0 and len(bare) >= 3 and bare != title and run_at(bare, cited) >= 0:
        at, used, added = run_at(bare, cited), bare, True
    longer = 0
    if at < 0 and title:
        longer = next((n for n in range(len(title) - 1, 3, -1) if run_at(title[:n], cited) >= 0), 0)
        if longer:
            at, used = run_at(title[:longer], cited), title[:longer]
    if not words(record["title"]):
        out["title"] = ("no data", "")
    elif added:
        out["title"] = ("same", "The record adds a remark in brackets to the title, which is `" + record["title"] + "`.")
    elif longer:
        out["title"] = ("differs", "The citation holds the first words of the title of the record, which is `" + record["title"] + "`.")
    elif part_of_book:
        out["title"] = ("same", "The record is the part `" + record["title"] + "` of the cited book.")
    elif at >= 0:
        out["title"] = ("same", "")
    else:
        out["title"] = ("differs", "The record has the title `" + pub["title"] + "`.")
    # the authors stand before the title
    head = citation
    if at >= 0:
        m = re.search(r"\W+".join(map(re.escape, lead or used[:3])), plain(citation), re.I)
        if m:
            head = citation[:m.start()]
    names = [n for n in re.split(r",\s*(?:and\s+)?|\s+and\s+", head.strip(" ,“\"")) if n.strip()]
    authors = record["authors"] or pub["authors"]
    if not authors:
        out["authors"] = ("no data", "")
    else:
        head_words = set(words(head))
        missing = [a for a in authors if not set(words(a)) <= head_words]
        if missing:
            out["authors"] = ("differs", "The citation lacks " + ", ".join(missing) + ".")
        elif head is not citation and len(names) != len(authors):
            out["authors"] = ("differs", f"The citation names {len(names)} and the record {len(authors)}.")
        else:
            out["authors"] = ("same", "")
    years = set(record["years"]) | set(pub["years"])
    cited_years = {int(y) for y in re.findall(r"\b(1[5-9]\d\d|20\d\d)\b", citation)}
    if not years:
        out["year"] = ("no data", "")
    elif not cited_years:
        out["year"] = ("absent", "")
    elif cited_years & years:
        out["year"] = ("same", "")
    elif record["how"] == "arxiv" and "arxiv" not in cited:
        out["year"] = ("no data", "")
    else:
        note = "The record has " + ", ".join(map(str, sorted(years))) + "."
        if pub.get("kind") == "journal-article" and pub["volume"] and record["how"] in ("doi", "search"):
            note += " A journal can date an article by the year of its volume, here volume " + pub["volume"] + ", and the record by the day it went online."
        out["year"] = ("differs", note)
    tail = cited[at + len(used):] if at >= 0 else cited
    places = [pl for pl in pub.get("places", []) or [pub["place"]] if pl]
    if record["how"] == "arxiv":
        if "arxiv" in cited:
            out["place"] = ("same", "")
        elif record["place"] and place_stands(re.split(r"[,(\d]", record["place"])[0], tail):
            out["place"] = ("same", "")
        else:
            out["place"] = ("no data", "")
    elif not places:
        out["place"] = ("no data", "")
    elif part_of_book or any(place_stands(pl, tail) for pl in places):
        out["place"] = ("same", "")
    elif pub.get("kind") in ("book", "monograph", "edited-book", "reference-book"):
        out["place"] = ("absent", "The citation gives the publisher, and the record names the series " + pub["place"] + ".")
    elif "arxiv" in tail:
        out["place"] = ("absent", "The citation gives the preprint, and the record names " + pub["place"] + ".")
    else:
        out["place"] = ("differs", "The record has `" + pub["place"] + "`.")
    volume = words(pub["volume"])
    pages = re.search(r"pp?\.\s*(\d+)\s*[–\-]+\s*(\d+)", citation)
    numbers = [w for w in tail if w.isdigit() and int(w) not in cited_years and not (pages and w in pages.groups())]
    if not volume:
        out["volume"] = ("no data", "")
    elif all(v in tail for v in volume):
        out["volume"] = ("same", "")
    elif numbers and out["place"][0] == "same":
        out["volume"] = ("differs", "The citation has " + ", ".join(numbers) + " and the record volume " + pub["volume"] + ".")
    else:
        out["volume"] = ("absent", "")
    rec_pages = re.findall(r"\d+", pub["pages"])
    if not pages:
        out["pages"] = ("absent", "")
    elif len(rec_pages) < 2:
        out["pages"] = ("no data", "")
    elif list(pages.groups()) == rec_pages[:2]:
        out["pages"] = ("same", "")
    else:
        out["pages"] = ("differs", "The record has pages " + pub["pages"] + ".")
    if (record.get("other_edition") or pub.get("other_edition")) and pub.get("kind") != "journal-article":
        for field in ("year", "place"):
            if out[field][0] == "differs":
                out[field] = ("differs", out[field][1] + " The record may be of another edition or a reprint.")
    return out


# Citations without a record in the three catalogues, read against another source by the language
# model Claude on 28 November 2026. The key is the start of the citation.
READ = {
    "Bernhard Riemann, Ueber die Anzahl": {
        "source": "the head of the opened file, the translation of Wilkins at claymath.org",
        "agrees": True,
        "note": "The file gives the German title, Monatsberichte der Berliner Akademie, November 1859, the translator David R. Wilkins and the date December 1998 of a preliminary version."},
    "Jean-Benoît Bost, Périodes et isogénies": {
        "source": "the cover page of the opened Numdam file and the record Zbl 0936.11042",
        "agrees": True,
        "note": "Both give Astérisque 237 of 1996. They add what the citation leaves out, that the text is exposé 795 of the Séminaire Bourbaki 1994/95 on pages 115 to 161, with the subtitle d'après D. Masser et G. Wüstholz. zbMATH holds the title in English, so the search by the French title did not find it."},
    "Pafnuty L. Chebyshev, Mémoire sur les nombres premiers": {
        "source": "the Numdam record JMPA_1852_1_17__366_0",
        "agrees": True,
        "note": "The record gives the title, the Journal de Mathématiques Pures et Appliquées, volume 17, 1852, and adds the pages 366 to 390. It spells the author Tchebichef, as the journal printed the name."},
    "James S. Milne, Algebraic Number Theory": {
        "source": "the title page of the opened file at jmilne.org",
        "agrees": True,
        "note": "The title page gives Version 3.08, July 19, 2020, and a BibTeX entry with the year 2020."},
    "Kiran S. Kedlaya, von Mangoldt": {
        "source": "the head of the opened file at kskedlaya.org",
        "agrees": True,
        "note": "The head reads 18.785: Analytic Number Theory, MIT, spring 2007 (K.S. Kedlaya), and the title von Mangoldt's formula follows."},
}

FIELDS = ("authors", "title", "year", "place", "volume", "pages")
NAMES = {"arxiv": "arXiv", "doi": "Crossref", "search": "Crossref", "zbmath": "zbMATH"}


def merge(per_record):
    """One outcome for each field from the outcomes against the single records."""
    out = {}
    # a record of a reprint says nothing against the year and the place of the cited printing
    dated = any(f["year"][0] == "same" for r, f in per_record)
    for r, f in per_record:
        if r.get("other_edition") and dated and f["year"][0] == "differs" and f["place"][0] == "differs":
            for field in ("year", "place", "volume", "pages"):
                if f[field][0] == "differs":
                    f[field] = ("no data", "")
    for field in FIELDS:
        got = [(r["id"], NAMES[r["how"]], f[field]) for r, f in per_record]
        outcomes = [g[2][0] for g in got]
        outcome = next(o for o in ("same", "differs", "absent", "no data") if o in outcomes)
        notes = [f"{name}, {ident}. {g[1]}" for ident, name, g in got if g[0] == "differs"]
        if outcome != "differs":
            notes += [g[1] for _, _, g in got if g[0] == outcome and g[1]][:1]
        out[field] = {"outcome": outcome, "note": " ".join(notes),
                      "against": {ident: g[0] for ident, _, g in got}}
    return out


def main():
    folder = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "verification/review/codex-novelty"
    batches = json.loads((HERE / "units.json").read_text())["batches"]
    cites = {}
    for batch in batches:
        for unit in json.loads((folder / f"{batch['batch']}.json").read_text()):
            for source in unit["nearest"]:
                entry = cites.setdefault(source["citation"], {"citation": source["citation"], "url": source["url"], "units": []})
                if unit["id"] not in entry["units"]:
                    entry["units"].append(unit["id"])
    rows = []
    for entry in cites.values():
        records = find_records(entry["citation"], entry["url"])
        row = dict(entry, records=records)
        if records:
            # the authors end where the earliest of the titles of the records begins
            cited = words(entry["citation"])
            starts = [(run_at(words(r["title"]), cited), words(r["title"])[:3]) for r in records if words(r["title"])]
            starts = sorted(s for s in starts if s[0] >= 0)
            lead = starts[0][1] if starts else None
            row["fields"] = merge([(r, compare(entry["citation"], r, lead)) for r in records])
        else:
            row["read"] = next((v for k, v in READ.items() if entry["citation"].startswith(k)), None)
        rows.append(row)
    (folder / "metadata.json").write_text(json.dumps(rows, ensure_ascii=False, indent=1) + "\n")
    print("citations", len(rows))
    for name in ("arXiv", "Crossref", "zbMATH"):
        print("with a record of", name, sum(1 for r in rows if any(NAMES[x["how"]] == name for x in r["records"])))
    for n in (0, 1, 2, 3):
        print("with records of", n, "catalogues", sum(1 for r in rows if len({NAMES[x["how"]] for x in r["records"]}) == n))
    none = [r for r in rows if not r["records"]]
    print("without a record and read against another source", sum(1 for r in none if r.get("read")),
          "of which agree", sum(1 for r in none if r.get("read") and r["read"]["agrees"]))
    for field in FIELDS:
        tally = {}
        for r in rows:
            if r["records"]:
                tally[r["fields"][field]["outcome"]] = tally.get(r["fields"][field]["outcome"], 0) + 1
        print(field, tally)
    print("with a record and no field that differs",
          sum(1 for r in rows if r["records"] and all(f["outcome"] != "differs" for f in r["fields"].values())))
    print("with a field that one record contradicts while another agrees",
          sum(1 for r in rows if r["records"] and any(
              f["outcome"] == "same" and "differs" in f["against"].values() for f in r["fields"].values())))


main()
