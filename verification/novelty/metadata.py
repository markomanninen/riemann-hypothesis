#!/usr/bin/env python3
"""Compare the citations of the literature search with the records of two catalogues.

Usage: python3 -I verification/novelty/metadata.py [answers folder]

The answers folder defaults to verification/review/codex-novelty. A citation is the field
`citation` of a source of an answer, one line of text with the authors, the title, the place of
publication and the year, as the model wrote it. The script finds a record for each different
citation and compares the citation with it field by field.

Where the record comes from

  arxiv      the address or the citation holds an arXiv identifier, and the record is the
             answer of the arXiv interface for it. When that record names a DOI, the Crossref
             record of the DOI is fetched as well, for the journal, the volume and the pages.
  doi        the address holds a DOI, and the record is the Crossref record of it
  search     Crossref is asked for the whole citation as free text, and the first of its
             answers whose title stands in the citation word for word is taken
  none       none of the three gave a record, so the citation is not compared

What is compared

  authors    every family name of the record stands in the part of the citation before the
             title, and that part holds as many names as the record has authors
  title      the words of the title of the record stand in the citation in order
  year       a year of the citation is one of the years of the record. A record of Crossref
             has up to three years, of the printed issue, of the online version and of the
             issue as catalogued, and an arXiv record has the year of each version.
  place      the words of the journal or the book series of the record stand in the citation
  volume     the volume of the record stands in the citation after the title
  pages      the pages that the citation gives are the pages of the record

Each field gets one of four outcomes. `same` means that the citation agrees with the record.
`differs` means that the citation gives something else, and the note says what. `absent` means
that the citation does not give the field. `no data` means that the record does not give it.

The script keeps the answers of the catalogues in data/catalogue next to itself, which git
ignores, writes metadata.json into the answers folder and prints the counts. A citation that
agrees with its record is a correct description of that work. Whether the work says what the
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
        time.sleep(4 + 20 * attempt)  # the arXiv interface asks for a pause between calls
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


def find_record(citation, url):
    m = ARXIV.search(url) or ARXIV.search(citation)
    if m:
        record = arxiv_record(m.group(1) or m.group(2))
        if record:
            journal = crossref_doi(record["doi"], "arxiv") if record.get("doi") else None
            if not journal and "arxiv" not in words(citation):
                journal = crossref_search(citation)
            if journal:
                record["journal"] = journal
            return record
    m = DOI.search(urllib.parse.unquote(url))
    if m:
        doi = re.sub(r"(\.pdf|/pdf|/full)$", "", m.group(1))
        record = crossref_doi(doi)
        if record:
            return record
    return crossref_search(citation)


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
    if all(w in tail for w in full if w not in SMALL):
        return True
    for i in range(len(full)):
        for j in range(i + 3, len(full) + 1):
            run = full[i:j]
            for letters in ("".join(w[0] for w in run), "".join(w[0] for w in run if w not in SMALL)):
                rest = [w for w in full[:i] + full[j:] if w not in SMALL]
                if letters in tail and all(w in tail for w in rest):
                    return True
    return False


def compare(citation, record):
    """Outcome and note for each field of one citation against one record."""
    cited = words(citation)
    out = {}
    pub = record.get("journal") or record
    # the title, of the preprint or of the printed version, or of the book that holds the part
    at, used = -1, []
    part_of_book = False
    for title in [words(record["title"]), words(pub["title"])]:
        here = run_at(title, cited) if title else -1
        if here >= 0 and (at < 0 or here < at):
            at, used = here, title
    if at < 0:
        for place in pub.get("places", []):
            if len(words(place)) >= 2 and run_at(words(place), cited) >= 0:
                at, used, part_of_book = run_at(words(place), cited), words(place), True
                break
    if not words(record["title"]):
        out["title"] = ("no data", "")
    elif part_of_book:
        out["title"] = ("same", "The record is the part `" + record["title"] + "` of the cited book.")
    elif at >= 0:
        out["title"] = ("same", "")
    else:
        out["title"] = ("differs", "The record has the title `" + pub["title"] + "`.")
    # the authors stand before the title
    head = citation
    if at >= 0:
        m = re.search(r"\W+".join(map(re.escape, used[:3])), plain(citation), re.I)
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
    else:
        note = "The record has " + ", ".join(map(str, sorted(years))) + "."
        if pub.get("kind") == "journal-article" and pub["volume"]:
            note += " A journal can date an article by the year of its volume, here volume " + pub["volume"] + ", and the record by the day it went online."
        out["year"] = ("differs", note)
    tail = cited[at + len(used):] if at >= 0 else cited
    places = [pl for pl in pub.get("places", []) or [pub["place"]] if pl]
    if record["how"] == "arxiv" and "journal" not in record:
        if "arxiv" in cited:
            out["place"] = ("same", "")
        elif record["place"] and place_stands(record["place"].split(",")[0].split("(")[0], tail):
            out["place"] = ("same", "The arXiv record names the journal, and no record of the journal was found.")
        else:
            out["place"] = ("differs", "The record is an arXiv preprint, and no record of a journal was found.")
    elif not places:
        out["place"] = ("no data", "")
    elif part_of_book or any(place_stands(pl, tail) for pl in places):
        out["place"] = ("same", "")
    elif pub.get("kind") in ("book", "monograph", "edited-book", "reference-book"):
        out["place"] = ("absent", "The citation gives the publisher, and the record names the series " + pub["place"] + ".")
    elif "arxiv" in tail and record["how"] == "arxiv":
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


FIELDS = ("authors", "title", "year", "place", "volume", "pages")


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
        record = find_record(entry["citation"], entry["url"])
        row = dict(entry, record=record)
        if record:
            row["fields"] = {k: {"outcome": v[0], "note": v[1]} for k, v in compare(entry["citation"], record).items()}
        rows.append(row)
    (folder / "metadata.json").write_text(json.dumps(rows, ensure_ascii=False, indent=1) + "\n")
    print("citations", len(rows))
    for how in ("arxiv", "doi", "search"):
        print("record by", how, sum(1 for r in rows if r["record"] and r["record"]["how"] == how))
    print("no record", sum(1 for r in rows if not r["record"]))
    for field in FIELDS:
        tally = {}
        for r in rows:
            if r["record"]:
                tally[r["fields"][field]["outcome"]] = tally.get(r["fields"][field]["outcome"], 0) + 1
        print(field, tally)
    clean = sum(1 for r in rows if r["record"] and all(f["outcome"] != "differs" for f in r["fields"].values()))
    print("with a record and no field that differs", clean)


main()
