#!/usr/bin/env python3
"""Write the table of SEARCH.md from the answers of the literature search.

Usage: python3 -I verification/novelty/search.py

Run quotes.py first. The script reads units.json, the answers in
verification/review/codex-novelty and quotes.json there, prints the counts that SEARCH.md
quotes, and replaces the lines of SEARCH.md between the two table marks and between the two marks of
the list of differences. The prose and the small tables of SEARCH.md are written by hand.
"""
import collections
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
ANS = HERE.parent / "review" / "codex-novelty"


def short(citation):
    """Authors and year of a citation written as authors, title, place, year."""
    authors = citation.split(",")[0].strip()
    m = re.match(r"(.+? and [^,]+|[^,]+(?:, [^,]+)*?, and [^,]+|[^,]+)", citation)
    authors = m.group(1) if m else authors
    year = re.findall(r"\b(1[6-9]\d\d|20\d\d)\b", citation)
    return f"{authors} {year[-1]}" if year else authors


def main():
    batches = json.loads((HERE / "units.json").read_text())["batches"]
    quotes = collections.defaultdict(list)
    for q in json.loads((ANS / "quotes.json").read_text()):
        quotes[q["id"]].append(q["state"])
    counts = collections.Counter()
    diffs = []
    conf = collections.Counter()
    lines = []
    for batch in batches:
        lines += ["", f"**{batch['title']}**", "",
                  "| Unit | Class | Confidence | Technique in the words of the answer | Nearest source | Quotes |",
                  "|---|---|---|---|---|---|"]
        for u in json.loads((ANS / f"{batch['batch']}.json").read_text()):
            kind = "timeline" if u["id"].startswith("T") else "claim"
            counts[kind, u["class"]] += 1
            conf[u["class"], u["confidence"]] += 1
            first = u["technique"].split(". ")[0].rstrip(".").replace("|", "/") + "."
            near = short(u["nearest"][0]["citation"]) if u["nearest"] else "none"
            st = quotes[u["id"]]
            q = "none" if not st else f"{sum(s != 'unopened' for s in st)} of {len(st)}"
            if u["class"] in "ANU":
                diffs.append(f"- **{u['id']}**, class {u['class']}. {u['difference'].strip()}")
            lines.append(f"| {u['id']} | {u['class']} | {u['confidence']} | {first} | {near} | {q} |")
    for key in sorted(counts):
        print(*key, counts[key])
    for key in sorted(conf):
        print("confidence", *key, conf[key])
    doc = HERE / "SEARCH.md"
    text = doc.read_text()
    a, b = "<!-- table starts -->", "<!-- table ends -->"
    text = text[:text.index(a) + len(a)] + "\n" + "\n".join(lines) + "\n\n" + text[text.index(b):]
    a, b = "<!-- differences start -->", "<!-- differences end -->"
    text = text[:text.index(a) + len(a)] + "\n\n" + "\n".join(diffs) + "\n\n" + text[text.index(b):]
    doc.write_text(text)


main()
