#!/usr/bin/env python3
"""Open every source that the literature search cites and look for its quote there.

Usage: python3 -I verification/novelty/quotes.py [answers folder]

The answers folder defaults to verification/review/codex-novelty. It holds one JSON file for
each batch of units.json, in the format of brief-gemini.md.

For each cited source the script downloads the address with curl into data/sources next to
itself, which git ignores, and turns a PDF into text with pdftotext. It then splits the quote
and the text into words of letters and digits and finds the longest run of consecutive words
of the quote that stands in the text. A quote whose every word stands there in order is
`found`. The language model Claude read the places of the other quotes on 28 November 2026, and
the table READ below holds the outcome of that reading.

  found       every word of the quote stands in the downloaded text in order
  read        a formula, a line break or a scanned page broke the match, and the quote was
              found by reading the text at the place named in READ
  unopened    the address gave no readable text to this script, so the quote is unchecked

The script writes quotes.json into the answers folder and prints the counts. A found quote
says that the words stand in the source. It leaves open whether the source supports the class
that the answer gives.
"""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import unicodedata

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "data" / "sources"

# (unit, start of the address after https://) -> (state, note of the reading)
READ = {
    ("1.1", "www.cambridge.org"): ("read", "The quote stands in Corollary 1. A formula splits it in the text layer."),
    ("1.2", "ndl.ethernet.edu.et"): ("unopened", "The address returned a web page without the text of the book."),
    ("1.3", "ndl.ethernet.edu.et"): ("unopened", "The address returned a web page without the text of the book."),
    ("2.2", "personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1986"): ("read", "The scanned text reads `contains at least one sign change off(s)` after (2.2)."),
    ("2.2", "personal.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1984"): ("read", "The words stand in Theorem 1, with the conditions (1.7) between them in the scan."),
    ("2.3", "www.numdam.org/article/SB_1994-1995"): ("read", "The sentence stands in the text with the symbol of the map between its words."),
    ("3.5", "dms.umontreal.ca"): ("read", "The text layer of this copy is unreadable. The sentence stands before Proposition 2.2 in arXiv:math/0206031."),
    ("3.8", "www.ams.org"): ("unopened", "The site answered with a page that checks the connection."),
    ("5.3", "numdam.org/item/10.1007"): ("read", "The quote is formula (4.11) of Proposition 4.5, which stands in the text over several lines."),
    ("5.5", "www2.math.ethz.ch"): ("unopened", "The address answered 404."),
    ("7.1", "heuklyd.github.io"): ("read", "The sentence stands before formula (4), with the integral sign as another character."),
    ("7.1", "www.cambridge.org"): ("read", "The quote is formula 2.1 on page 317, read from the image of the scanned page."),
    ("7.2", "www.cambridge.org"): ("read", "The quote is formula 1.1 on page 316, read from the image of the scanned page."),
    ("7.2", "link.springer.com"): ("unopened", "The address returned a page without the text of the article."),
    ("7.4", "heuklyd.github.io"): ("read", "The quote is formula (4), which stands in the text over several lines."),
    ("9.3", "www.mathnet.ru"): ("unopened", "The address returned a web page without the text of the article."),
    ("9.3", "www.numdam.org/article/SB_1972-1973"): ("read", "The scanned text reads `vanishes at every fixed point of`, then the symbol of the map, then `except at`."),
    ("10.2", "annals.math.princeton.edu"): ("read", "The sentence opens Theorem 2.1.1. The group is written with a subscript in the text."),
    ("10.2", "www.ams.org"): ("unopened", "The site answered with a page that checks the connection."),
    ("T1", "www.numdam.org/item/SB_1972-1973"): ("read", "The scanned text reads `consider derivatives an hyperderivatives of f` with the words out of order."),
    ("T2", "arxiv.org/pdf/math/0610163"): ("read", "The sentence stands in the introduction, with a page header between its words."),
    ("T6", "arxiv.org/pdf/math/0507368"): ("read", "The source reads `for all positive integer n`, one letter away from the quote."),
    ("T9", "arxiv.org/pdf/1207.4709"): ("read", "The sentence stands after Theorem 1.3, with a line of a formula before `L(s, π)`."),
    ("T19", "www.pnas.org"): ("unopened", "The site returned no text of the article."),
    ("T19", "page-one.springer.com"): ("read", "The sentence stands in Proposition 13.1, with subscripts spaced apart in the scan."),
}


def words(text):
    text = unicodedata.normalize("NFKD", text).replace("ﬁ", "fi").replace("ﬂ", "fl").lower()
    return re.findall(r"[a-z0-9]+", text)


def source_text(url):
    CACHE.mkdir(parents=True, exist_ok=True)
    raw = CACHE / hashlib.md5(url.encode()).hexdigest()[:10]
    txt = raw.with_suffix(".txt")
    if not txt.exists():
        subprocess.run(["curl", "-sL", "-m", "90", "-A", "Mozilla/5.0", "-o", str(raw), url])
        kind = subprocess.run(["file", "-b", str(raw)], capture_output=True, text=True).stdout
        if "PDF" in kind:
            subprocess.run(["pdftotext", str(raw), str(txt)], stderr=subprocess.DEVNULL)
        else:
            page = raw.read_bytes().decode("utf8", "replace") if raw.exists() else ""
            txt.write_text(re.sub(r"<[^>]+>", " ", page))
    return txt.read_text(errors="replace") if txt.exists() else ""


def longest_run(quote, text):
    best = 0
    for i in range(len(quote)):
        for j in range(len(quote), i + best, -1):
            if " " + " ".join(quote[i:j]) + " " in text:
                best = j - i
                break
    return best


def main():
    folder = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "verification/review/codex-novelty"
    batches = json.loads((HERE / "units.json").read_text())["batches"]
    rows = []
    for batch in batches:
        for unit in json.loads((folder / f"{batch['batch']}.json").read_text()):
            for source in unit["nearest"]:
                url = source["url"]
                text = " " + " ".join(words(source_text(url))) + " "
                quote = words(source["quote"])
                run = longest_run(quote, text)
                state, note = "found", ""
                if run < len(quote):
                    key = next((k for k in READ if k[0] == unit["id"] and url.split("//", 1)[1].startswith(k[1])), None)
                    state, note = READ[key] if key else ("unopened", "The quote was not found and has not been read by hand.")
                rows.append({"id": unit["id"], "url": url, "quote": source["quote"],
                             "quote_words": len(quote), "longest_run": run, "state": state, "note": note})
    (folder / "quotes.json").write_text(json.dumps(rows, ensure_ascii=False, indent=1) + "\n")
    for state in ("found", "read", "unopened"):
        print(state, sum(r["state"] == state for r in rows))
    print("quotes", len(rows), "addresses", len({r["url"] for r in rows}))


main()
