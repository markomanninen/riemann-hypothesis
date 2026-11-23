#!/usr/bin/env python3
"""Write the readings of the outline lines as a document.

Usage: python3 -I verification/skeleton/reading.py

reading.json holds, for each of the 38 lines of the outline, what a reader wrote about the Lean
statement of its head and what a check of that reading found. The readings were written by
language models from the dossiers of dossier.py, as READING.md describes, so this script does
not make them. It lays them out as the second part of READING.md, below the line that starts
with `<!-- lines -->`, and keeps the text above that line as it is.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
MARK = "<!-- lines -->"


def words(name):
    """A module part as words: ThetaPairLifts reads Theta Pair Lifts."""
    name = re.sub(r"([A-Z])([A-Z][a-z])", r"\1 \2", name)
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name)


def short(name):
    return name.rsplit(".", 1)[-1]


STARTERS = {"a", "an", "the", "for", "if", "every", "each", "there", "it", "this", "that", "all", "both", "some", "no",
            "any", "under", "assume", "then", "one", "two", "three", "four", "with", "when", "its", "at", "from", "as",
            "in", "on", "of", "to", "by", "given", "let", "either", "neither", "which", "where", "what"}


def sentence(text):
    """The text as a sentence. An English first word gets a capital, and a name of the source keeps its case."""
    text = text.strip()
    if re.split(r"[\s,]", text, maxsplit=1)[0] in STARTERS:
        text = text[0].upper() + text[1:]
    return text if text.endswith((".", "!", "?")) else text + "."


def listed(names):
    """Names in code font, joined as a list in a sentence."""
    names = [f"`{x}`" for x in names]
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]


def clip(text, limit=150):
    text = text.strip().rstrip(".")
    return text if len(text) <= limit else text[:limit].rsplit(" ", 1)[0] + " …"


def entry(r, by_line):
    out = [f"### Line {r['line']}, `{short(r['name'])}`", ""]
    place = f"The head is `{r['name']}`, in the module {' › '.join(words(p) for p in r['module'].split('.'))}. "
    place += f"The line gathers {r['gathers']:,} declarations"
    place += f" and hangs from line {r['parent']}, `{short(by_line[r['parent']]['name'])}`." if r["parent"] else " and is the top of the outline."
    if r["wrappers"]:
        place += " Folded into the line " + ("is the wrapper " if len(r["wrappers"]) == 1 else "are the wrappers ")
        place += listed([short(w) for w in r["wrappers"]]) + "."
    out += [place, "", sentence(r["says"]), ""]
    for i, p in enumerate(r["premises"], 1):
        out.append(f"- Premise {i}. {sentence(p)}")
    out += [f"- Conclusion. {sentence(r['conclusion'])}", "", "```", r["notation"], "```", ""]
    opaque = [t["name"] for t in r["terms"] if t.get("opaque")]
    if opaque:
        out += ["The reading does not open " + ("the name " if len(opaque) == 1 else "the names ") + listed(opaque) + ".", ""]
    if r.get("suggests"):
        out += ["The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. "
                + sentence(r["suggests"]), ""]
    out += [f"The reader's confidence is {r['confidence']}. {sentence(r['why'])}", ""]
    check = r["check"]
    count = {1: "one error", 2: "two errors", 3: "three errors", 4: "four errors"}
    rounds = {1: "one round", 2: "two rounds", 3: "three rounds"}
    if check["first_errors"]:
        n = len(check["first_errors"])
        out += [f"The check found {count.get(n, str(n) + ' errors')} in the first version of this reading. The text above is the "
                f"corrected version, which passed the check after {rounds[check['rounds']]} of correction.", ""]
        out += [f"- {sentence(e)}" for e in check["first_errors"]] + [""]
    else:
        out += ["The check found no error in this reading.", ""]
    if check["second_errors"]:
        n = len(check["second_errors"])
        out += [f"The check found {count.get(n, str(n) + ' errors')} in the second reading, which the text above does not use.", ""]
    cross = r.get("cross_check")
    if cross:
        k = cross["changes"]
        out += [f"A second model, Gemini, checked this reading again. {'One passage' if k == 1 else str(k) + ' passages'} of the text "
                f"above {'was' if k == 1 else 'were'} changed after its findings were compared with the Lean text.", ""]
    deep = r.get("deeper")
    if deep:
        out += ["#### A deeper reading, with the record D7 at hand", "",
                f"A second reader saw the dossier, the whole text of `D7` and the glossary. The check found "
                f"{deep['errors_round_1']} errors in this reading and, after they were corrected, {deep['errors_round_2']} more, "
                "which were corrected too. The reading has not passed the check.", "", sentence(deep["says"]), ""]
        out += [f"- Premise {i}. {sentence(p)}" for i, p in enumerate(deep["premises"], 1)]
        out += [f"- Conclusion. {sentence(deep['conclusion'])}", ""]
        if deep["opened"]:
            out += ["This reading opens " + listed(deep["opened"]) + ".", ""]
        if deep["unopened"]:
            out += ["It does not open " + listed(deep["unopened"]) + ".", ""]
        out += [f"The reader's confidence is {deep['confidence']}. {sentence(deep['why'])}", ""]
    return out


def main():
    with open(os.path.join(HERE, "reading.json"), encoding="utf-8") as f:
        data = json.load(f)
    lines = data["lines"]
    by_line = {r["line"]: r for r in lines}
    body = ["## The outline at a glance", "",
            "| Line | Head | Gathers | Conclusion of the statement | Confidence |", "|---:|---|---:|---|---|"]
    for r in lines:
        body.append(f"| {r['line']} | {'· ' * r['level']}`{short(r['name'])}` | {r['gathers']:,} | {clip(r['conclusion'])} | {r['confidence']} |")
    body += ["", "## The lines", ""]
    for r in lines:
        body += entry(r, by_line)
    path = os.path.join(HERE, "READING.md")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    head = text[:text.index(MARK) + len(MARK)] if MARK in text else text.rstrip() + "\n\n" + MARK
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "\n\n" + "\n".join(body).rstrip() + "\n")
    print(f"{len(lines)} lines written to READING.md")


if __name__ == "__main__":
    main()
