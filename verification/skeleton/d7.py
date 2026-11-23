#!/usr/bin/env python3
"""The record D7 with every definition below it, as one file for readers, and the document.

Usage: python3 -I verification/skeleton/d7.py            writes data/d7/all.md and data/d7/index.json
       python3 -I verification/skeleton/d7.py --render   writes D7.md from d7.json

Run build.py of this folder first. Formalism.BasicNotions.D7 is the record that the statements
of the outline's lines 6 to 22 are built over. The script follows the definitions that its text
names, then the definitions that those name, until no new definition appears. It writes the
whole text of D7 and of every definition found into data/d7/all.md, level by level, each with a
number. Git ignores that folder.

d7.json holds what readers wrote about each definition from that file, as D7.md describes.
With --render the script lays those readings out below the line `<!-- definitions -->` of
D7.md and keeps the text above that line. It writes the reading of D7 as a whole, its fields in
groups, the numbers that the definitions fix, and one line for each definition.
"""
import json
import os
import re
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build  # noqa: E402

ROOT = "Formalism.BasicNotions.D7"
OUT = os.path.join(build.DATA, "d7")
MARK = "<!-- definitions -->"
DEFINITIONS = ("def", "abbrev", "structure", "class", "inductive")
STARTERS = {"a", "an", "the", "for", "if", "every", "each", "there", "it", "this", "that", "all", "both", "some", "no",
            "any", "under", "assume", "then", "one", "two", "three", "four", "with", "when", "its", "at", "from", "as",
            "in", "on", "of", "to", "by", "given", "let", "either", "neither", "which", "where", "what"}


def short(name):
    return name.rsplit(".", 1)[-1]


def words(name):
    name = re.sub(r"([A-Z])([A-Z][a-z])", r"\1 \2", name)
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name)


def sentence(text):
    text = text.strip()
    if re.split(r"[\s,]", text, maxsplit=1)[0] in STARTERS:
        text = text[0].upper() + text[1:]
    return text if text.endswith((".", "!", "?")) else text + "."


def collect():
    splitter = build.build_statements
    splitter.MAX_GIVEN = splitter.MAX_CLAIM = splitter.MAX_VALUE = 10 ** 9
    g, n, kinds, names, modules = build.load()
    real, ptr, adj = g["real"], g["strict_ptr"], g["strict"]
    by_name = {}
    for v in np.flatnonzero(real).tolist():
        by_name.setdefault(names[v], v)
    cache = {}

    def text_of(v):
        m = modules[v]
        if m not in cache:
            found = splitter.statements(m)
            cache[m] = (found[0], {d[1]: d for d in found[1]}) if found else ([], {})
        contexts, table = cache[m]
        d = table.get(names[v])
        if d is None:
            return None
        d = list(d) + [""] * (9 - len(d))
        return {"context": contexts[d[2] - 1] if d[2] else "", "given": d[3] or "", "claim": d[4] or "", "value": d[5] or ""}

    def whole(t):
        return " ".join((t["context"], t["given"], t["claim"], t["value"])) if t else ""

    def named_in(v, text):
        out = set()
        for e in adj[ptr[v]:ptr[v + 1]].tolist():
            for x in ([e] if real[e] else [y for y in adj[ptr[e]:ptr[e + 1]].tolist() if real[y]]):
                if kinds[x] in DEFINITIONS and x != v and re.search(r"(?<![\w'])" + re.escape(short(names[x])) + r"(?![\w'])", text):
                    out.add(x)
        return sorted(out, key=lambda x: names[x])

    def show(v, t, number):
        head = f"### {number}. `{names[v]}`" if number else f"### `{names[v]}`"
        lines = [head, "", f"{kinds[v]} in module `{modules[v]}`", ""]
        if t is None:
            return lines + ["The statement splitter did not find this declaration.", ""]
        if t["context"]:
            lines += ["Variables in scope:", "", "```lean", t["context"], "```", ""]
        code = (kinds[v] + " " + short(names[v]) + (" " + t["given"] if t["given"] else "")
                + ((" :\n    " + t["claim"]) if t["claim"] else "") + ((" :=\n" + t["value"]) if t["value"] else ""))
        return lines + ["```lean", code, "```", ""]

    root = by_name[ROOT]
    seen, frontier, levels = {root}, [root], []
    while frontier:
        found = []
        for u in frontier:
            for x in named_in(u, whole(text_of(u))):
                if x not in seen:
                    seen.add(x)
                    found.append(x)
        if found:
            levels.append(found)
        frontier = found
    os.makedirs(OUT, exist_ok=True)
    lines = ["# The record D7 and every definition below it", "", "## The record", ""] + show(root, text_of(root), 0)
    index, number = [], 0
    for depth, found in enumerate(levels, 1):
        lines += [f"## Level {depth}", ""]
        for x in found:
            number += 1
            t = text_of(x)
            lines += show(x, t, number)
            index.append({"number": number, "level": depth, "name": names[x], "kind": kinds[x], "module": modules[x],
                          "chars": len(whole(t))})
    with open(os.path.join(OUT, "all.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    with open(os.path.join(OUT, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1, ensure_ascii=False)
    print(f"{number} definitions on {len(levels)} levels, {[len(x) for x in levels]}, "
          f"{sum(len(x) for x in lines):,} characters in all.md")


def render():
    with open(os.path.join(HERE, "d7.json"), encoding="utf-8") as f:
        data = json.load(f)
    whole = data["whole"]
    body = ["## What an object of D7 is", "", sentence(whole["says"]), "",
            "The next sentences are a suggestion from the names, which the Lean text does not show. " + sentence(whole["suggests"]), "",
            f"## The {whole['fields']} fields in {len(whole['groups'])} groups", ""]
    for group in whole["groups"]:
        body += [f"### {group['title']}", "",
                 ("The field is " if len(group["fields"]) == 1 else f"The {len(group['fields'])} fields are ")
                 + ", ".join(f"`{x}`" for x in group["fields"]) + ".", "", sentence(group["gloss"]), ""]
    body += ["## The numbers that the definitions fix", ""] + [f"- {sentence(x)}" for x in whole["numbers"]] + [""]
    body += ["## The definitions below D7", ""]
    level = 0
    for r in data["definitions"]:
        if r["level"] != level:
            level = r["level"]
            body += [f"### Level {level}", ""]
        line = (f"- **{r['number']}.** `{r['name']}`, {'an' if r['kind'][0] in 'aeiou' else 'a'} {r['kind']} in {' › '.join(words(p) for p in r['module'].split('.')[:3])}. "
                + sentence(r["gloss"]))
        if r.get("unopened"):
            line += " The reading does not open " + ", ".join(f"`{x}`" for x in r["unopened"]) + "."
        if r.get("corrected"):
            line += " The check faulted the first version of this reading, and this is the corrected one."
        body.append(line)
        if r["number"] == data["definitions"][-1]["number"] or data["definitions"][r["number"]]["level"] != level:
            body.append("")
    path = os.path.join(HERE, "D7.md")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    head = text[:text.index(MARK) + len(MARK)] if MARK in text else text.rstrip() + "\n\n" + MARK
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "\n\n" + "\n".join(body).rstrip() + "\n")
    print(f"{len(data['definitions'])} definitions written to D7.md")


if __name__ == "__main__":
    render() if "--render" in sys.argv[1:] else collect()
