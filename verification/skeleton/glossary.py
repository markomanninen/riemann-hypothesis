#!/usr/bin/env python3
"""Dossiers and the document for the glossary of the outline's most frequent unopened names.

Usage: python3 -I verification/skeleton/glossary.py            writes the dossiers
       python3 -I verification/skeleton/glossary.py --render   writes GLOSSARY.md from glossary.json

Run build.py of this folder first. NAMES lists the ten definitions that the readings of
READING.md leave unopened in most lines. For each one the script writes a dossier into
data/glossary, which git ignores. A dossier holds

  the whole text of the definition
  the number of project definitions that lie below it, level by level
  the definitions of the levels below it with their bodies, as far as BUDGET characters reach

Level one holds the definitions that the text of the definition names, level two those that
the definitions of level one name, and so on. The script also writes data/glossary/index.json
with the counts.

glossary.json holds what readers wrote about each definition from its dossier, as GLOSSARY.md
describes. With --render the script lays those readings out below the line `<!-- entries -->`
of GLOSSARY.md and keeps the text above that line.
"""
import json
import os
import re
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build  # noqa: E402

OUT = os.path.join(build.DATA, "glossary")
MARK = "<!-- entries -->"
DEFINITIONS = ("def", "abbrev", "structure", "class", "inductive")
NAMES = [
    "UpperTheory.Zero.LLC.RecTExists",
    "Formalism.BasicNotions.D7",
    "GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses",
    "GlobalTheory.Fc.RL.LinkedAt",
    "GlobalTheory.Mem.Top.Bl.parametersOfDependence",
    "GlobalTheory.Fc.R1.SlotNormCondition",
    "GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt",
    "GlobalTheory.Mem.Top.Bl.KPx",
    "GlobalTheory.Fc.BundleCondition",
    "Formalism.IndefR.Cx.CxData.MIstar2",
]
BUDGET = 60000          # characters of one dossier
ROOT_CHARS = 16000      # characters of the definition itself
BODY_CHARS = (3000, 2000, 1200)   # characters of a body at level one, two and deeper
DEPTH = 12              # levels that the count follows
STOP = 6000             # definitions after which the count stops


def words(name):
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
    names = [f"`{x}`" for x in names]
    return names[0] if len(names) == 1 else ", ".join(names[:-1]) + " and " + names[-1]


def dossiers():
    splitter = build.build_statements
    splitter.MAX_GIVEN = splitter.MAX_CLAIM = splitter.MAX_VALUE = 10 ** 9   # the glossary reads whole texts
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

    def show(v, t, limit):
        lines = [f"### `{names[v]}`", "", f"{kinds[v]} in module `{modules[v]}`", ""]
        if t is None:
            return lines + ["The statement splitter did not find this declaration.", ""]
        if t["context"]:
            lines += ["Variables in scope:", "", "```lean", t["context"], "```", ""]
        code = (kinds[v] + " " + short(names[v]) + (" " + t["given"] if t["given"] else "")
                + ((" :\n    " + t["claim"]) if t["claim"] else ""))
        if t["value"]:
            code += " :=\n" + t["value"]
        cut = len(code) > limit
        lines += ["```lean", code[:limit] + ("\n  … (cut)" if cut else ""), "```", ""]
        if cut:
            lines += [f"The text above is cut after {limit:,} of its {len(code):,} characters.", ""]
        return lines

    os.makedirs(OUT, exist_ok=True)
    for f in os.listdir(OUT):
        os.remove(os.path.join(OUT, f))
    index = []
    for number, name in enumerate(NAMES, 1):
        v = by_name[name]
        t = text_of(v)
        # The levels below the definition, counted to DEPTH levels or STOP definitions.
        seen, frontier, levels, order = {v}, [v], [], []
        for depth in range(1, DEPTH + 1):
            found = []
            for u in frontier:
                for x in named_in(u, whole(text_of(u))):
                    if x not in seen:
                        seen.add(x)
                        found.append(x)
            if not found:
                break
            levels.append(len(found))
            order.append(found)
            frontier = found
            if len(seen) > STOP:
                break
        open_end = len(seen) > STOP or len(levels) == DEPTH
        lines = [f"# Definition {number} of the glossary", "",
                 f"`{name}`, a {kinds[v]}.", "", "## The definition", ""] + show(v, t, ROOT_CHARS)
        lines += ["## What lies below it", "",
                  "The number of project definitions at each level below this definition is "
                  + ", ".join(f"{c:,}" for c in levels) + ("." if not open_end else ", and the count was stopped there."), ""]
        used, shown = sum(len(x) for x in lines), 0
        for depth, found in enumerate(order, 1):
            block = [f"## Definitions, level {depth}", ""]
            for x in found:
                part = show(x, text_of(x), BODY_CHARS[min(depth, len(BODY_CHARS)) - 1])
                if used + sum(len(p) for p in part) > BUDGET:
                    break
                block += part
                used += sum(len(p) for p in part)
                shown += 1
            else:
                lines += block
                continue
            lines += block + [f"The dossier stops here, at {shown:,} definitions, because it holds {BUDGET:,} characters at most.", ""]
            break
        file = f"{number:02d}-{re.sub(r'[^A-Za-z0-9]+', '_', short(name))}.md"
        with open(os.path.join(OUT, file), "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
        index.append({"number": number, "name": name, "kind": kinds[v], "module": modules[v], "file": file,
                      "own_chars": len(whole(t)), "levels": levels, "below": len(seen) - 1, "count_stopped": open_end,
                      "shown": shown, "chars": sum(len(x) for x in lines)})
        print(f"{number:>2} {short(name):<34} own {len(whole(t)):>6,} ch  below {len(seen) - 1:>5,}{'+' if open_end else ' '}  shown {shown:>3}  dossier {index[-1]['chars']:>6,} ch")
    with open(os.path.join(OUT, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1, ensure_ascii=False)


def render():
    with open(os.path.join(HERE, "glossary.json"), encoding="utf-8") as f:
        entries = json.load(f)["entries"]
    body = []
    for r in entries:
        below = f"{r['below']:,}" + (" or more" if r["count_stopped"] else "")
        body += [f"### `{short(r['name'])}`", "",
                 f"The full name is `{r['name']}`, a {r['kind']} in the module {' › '.join(words(p) for p in r['module'].split('.'))}. "
                 f"{below} project definitions lie below it, and the reader saw {r['shown']:,} of them. "
                 f"The reader describes it as {r['what'].strip().rstrip('.')}.", "",
                 sentence(r["says"]), ""]
        for part in r["parts"]:
            body.append(f"- `{part['name']}`. {sentence(part['gloss'])}")
        body.append("")
        if r.get("unopened"):
            body += ["The reading does not open " + ("the name " if len(r["unopened"]) == 1 else "the names ") + listed(r["unopened"]) + ".", ""]
        if r.get("suggests"):
            body += ["The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. "
                     + sentence(r["suggests"]), ""]
        body += [f"The reader's confidence is {r['confidence']}. {sentence(r['why'])}", ""]
        check = r["check"]
        count = {1: "one error", 2: "two errors", 3: "three errors", 4: "four errors"}
        rounds = {1: "one round", 2: "two rounds", 3: "three rounds"}
        if check["first_errors"]:
            k = len(check["first_errors"])
            body += [f"The check found {count.get(k, str(k) + ' errors')} in the first version of this reading. The text above is the "
                     f"corrected version, which passed the check after {rounds[check['rounds']]} of correction.", ""]
            body += [f"- {sentence(e)}" for e in check["first_errors"]] + [""]
        else:
            body += ["The check found no error in this reading.", ""]
        if check["second_errors"]:
            k = len(check["second_errors"])
            body += [f"The check found {count.get(k, str(k) + ' errors')} in the second reading, which the text above does not use.", ""]
    path = os.path.join(HERE, "GLOSSARY.md")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    head = text[:text.index(MARK) + len(MARK)] if MARK in text else text.rstrip() + "\n\n" + MARK
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "\n\n" + "\n".join(body).rstrip() + "\n")
    print(f"{len(entries)} entries written to GLOSSARY.md")


if __name__ == "__main__":
    render() if "--render" in sys.argv[1:] else dossiers()
