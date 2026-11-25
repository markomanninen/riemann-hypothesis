#!/usr/bin/env python3
"""Prepare and lay out the catalogue of the theorems in library terms that have large proofs.

Usage: python3 -I verification/reuse/catalogue.py dossiers
       python3 -I verification/reuse/catalogue.py collect FOLDER
       python3 -I verification/reuse/catalogue.py render

Run statements.py of this folder first. It writes data/small_vocabulary.tsv.gz, which marks
the theorems whose statement is written with library constants alone and gives the number of
declarations that each proof rests on.

dossiers  takes the theorems in library terms whose proof rests on more than 100 declarations,
          keeps one theorem for each group of statements that Lean found equal, the one with
          the largest proof, and writes one file for each into data/catalogue/batchNN, twenty
          to a folder. A dossier holds the whole Lean statement with the `variable` lines in
          scope. It also writes data/catalogue/index.json.

collect   reads the answers of the model runs from FOLDER, where the first reader's answer for
          a batch is A-batchNN.out, the second reader's B-batchNN.out and the check's
          C-batchNN.out, and writes them to catalogue.json.

render    reads catalogue.json and writes the part of CATALOGUE.md below the line
          `<!-- entries -->`. The text above that line is kept.

The readings were written by language models from the dossiers, as CATALOGUE.md describes, so
this script does not make them.
"""
import gzip
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "data", "catalogue")
MARK = "<!-- entries -->"
BATCH = 20
ABOVE = 100
sys.path.insert(0, HERE)
from audit import Source, answers, clip, sentence, short  # noqa: E402


def dossiers():
    rows = []
    with gzip.open(os.path.join(HERE, "data", "small_vocabulary.tsv.gz"), "rt", encoding="utf-8") as f:
        col = {c: k for k, c in enumerate(next(f).rstrip("\n").split("\t"))}
        for line in f:
            p = line.rstrip("\n").split("\t")
            if p[col["library_terms"]] == "1" and int(p[col["rests_on"]]) > ABOVE:
                rows.append({"module": p[col["module"]], "name": p[col["name"]], "kind": p[col["kind"]],
                             "used": p[col["used"]] == "1", "rests_on": int(p[col["rests_on"]]),
                             "areas": p[col["areas"]], "same_as": p[col["same_as"]]})
    rows.sort(key=lambda r: (-r["rests_on"], r["name"]))
    chosen, by_group = [], {}
    for r in rows:
        if r["same_as"] and r["same_as"] in by_group:
            by_group[r["same_as"]]["others"].append(r["name"])
            continue
        r["others"] = []
        if r["same_as"]:
            by_group[r["same_as"]] = r
        chosen.append(r)
    source = Source()
    os.makedirs(OUT, exist_ok=True)
    index, missing = [], 0
    for k, r in enumerate(chosen, 1):
        folder = f"batch{(k - 1) // BATCH + 1:02d}"
        os.makedirs(os.path.join(OUT, folder), exist_ok=True)
        text = source.text(r["module"], r["name"])
        missing += text is None
        lines = [f"# Theorem {k}, `{r['name']}`", "",
                 f"The theorem lies in the module `{r['module']}`. Its statement is written with constants of Mathlib and",
                 f"Lean alone. Its proof rests on {r['rests_on']:,} declarations of the project and is not shown here.", "",
                 "## The statement", "", "```lean", text or "(the splitter did not find this declaration)", "```", ""]
        slug = re.sub(r"[^\w]+", "_", short(r["name"]))[:60]
        file = f"{k:03d}-{slug}.md"
        body = "\n".join(lines)
        with open(os.path.join(OUT, folder, file), "w", encoding="utf-8") as f:
            f.write(body)
        index.append({"number": k, "name": r["name"], "module": r["module"], "kind": r["kind"], "used": r["used"],
                      "rests_on": r["rests_on"], "areas": r["areas"], "same_statement": r["others"],
                      "folder": folder, "file": file, "chars": len(body)})
    with open(os.path.join(OUT, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1, ensure_ascii=False)
    sizes = [r["chars"] for r in index]
    print(f"{len(rows)} theorems, {len(index)} statements in {index[-1]['folder'][-2:]} folders, {sum(sizes):,} characters, "
          f"largest {max(sizes):,}, {missing} declarations not found")


def collect(folder):
    with open(os.path.join(OUT, "index.json"), encoding="utf-8") as f:
        index = json.load(f)
    a, b, c = answers(folder, "A"), answers(folder, "B"), answers(folder, "C")
    entries = []
    for r in index:
        k = r["number"]
        if k not in a or k not in b or k not in c:
            sys.exit(f"theorem {k} lacks an answer")
        entries.append({x: r[x] for x in ("number", "name", "module", "kind", "used", "rests_on", "areas", "same_statement")}
                       | {"a": {x: y for x, y in a[k].items() if x not in ("number", "name")},
                          "b": {x: y for x, y in b[k].items() if x != "number"},
                          "check": {x: y for x, y in c[k].items() if x != "number"}})
    with open(os.path.join(HERE, "catalogue.json"), "w", encoding="utf-8") as f:
        json.dump({"theorems": entries}, f, indent=1, ensure_ascii=False)
    print(f"{len(entries)} theorems written to catalogue.json")


def capital(text):
    return text[:1].upper() + text[1:]


def render():
    with open(os.path.join(HERE, "catalogue.json"), encoding="utf-8") as f:
        entries = json.load(f)["theorems"]
    body = []
    for kind, title in (("named theorem", "Named theorems"), ("standard fact", "Standard facts"),
                        ("technical step", "Technical steps")):
        part = [e for e in entries if e["check"]["kind"] == kind]
        body += [f"## {title}", "", f"The check puts {len(part)} statements in this kind.", "",
                 "| No. | Theorem | Known as, by the check | Relation | The proof rests on |", "|---:|---|---|---|---:|"]
        for e in part:
            body.append(f"| {e['number']} | `{short(e['name'])}` | {capital(clip(e['check']['known_as'], 90))} | "
                        f"{e['check']['relation']} | {e['rests_on']:,} |")
        body.append("")
    body += ["## The statements", ""]
    for e in entries:
        a, b, c = e["a"], e["b"], e["check"]
        place = (f"The theorem is `{e['name']}` in the module `{e['module']}`. Its proof rests on {e['rests_on']:,} "
                 f"declarations, and the five theorems {'use' if e['used'] else 'do not use'} it.")
        if e["same_statement"]:
            n = len(e["same_statement"])
            place += (f" Lean found the same statement in {n} other theorem{'s' if n > 1 else ''}, "
                      + ", ".join(f"`{x}`" for x in e["same_statement"][:4]) + (" and others." if n > 4 else "."))
        body += [f"### {e['number']}, `{short(e['name'])}`", "", place, "", sentence(a["states"]), "", "```", a["notation"], "```", ""]
        body += [f"The first reader gives it the kind {a['kind']} and names the published result as follows. "
                 f"{capital(sentence(a['known_as']))} {sentence(a['reference']) if a.get('reference') else ''}".rstrip(), "",
                 f"The second reader gives it the kind {b['kind']} and the check the kind {c['kind']}. The check names the "
                 f"published result as follows. {capital(sentence(c['known_as']))} For the relation to that result the "
                 f"check has {c['relation']}, the first reader {a['relation']} and the second reader {b['relation']}.", ""]
        if c.get("note"):
            body += ["The check adds this. " + sentence(c["note"]), ""]
        if c.get("vacuity") and c["vacuity"].strip().lower().rstrip(".") != "none found":
            body += ["On emptiness the check wrote this. " + sentence(c["vacuity"]), ""]
        errors = c.get("a_errors") or []
        if errors:
            body += ["The check found these errors in the first reader's account of the Lean text, and the account above is "
                     "printed as the reader wrote it.", ""]
            body += [f"- {sentence(x)}" for x in errors] + [""]
    path = os.path.join(HERE, "CATALOGUE.md")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    head = text[:text.index(MARK) + len(MARK)] if MARK in text else text.rstrip() + "\n\n" + MARK
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "\n\n" + "\n".join(body).rstrip() + "\n")
    print(f"{len(entries)} theorems written to CATALOGUE.md")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "collect":
        collect(sys.argv[2])
    elif len(sys.argv) == 2 and sys.argv[1] in ("dossiers", "render"):
        {"dossiers": dossiers, "render": render}[sys.argv[1]]()
    else:
        sys.exit(__doc__)
