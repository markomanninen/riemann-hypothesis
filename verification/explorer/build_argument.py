#!/usr/bin/env python3
"""Collect the argument skeleton and its readings for the Argument tab of the explorer.

Usage: python3 -I verification/explorer/build_argument.py

The script reads the files of verification/skeleton and writes data/argument.json:

  nodes     the skeleton declarations, each with its parent, the number of declarations it
            gathers, its own pool, its module and the published statements it takes or proves
  lines     the 38 lines of the outline, each with the reading of its head from READING.md
  glossary  the ten definitions of GLOSSARY.md with their readings
  d7        the reading of the record D7 as a whole, with its groups of fields and its numbers
  reached   the number of declarations that the five theorems reach

The readings were written by a language model, as the documents of verification/skeleton
describe. This script copies them and writes none.
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
SKELETON = os.path.join(os.path.dirname(HERE), "skeleton")
PARTS = 24  # parts of a glossary entry that the page shows before it asks for more


def load(name):
    with open(os.path.join(SKELETON, name), encoding="utf-8") as f:
        return json.load(f)


def main():
    skeleton, published = load("skeleton.json"), load("published.json")
    reading, glossary, d7, summary = load("reading.json"), load("glossary.json"), load("d7.json"), load("summary.json")
    marks = published["skeleton"]
    nodes = []
    for node, mark in zip(skeleton["nodes"], marks):
        nodes.append({"n": node["name"], "m": node["module"], "p": node["parent"], "g": node["gathers"], "o": node["own"],
                      "w": node["passes"], "t": [x.rsplit(".", 1)[-1] for x in mark["takes"]],
                      "v": [x.rsplit(".", 1)[-1] for x in mark["proves"] + mark["derives"]]})
    index = {node["name"]: k for k, node in enumerate(skeleton["nodes"])}
    lines = []
    for r in reading["lines"]:
        check = r["check"]
        lines.append({"line": r["line"], "level": r["level"], "parent": r["parent"], "node": index[r["name"]],
                      "first": index[r["first"]], "wrappers": [x.rsplit(".", 1)[-1] for x in r["wrappers"]],
                      "says": r["says"], "premises": r["premises"], "conclusion": r["conclusion"], "notation": r["notation"],
                      "unopened": [t["name"] for t in r["terms"] if t.get("opaque")], "suggests": r["suggests"],
                      "confidence": r["confidence"], "why": r["why"], "errors": len(check["first_errors"]),
                      "rounds": check["rounds"]})
    entries = []
    for e in glossary["entries"]:
        entries.append({"name": e["name"], "module": e["module"], "kind": e["kind"], "what": e["what"], "below": e["below"],
                        "more": e["count_stopped"], "shown": e["shown"], "says": e["says"], "parts": e["parts"],
                        "unopened": e["unopened"], "suggests": e["suggests"], "confidence": e["confidence"], "why": e["why"],
                        "errors": len(e["check"]["first_errors"])})
    whole = d7["whole"]
    out = {"reached": summary["source"]["reached"], "declarations": summary["source"]["declarations"],
           "min": skeleton["min"], "top": skeleton["top"], "nodes": nodes, "lines": lines, "glossary": entries,
           "d7": {"says": whole["says"], "suggests": whole["suggests"], "fields": whole["fields"], "groups": whole["groups"],
                  "numbers": whole["numbers"], "definitions": len(d7["definitions"])},
           "docs": "https://github.com/markomanninen/riemann-hypothesis/blob/main/verification/skeleton/"}
    path = os.path.join(HERE, "data", "argument.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, separators=(",", ":"))
    print(f"{len(nodes)} skeleton declarations, {len(lines)} lines, {len(entries)} glossary entries, "
          f"{len(whole['groups'])} groups of D7, {os.path.getsize(path) / 1e6:.2f} MB")


if __name__ == "__main__":
    main()
