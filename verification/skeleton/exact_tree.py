#!/usr/bin/env python3
"""Compute the skeleton again on the exact graph and compare it with the skeleton of the text graph.

Usage: python3 -I verification/skeleton/exact_tree.py [--min N] [--outline N]

Run build.py of this folder and exact_graph.py of verification/decl-graph first. This script
reads data/exact_graph.npz, in which a compiled constant points to the constants that its
compiled type and value mention, and computes the dominator tree of that graph from the five
theorems of Main with the functions of build.py. Lean's helper constants, such as `_proof_1`,
are nodes of the tree but are not counted, so a node gathers the declarations of the text below
it, as in build.py.

It writes, next to itself:

  exact-tree.json     the figures, the skeleton of the exact graph, and for each line of
                      OUTLINE.txt what the exact graph says about it
  OUTLINE-EXACT.txt   the outline of the exact graph, in the form of OUTLINE.txt

The files of build.py are read and left as they are.
"""
import argparse
import gzip
import json
import os
import re
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
GRAPH = os.path.join(os.path.dirname(HERE), "decl-graph", "data")
sys.path.insert(0, HERE)
import build  # noqa: E402


def outline_lines(name="OUTLINE.txt"):
    """The lines of an outline file as (gathers, level, name, name of the line it hangs from)."""
    out, stack = [], []
    with open(os.path.join(HERE, name), encoding="utf-8") as f:
        for line in f:
            m = re.match(r"\s*([\d,]+)  (\s*)(\S+)", line)
            if not m:
                continue
            level = len(m.group(2)) // 2
            stack[level:] = [m.group(3)]
            out.append((int(m.group(1).replace(",", "")), level, m.group(3), stack[level - 1] if level else None))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--min", type=int, default=1000)
    ap.add_argument("--outline", type=int, default=10000)
    args = ap.parse_args()

    e = np.load(os.path.join(GRAPH, "exact_graph.npz"))
    ptr, edges, row, starts = e["ptr"], e["edges"], e["row"], e["starts"]
    n = len(row)
    names, modules, kinds, gid = [], [], [], []
    with gzip.open(os.path.join(GRAPH, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        head = f.readline().rstrip("\n").split("\t")
        col = {c: head.index(c) for c in ("id", "module", "kind", "name")}
        for line in f:
            p = line.rstrip("\n").split("\t")
            names.append(p[col["name"]]); modules.append(p[col["module"]])
            kinds.append(p[col["kind"]]); gid.append(int(p[col["id"]]))

    order, idom, passes, nedges = build.tree_of(ptr, edges, starts, n)
    count = len(order)
    rows = np.full(count, -1, np.int64)
    rows[1:] = row[order[1:]]
    real = (rows >= 0).astype(np.int64)
    below = build.gather(idom, real)
    sys.stderr.write(f"{count - 1:,} constants reached, {int(real.sum()):,} declarations, {passes} passes\n")

    # The tree of the text graph, by the row of each declaration.
    t = np.load(os.path.join(HERE, "data", "tree.npz"))
    text_below = dict(zip(t["order"].tolist(), t["below"].tolist()))
    text_of_row = lambda r: text_below.get(gid[r], 0)

    # The skeleton of the exact graph, with each node hung from its nearest skeleton ancestor.
    picked = [int(b) for b in np.flatnonzero(below >= args.min)[1:] if real[b]]
    slot = {b: k for k, b in enumerate(picked)}
    nodes, kids = [], {}
    for k, b in enumerate(picked):
        a = int(idom[b])
        while a and a not in slot:
            a = int(idom[a])
        parent = slot.get(a)
        r = int(rows[b])
        nodes.append({"name": names[r], "kind": kinds[r], "module": modules[r], "parent": parent,
                      "gathers": int(below[b]), "text_gathers": text_of_row(r)})
        if parent is not None:
            kids.setdefault(parent, []).append(k)
    for k in range(len(nodes)):
        kids[k] = sorted(kids.get(k, []), key=lambda c: -nodes[c]["gathers"])
    top = max((k for k, node in enumerate(nodes) if node["parent"] is None), key=lambda k: nodes[k]["gathers"])

    by_name = {node["name"]: k for k, node in enumerate(nodes)}
    exact_pos = {}
    for b in range(1, count):
        if rows[b] >= 0:
            exact_pos[names[int(rows[b])]] = b
    with open(os.path.join(HERE, "OUTLINE-EXACT.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(build.outline(nodes, kids, top, args.outline)) + "\n")
    # A line of OUTLINE.txt keeps its place when OUTLINE-EXACT.txt has the same name at the same
    # level, hanging from the same line. Both outlines fold runs of wrappers in the same way.
    exact_lines = {(level, name, parent) for _, level, name, parent in outline_lines("OUTLINE-EXACT.txt")}
    lines = []
    for text_gathers, level, name, parent in outline_lines():
        b = exact_pos.get(name)
        lines.append({"name": name, "level": level, "parent": parent, "text_gathers": text_gathers,
                      "exact_gathers": int(below[b]) if b is not None else 0,
                      "same_place": (level, name, parent) in exact_lines})
    text_names_outline = {name for _, _, name, _ in outline_lines()}
    added = [name for _, _, name, _ in outline_lines("OUTLINE-EXACT.txt") if name not in text_names_outline]

    text_sk = json.load(open(os.path.join(HERE, "skeleton.json"), encoding="utf-8"))["nodes"]
    text_names = {node["name"] for node in text_sk}
    exact_names = set(by_name)
    summary = {
        "reached_constants": count - 1,
        "reached_declarations": int(real.sum()),
        "edges": nedges,
        "passes": passes,
        "gathering_at_least": {str(m): int(((below >= m) & (real > 0)).sum()) for m in (100000, 10000, 1000, 100)},
        "skeleton": {"min": args.min, "nodes": len(nodes), "top": nodes[top]["name"], "top_gathers": nodes[top]["gathers"],
                     "also_in_text_skeleton": len(exact_names & text_names),
                     "only_in_exact_skeleton": len(exact_names - text_names),
                     "only_in_text_skeleton": len(text_names - exact_names)},
        "outline": {"lines": len(lines), "same_place": sum(x["same_place"] for x in lines),
                    "lines_added_in_exact": added},
        "outline_lines": lines,
        "nodes": nodes,
    }
    with open(os.path.join(HERE, "exact-tree.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in summary.items() if k not in ("outline_lines", "nodes")}, indent=1))


if __name__ == "__main__":
    main()
