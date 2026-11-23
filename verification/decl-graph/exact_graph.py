#!/usr/bin/env python3
"""Follow the exact declaration graph from the five theorems of Main and compare it with the text graph.

Usage: python3 -I verification/decl-graph/exact_graph.py [CHUNK ...]

The script reads the chunks that exact_extract.py wrote to data/exact, or the files given, and
the declaration table of build.py. Every constant of the project is a node, and an edge leads
from a constant to each project constant that its compiled type or value mentions. Constants
that Lean creates itself, such as `_proof_1`, `match_1` or `eq_1`, are nodes as well, so a path
through them counts. The five theorems of Main are followed through these edges.

A compiled private name `_private.P.0.n`, where P is the dotted file path of module M, is
matched with the source name n of module M. The reached constants are then compared with each of the six text runs of build.py.

It writes exact-summary.json next to itself, and data/exact_graph.npz with the nodes, the edges
and the row of the declaration table that each node matches, -1 for a constant that has no row.
"""
import collections
import glob
import gzip
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
RUNS = ["names", "names+automation", "fields", "fields+automation", "loose", "loose+automation"]
TARGETS = ["LFunction_ne_zero_of_half_lt_re", "riemannHypothesis", "riemannZeta_eq_zero_re",
           "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]


def user_name(module, name):
    """The source name of a compiled name. A private constant is compiled as `_private.P.0.n`,
    where P is the module's file path in dotted form, such as `src.Main`, so P is checked to end
    with the module's name and is then dropped."""
    prefix = "_private."
    if name.startswith(prefix):
        path, sep, rest = name[len(prefix):].partition(".0.")
        if sep and (path == module or path.endswith("." + module)):
            return rest
    return name


def library(module):
    return module.split(".", 1)[0]


def main():
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(DATA, "exact", "chunk-*.tsv.gz")))
    if not files:
        sys.exit("no chunks found, run exact_extract.py first")

    # The nodes and their mentions, with the mentions kept as names until every node is known.
    index, names, modules, kinds, mentions = {}, [], [], [], []
    for path in files:
        opener = gzip.open if path.endswith(".gz") else open
        with opener(path, "rt", encoding="utf-8") as f:
            for line in f:
                module, name, kind, refs = line.rstrip("\n").split("\t")
                index[name] = len(names)
                names.append(name)
                modules.append(module)
                kinds.append(kind)
                mentions.append(refs)
    n = len(names)
    ptr = np.zeros(n + 1, dtype=np.int64)
    targets_of = []
    for i, refs in enumerate(mentions):
        out = [index[r] for r in refs.split(" ") if r in index] if refs else []
        targets_of.append(out)
        ptr[i + 1] = ptr[i] + len(out)
    edges = np.fromiter((j for out in targets_of for j in out), dtype=np.int32, count=int(ptr[-1]))
    del mentions, targets_of

    # Follow the five theorems.
    starts = [index[t] for t in TARGETS if t in index]
    if len(starts) != len(TARGETS):
        sys.exit(f"the compiled data lacks a target theorem: {[t for t in TARGETS if t not in index]}")
    seen = np.zeros(n, dtype=bool)
    stack = list(starts)
    seen[starts] = True
    while stack:
        i = stack.pop()
        for j in edges[ptr[i]:ptr[i + 1]]:
            if not seen[j]:
                seen[j] = True
                stack.append(int(j))

    # Match the nodes with the rows of the declaration table.
    rows = {}
    table = []
    with gzip.open(os.path.join(DATA, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        header = next(f).rstrip("\n").split("\t")
        col = {h: k for k, h in enumerate(header)}
        for line in f:
            r = line.rstrip("\n").split("\t")
            rows[(r[col["module"]], r[col["name"]])] = len(table)
            table.append(r)
    row_of = np.full(n, -1, dtype=np.int64)
    for i in range(n):
        row_of[i] = rows.get((modules[i], user_name(modules[i], names[i])), -1)
    matched = row_of >= 0
    exact_rows = np.zeros(len(table), dtype=bool)
    exact_rows[row_of[seen & matched]] = True
    compiled_rows = np.zeros(len(table), dtype=bool)
    compiled_rows[row_of[matched]] = True

    summary = {
        "chunks": len(files),
        "compiled_constants": n,
        "edges": int(ptr[-1]),
        "constants_with_a_row": int(matched.sum()),
        "rows": len(table),
        "rows_found_compiled": int(compiled_rows.sum()),
        "reached_constants": int(seen.sum()),
        "reached_rows": int(exact_rows.sum()),
        "reached_rows_share": round(float(exact_rows.sum()) / len(table), 4),
        "reached_constants_without_a_row_by_kind": dict(collections.Counter(
            kinds[i] for i in np.flatnonzero(seen & ~matched)).most_common()),
        "reached_rows_by_library": {},
        "text_runs": {},
    }
    by_lib = collections.defaultdict(lambda: [0, 0])
    for k, r in enumerate(table):
        lib = library(r[col["module"]])
        by_lib[lib][1] += 1
        by_lib[lib][0] += int(exact_rows[k])
    summary["reached_rows_by_library"] = dict(sorted(by_lib.items()))
    # Only rows that the compiled data holds can be judged, because a row without a compiled
    # constant has no exact answer.
    for run in RUNS:
        text = np.array([r[col[run]] == "1" for r in table])
        judged = compiled_rows
        summary["text_runs"][run] = {
            "text_reached": int((text & judged).sum()),
            "both": int((text & exact_rows).sum()),
            "text_only": int((text & judged & ~exact_rows).sum()),
            "exact_only": int((~text & exact_rows).sum()),
        }
    np.savez_compressed(os.path.join(DATA, "exact_graph.npz"), ptr=ptr, edges=edges, row=row_of, reached=seen,
                        starts=np.array(starts))
    with gzip.open(os.path.join(DATA, "exact_nodes.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("node\tmodule\tname\tkind\trow\treached\n")
        for i in range(n):
            f.write(f"{i}\t{modules[i]}\t{names[i]}\t{kinds[i]}\t{row_of[i]}\t{int(seen[i])}\n")
    with open(os.path.join(HERE, "exact-summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
