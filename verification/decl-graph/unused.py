#!/usr/bin/env python3
"""Sort the declarations that the five theorems of Main do not use.

Usage: python3 -I verification/decl-graph/unused.py

Run exact_graph.py and exact_axioms.py of this folder first. A declaration is unused when it is
a row of data/declarations.tsv.gz that the exact graph does not reach from the five theorems.
The script sorts the unused declarations in these ways:

  compiled or not   a row that has no compiled constant is counted apart
  repeats           a row that Lean found to state exactly what another declaration states, by
                    the table same_checked.tsv.gz of verification/redundancy, and whether that
                    other declaration is used
  imports           whether the module of a row lies below Main.lean in the import graph of
                    verification/import-graph
  tops              an unused declaration that no constant of the project mentions; every other
                    unused declaration is mentioned by some unused constant
  reach of a top    the unused declarations that a top reaches through unused constants, and
                    those that it alone reaches
  axioms            the axioms that every unused constant of the project reaches, read from the
                    same compiled data as exact_axioms.py

It writes unused.json next to itself and prints the figures.
"""
import collections
import glob
import gzip
import json
import os

import sys

import numba
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
VERIFICATION = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from exact_graph import user_name  # noqa: E402


@numba.njit(cache=True)
def reach_of_tops(ptr, edges, unused, decl, tops):
    """For each top, the declarations it reaches through unused constants, and for each constant
    the one top that reaches it, -2 when several do and -1 when none does."""
    n = len(ptr) - 1
    owner = np.full(n, -1, np.int64)
    mark = np.full(n, -1, np.int64)
    stack = np.empty(n, np.int64)
    reach = np.zeros(len(tops), np.int64)
    for k in range(len(tops)):
        sp = 0
        stack[sp] = tops[k]
        sp += 1
        mark[tops[k]] = k
        while sp > 0:
            sp -= 1
            v = stack[sp]
            if decl[v]:
                reach[k] += 1
            if owner[v] == -1:
                owner[v] = k
            elif owner[v] != k:
                owner[v] = -2
            for j in range(ptr[v], ptr[v + 1]):
                w = edges[j]
                if unused[w] and mark[w] != k:
                    mark[w] = k
                    stack[sp] = w
                    sp += 1
    return reach, owner


@numba.njit(cache=True)
def components(ptr, edges, unused):
    """The groups of unused constants that mentions join, ignoring their direction."""
    n = len(ptr) - 1
    parent = np.arange(n)
    for v in range(n):
        if not unused[v]:
            continue
        for j in range(ptr[v], ptr[v + 1]):
            w = edges[j]
            if unused[w]:
                a = v
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                b = w
                while parent[b] != b:
                    parent[b] = parent[parent[b]]
                    b = parent[b]
                if a != b:
                    parent[a] = b
    for v in range(n):
        a = v
        while parent[a] != a:
            a = parent[a]
        parent[v] = a
    return parent


def main():
    g = np.load(os.path.join(DATA, "exact_graph.npz"))
    ptr, edges, row, reached = g["ptr"], g["edges"].astype(np.int64), g["row"], g["reached"]
    n = len(row)
    names, modules = [None] * n, [None] * n
    with gzip.open(os.path.join(DATA, "exact_nodes.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for line in f:
            i, m, name, _, _, _ = line.rstrip("\n").split("\t")
            names[int(i)], modules[int(i)] = name, m
    table = []
    with gzip.open(os.path.join(DATA, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        head = next(f).rstrip("\n").split("\t")
        col = {c: k for k, c in enumerate(head)}
        for line in f:
            p = line.rstrip("\n").split("\t")
            table.append((p[col["module"]], p[col["name"]], p[col["kind"]]))
    rows = len(table)
    used = np.zeros(rows, bool)
    used[row[reached & (row >= 0)]] = True
    compiled = np.zeros(rows, bool)
    compiled[row[row >= 0]] = True
    unused_rows = np.flatnonzero(~used)

    # Repeats, by the groups of statements that Lean compared in verification/redundancy.
    at = {(m, name): k for k, (m, name, _) in enumerate(table)}
    link = list(range(rows))

    def root(a):
        while link[a] != a:
            link[a] = link[link[a]]
            a = link[a]
        return a

    groups = collections.defaultdict(list)
    with gzip.open(os.path.join(VERIFICATION, "redundancy", "data", "same_checked.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for line in f:
            group, m, name, found, _, statement = line.rstrip("\n").split("\t")
            k = at.get((m, name))
            if found == "1" and k is not None:
                groups[(group, statement)].append(k)
    for members in groups.values():
        for k in members[1:]:
            a, b = root(members[0]), root(k)
            if a != b:
                link[a] = b
    in_group = np.zeros(rows, bool)
    for members in groups.values():
        in_group[members] = True
    size, has_used = collections.Counter(), set()
    for k in np.flatnonzero(in_group).tolist():
        r = root(k)
        size[r] += 1
        if used[k]:
            has_used.add(r)

    # The import graph.
    below_main = {}
    with gzip.open(os.path.join(VERIFICATION, "import-graph", "modules.tsv.gz"), "rt", encoding="utf-8") as f:
        mhead = next(f).rstrip("\n").split("\t")
        mcol = {c: k for k, c in enumerate(mhead)}
        for line in f:
            p = line.rstrip("\n").split("\t")
            below_main[p[mcol["module"]]] = p[mcol["below_main"]] == "1"

    def sort_of(k):
        m, name, _ = table[k]
        if not compiled[k]:
            return "not compiled"
        if in_group[k] and root(k) in has_used:
            return "states what a used declaration states"
        if in_group[k] and size[root(k)] > 1:
            return "states what only unused declarations state"
        return "states its own statement"

    sorts = collections.Counter()
    sorts_by_kind = collections.defaultdict(collections.Counter)
    for k in unused_rows.tolist():
        s = sort_of(k)
        sorts[s] += 1
        sorts_by_kind[s][table[k][2]] += 1

    by_module = collections.defaultdict(lambda: [0, 0])
    for k, (m, _, _) in enumerate(table):
        by_module[m][0 if used[k] else 1] += 1
    whole = [m for m, (u, x) in by_module.items() if u == 0]
    outside = [k for k in unused_rows.tolist() if not below_main.get(table[k][0], True)]

    # Tops, their reach, and the connected groups of unused constants.
    unused = ~reached
    decl = row >= 0
    indegree = np.bincount(edges, minlength=n)
    tops = np.flatnonzero(unused & decl & (indegree == 0))
    reach, owner = reach_of_tops(ptr, edges, unused, decl, tops)
    alone = collections.Counter(owner[unused & decl & (owner >= 0)].tolist())
    label = components(ptr, edges, unused)
    comp = collections.Counter(label[unused & decl].tolist())
    comp_sizes = sorted(comp.values(), reverse=True)
    largest = comp.most_common(1)[0][0]
    largest_parts = collections.Counter(".".join(modules[i].split(".")[:3])
                                        for i in np.flatnonzero(unused & decl & (label == largest)).tolist())

    def top_entry(k):
        t = int(tops[k])
        return {"name": user_name(modules[t], names[t]), "module": modules[t], "kind": table[int(row[t])][2],
                "reaches": int(reach[k]), "reaches_alone": alone.get(k, 0)}

    order = sorted(range(len(tops)), key=lambda k: -reach[k])

    # Axioms of the unused part, through the project and the libraries.
    refs, kind = {}, {}
    files = sorted(glob.glob(os.path.join(DATA, "exact", "chunk-*.tsv.gz"))) + \
        sorted(glob.glob(os.path.join(DATA, "exact", "lib-*.tsv.gz")))
    for path in files:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            for line in f:
                _, c, k, r = line.rstrip("\n").split("\t")
                if c not in refs:
                    refs[c], kind[c] = r, k
    ctors = {}
    for c, k in kind.items():
        if k == "ctor":
            of_type = c.rsplit(".", 1)[0]
            if kind.get(of_type) == "ind":
                ctors.setdefault(of_type, []).append(c)
    start = [names[i] for i in np.flatnonzero(unused).tolist()]
    seen = set(start)
    queue = collections.deque(start)
    missing = 0
    while queue:
        c = queue.popleft()
        r = refs.get(c)
        if r is None:
            missing += 1
            continue
        for x in (r.split(" ") if r else []) + ctors.get(c, []):
            if x not in seen:
                seen.add(x)
                queue.append(x)
    axioms = sorted(c for c in seen if kind.get(c) == "axiom")

    summary = {
        "rows": rows,
        "used_rows": int(used.sum()),
        "unused_rows": len(unused_rows),
        "unused_by_kind": dict(collections.Counter(table[k][2] for k in unused_rows.tolist()).most_common()),
        "unused_by_library": dict(collections.Counter(table[k][0].split(".")[0] for k in unused_rows.tolist()).most_common()),
        "sorts": dict(sorts.most_common()),
        "sorts_by_kind": {s: dict(c.most_common()) for s, c in sorts_by_kind.items()},
        "modules": len(by_module),
        "modules_without_a_used_row": len(whole),
        "unused_rows_in_those_modules": sum(by_module[m][1] for m in whole),
        "unused_rows_outside_the_imports_of_main": len(outside),
        "modules_outside_the_imports_of_main_with_rows": len({table[k][0] for k in outside}),
        "unused_constants": int(unused.sum()),
        "tops": len(tops),
        "tops_by_kind": dict(collections.Counter(table[int(row[t])][2] for t in tops.tolist()).most_common()),
        "tops_reaching_no_other_declaration": int((reach == 1).sum()),
        "unused_rows_reached_by_one_top": int((unused & decl & (owner >= 0)).sum()),
        "unused_rows_reached_by_several_tops": int((unused & decl & (owner == -2)).sum()),
        "unused_rows_reached_by_no_top": int((unused & decl & (owner == -1)).sum()),
        "groups": len(comp),
        "groups_of_one": sum(1 for s in comp_sizes if s == 1),
        "largest_groups": comp_sizes[:10],
        "largest_group_by_part": dict(largest_parts.most_common(10)),
        "tops_in_largest_group": int(sum(1 for t in tops.tolist() if label[t] == largest)),
        "largest_tops": [top_entry(k) for k in order[:40]],
        "axioms_reached_from_the_unused_constants": axioms,
        "reached_names_without_a_compiled_entry": missing,
    }
    with open(os.path.join(HERE, "unused.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in summary.items() if k != "largest_tops"}, indent=1, ensure_ascii=False))
    for t in summary["largest_tops"][:15]:
        print(t["reaches"], t["reaches_alone"], t["name"])


if __name__ == "__main__":
    main()
