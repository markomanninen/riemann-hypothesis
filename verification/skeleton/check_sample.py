#!/usr/bin/env python3
"""Compare the dominator tree of the text graph with the tree of a compiled sample.

Usage: python3 -I verification/skeleton/check_sample.py GRAPH_DIR [ROOT_MODULE]

GRAPH_DIR holds graph.npz and declarations.tsv.gz, as verification/decl-graph/build.py writes
them, and sample-deps.tsv.gz, the uses that Lean recorded when it compiled the sample. All three
have to come from the same source. ROOT_MODULE is the module whose declarations stand in for the
five theorems, Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys by default.

The script builds two graphs over the declarations of the sample. In the compiled graph a
declaration points to the declarations that its type and its proof term really contain. In the
text graph it points to the declarations that its text names. It computes the dominator tree of
each from the declarations of ROOT_MODULE and writes the comparison to sample-check.json.
"""
import collections
import gzip
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build  # noqa: E402

ROOT = "Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys"


def rows_of(edges, n):
    """Edges as a dictionary of sets, turned into the row starts and targets that build.tree_of takes."""
    ptr = np.zeros(n + 1, np.int64)
    for d, es in edges.items():
        ptr[d + 1] = len(es)
    np.cumsum(ptr, out=ptr)
    adj = np.zeros(int(ptr[-1]), np.int64)
    for d, es in edges.items():
        adj[ptr[d]:ptr[d + 1]] = sorted(es)
    return ptr, adj


class Tree:
    """A dominator tree over declaration numbers, with a test for one node standing above another."""

    def __init__(self, edges, roots, n):
        order, idom, _, _ = build.tree_of(*rows_of(edges, n), roots, n)
        self.nodes = [int(v) for v in order[1:]]
        self.parent = {int(order[b]): int(order[idom[b]]) for b in range(1, len(order))}
        kids = collections.defaultdict(list)
        for v, p in self.parent.items():
            kids[p].append(v)
        self.enter, self.leave, clock, stack = {}, {}, 0, [(n, 0)]
        self.enter[n] = 0
        while stack:
            v, k = stack[-1]
            if k < len(kids[v]):
                stack[-1] = (v, k + 1)
                clock += 1
                self.enter[kids[v][k]] = clock
                stack.append((kids[v][k], 0))
            else:
                self.leave[v] = clock
                stack.pop()
        self.virtual = n

    def gathers(self, v):
        """The number of declarations at and below v."""
        return self.leave[v] - self.enter[v] + 1

    def above(self, d, v):
        """Whether d dominates v, or is v."""
        return self.enter[d] <= self.enter[v] <= self.leave[d]


def main():
    graph = sys.argv[1]
    root_module = sys.argv[2] if len(sys.argv) > 2 else ROOT
    g, n, kinds, names, modules = build.load(graph)
    real, private = g["real"], g["private"]
    strict, sp = g["strict"], g["strict_ptr"]
    pub, priv = {}, {}
    for i in np.flatnonzero(real).tolist():
        if private[i]:
            priv[(modules[i], names[i])] = i
        else:
            pub.setdefault(names[i], i)

    def to_decl(const, module):
        """The source declaration that a compiled constant came from, by the rule of decl-graph/check_sample.py."""
        if const.startswith("_private."):
            module, _, const = const[len("_private."):].partition(".0.")
        parts = const.split(".")
        for k in range(len(parts), 0, -1):
            name = ".".join(parts[:k])
            i = priv.get((module, name))
            if i is None:
                i = pub.get(name)
            if i is not None:
                return i
        return None

    rows, home = [], {}
    with gzip.open(os.path.join(graph, "sample-deps.tsv.gz"), "rt", encoding="utf-8") as f:
        for line in f:
            m, _, const, used = line.rstrip("\n").split("\t")
            rows.append((m, const, used.split() if used else []))
            home[const] = m
    sample_modules = {m for m, _, _ in rows}
    compiled = collections.defaultdict(set)
    for m, const, used in rows:
        d = to_decl(const, m)
        if d is None:
            continue
        for u in used:
            e = to_decl(u, home.get(u, m))
            if e is not None and e != d:
                compiled[d].add(e)
    sample = {i for i in np.flatnonzero(real).tolist() if modules[i] in sample_modules}

    text = {}
    for d in sample:
        out = set()
        for e in strict[sp[d]:sp[d + 1]].tolist():
            # A record that is no declaration, such as a `variable` line, passes its names on.
            out.update([e] if real[e] else [x for x in strict[sp[e]:sp[e + 1]].tolist() if real[x]])
        out.discard(d)
        text[d] = out & sample
    roots = sorted(i for i in sample if modules[i] == root_module)
    exact_tree = Tree({d: es & sample for d, es in compiled.items() if d in sample}, roots, n)
    text_tree = Tree(text, roots, n)

    in_exact, in_text = set(exact_tree.nodes), set(text_tree.nodes)
    both = in_exact & in_text
    same_parent = sum(1 for v in both if exact_tree.parent[v] == text_tree.parent[v])
    # A parent in the text tree is right when it really dominates the node, even if a nearer dominator exists.
    true_parent = sum(1 for v in both if text_tree.parent[v] in (text_tree.virtual,) or
                      (text_tree.parent[v] in in_exact and exact_tree.above(text_tree.parent[v], v)))
    out = {"root_module": root_module, "sample_modules": len(sample_modules), "source_declarations": len(sample),
           "roots": len(roots), "reached_compiled": len(in_exact), "reached_text": len(in_text), "reached_both": len(both),
           "same_immediate_dominator": same_parent, "text_dominator_really_dominates": true_parent, "chapters": {}}
    for share in (0.01, 0.05):
        floor = max(2, round(share * len(in_exact)))
        ex = {v for v in in_exact if exact_tree.gathers(v) >= floor}
        tx = {v for v in in_text if text_tree.gathers(v) >= floor}
        pairs = right = real_pairs = 0
        for d in tx:
            below = [v for v in in_text if v != d and text_tree.above(d, v)]
            pairs += len(below)
            right += sum(1 for v in below if d in in_exact and v in in_exact and exact_tree.above(d, v))
        for d in ex:
            real_pairs += exact_tree.gathers(d) - 1
        found = sum(1 for d in ex for v in in_exact
                    if v != d and exact_tree.above(d, v) and d in in_text and v in in_text and text_tree.above(d, v))
        ratios = sorted(text_tree.gathers(v) / exact_tree.gathers(v) for v in ex & tx)
        out["chapters"][f"{share:.0%}"] = {
            "gathers_at_least": floor, "compiled": len(ex), "text": len(tx), "in_both": len(ex & tx),
            "text_pairs": pairs, "text_pairs_true": right, "compiled_pairs": real_pairs, "compiled_pairs_found": found,
            "size_ratio_text_to_compiled": {"lowest": round(ratios[0], 3), "median": round(ratios[len(ratios) // 2], 3),
                                            "highest": round(ratios[-1], 3)} if ratios else {}}
    with open(os.path.join(HERE, "sample-check.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
