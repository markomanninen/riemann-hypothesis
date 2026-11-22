#!/usr/bin/env python3
"""Test the dominator routine of build.py against networkx on random graphs.

Usage: python3 -I verification/skeleton/test_tree.py

Needs networkx. Each graph has a few hundred nodes and random edges, cycles included, and two
roots. The script fails with an assertion when an immediate dominator differs.
"""
import os
import random
import sys

import networkx as nx
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import build  # noqa: E402


def one(seed):
    rnd = random.Random(seed)
    n = rnd.randint(2, 400)
    edges = {(rnd.randrange(n), rnd.randrange(n)) for _ in range(rnd.randint(0, 4 * n))}
    if seed % 2:
        edges = {(a, b) for a, b in edges if a < b}  # every second graph has no cycle
    roots = sorted({rnd.randrange(n), rnd.randrange(n)})
    ptr = np.zeros(n + 1, np.int64)
    for a, _ in edges:
        ptr[a + 1] += 1
    np.cumsum(ptr, out=ptr)
    adj = np.array([b for _, b in sorted(edges)], np.int64)
    order, idom, _, _ = build.tree_of(ptr, adj, roots, n)
    mine = {int(order[b]): int(order[idom[b]]) for b in range(1, len(order))}
    g = nx.DiGraph(list(edges) + [(n, r) for r in roots])
    theirs = {v: d for v, d in nx.immediate_dominators(g, n).items() if v != n}
    assert mine == theirs, f"graph {seed} differs"
    return len(mine)


if __name__ == "__main__":
    reached = sum(one(seed) for seed in range(400))
    print(f"400 random graphs agree with networkx, {reached:,} nodes reached in all")
