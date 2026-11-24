#!/usr/bin/env python3
"""Count the declarations of the project that a compiled constant rests on.

Usage: python3 -I verification/strategy/cone.py NAME [NAME ...]
       python3 -I verification/strategy/cone.py --users NAME [NAME ...]

Run exact_graph.py of verification/decl-graph first. This script reads its files
data/exact_graph.npz and data/exact_nodes.tsv.gz. In that graph every compiled constant of the
project is a node, and an edge leads from a constant to each project constant that its compiled
type or value mentions.

A NAME is the full name of a constant, or the end of one from a dot onwards, such as `ch_core`
for `Deduction.ch_core`. When several constants end in NAME, the script prints up to five.

Without an option the script follows the edges from each named constant and prints the number
of source declarations among the constants it reaches, the named constant included. A source
declaration is a constant with a row in the declaration table of build.py, so Lean's helper
constants, such as `_proof_1`, are followed but not counted. Mathlib and Lean's library are
outside the graph. README.md of this folder calls this number what the constant rests on.

With --users the script prints the constants that mention the named constant directly. For a
structure constructor, such as `Formalism.HC.EAtH.mk`, these are the places that build a value
of the structure.
"""
import gzip
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(os.path.dirname(HERE), "decl-graph", "data")


class Graph:
    """The exact graph with the names of its nodes."""

    def __init__(self):
        z = np.load(os.path.join(DATA, "exact_graph.npz"))
        self.ptr, self.edges, self.row = z["ptr"], z["edges"], z["row"]
        n = len(self.row)
        self.names, self.modules, self.kinds = [""] * n, [""] * n, [""] * n
        self.by_name, self.by_last = {}, {}
        with gzip.open(os.path.join(DATA, "exact_nodes.tsv.gz"), "rt", encoding="utf-8") as f:
            next(f)
            for line in f:
                p = line.rstrip("\n").split("\t")
                i = int(p[0])
                self.names[i], self.modules[i], self.kinds[i] = p[2], p[1], p[3]
                self.by_name.setdefault(p[2], []).append(i)
                self.by_last.setdefault(p[2].rsplit(".", 1)[-1], []).append(i)

    def find(self, name):
        """The nodes named `name`, or else the nodes whose name ends in `.name`."""
        if name in self.by_name:
            return self.by_name[name]
        tail = "." + name
        return [i for i in self.by_last.get(name.rsplit(".", 1)[-1], []) if self.names[i].endswith(tail)]

    def reached(self, start):
        """A mask of the nodes that the edges reach from node `start`, with `start` itself."""
        seen = np.zeros(len(self.row), dtype=bool)
        seen[start] = True
        front = np.array([start], dtype=np.int64)
        while front.size:
            lo, hi = self.ptr[front], self.ptr[front + 1]
            size = hi - lo
            total = int(size.sum())
            if not total:
                break
            first = np.cumsum(size) - size
            pos = np.repeat(lo - first, size) + np.arange(total)
            front = np.unique(self.edges[pos])
            front = front[~seen[front]].astype(np.int64)
            seen[front] = True
        return seen

    def rests_on(self, start):
        """The number of source declarations among the nodes reached from `start`."""
        return int((self.reached(start) & (self.row >= 0)).sum())

    def users(self, target):
        """The nodes that mention node `target` directly."""
        pos = np.nonzero(self.edges == target)[0]
        return np.unique(np.searchsorted(self.ptr, pos, side="right") - 1)


def main():
    args = sys.argv[1:]
    users = bool(args) and args[0] == "--users"
    if users:
        args = args[1:]
    if not args:
        sys.exit(__doc__)
    g = Graph()
    for name in args:
        hits = g.find(name)
        if not hits:
            print("not found  " + name)
            continue
        for i in hits[:5]:
            if users:
                us = g.users(i)
                print("%s is mentioned by %d constants" % (g.names[i], len(us)))
                for u in us:
                    print("    %s  [%s, %s]" % (g.names[u], g.kinds[u], g.modules[u]))
            else:
                print("%9s  %s  [%s, %s]" % (format(g.rests_on(i), ","), g.names[i], g.kinds[i], g.modules[i]))
        if len(hits) > 5:
            print("    %d constants end in %s, and the first five are shown" % (len(hits), name))


if __name__ == "__main__":
    main()
