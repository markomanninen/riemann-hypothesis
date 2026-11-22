#!/usr/bin/env python3
"""Find the theorems that carry the argument of the proof.

Usage: python3 -I verification/skeleton/build.py [--min N] [--outline N]

Run verification/decl-graph/build.py first. This script reads its declaration graph, in which a
declaration points to the declarations that its text names, and computes the dominator tree of
that graph from the five theorems of Main.

A declaration D dominates a declaration E when every chain of mentions from the five theorems
to E passes through D. The nearest such D is the immediate dominator of E, and these pairs form
a tree. The declarations below D in that tree are the ones the proof uses only by way of D, so
their number says how much of the proof D gathers below it. The skeleton is the part of the
tree whose nodes gather at least --min declarations, 1,000 by default.

The script writes, next to itself:

  summary.json    the figures of the run
  skeleton.json   the nodes of the skeleton, each with its parent, its counts and its statement
  OUTLINE.txt     the nodes that gather at least --outline declarations, as indented lines
  data/tree.npz   the whole dominator tree as arrays, which git ignores

The graph comes from the source text, so the tree is an estimate. README.md says how far it
can be trusted.
"""
import argparse
import gzip
import json
import os
import sys
import time

import numpy as np

try:
    from numba import njit
except ImportError:  # The script runs without numba and then takes about four times as long.
    def njit(*args, **kwargs):
        return (lambda f: f) if not (args and callable(args[0])) else args[0]

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFICATION = os.path.dirname(HERE)
GRAPH = os.path.join(VERIFICATION, "decl-graph", "data")
DATA = os.path.join(HERE, "data")
THEOREMS = ("theorem", "lemma")
WRAPPER = 0.99

sys.path.insert(0, os.path.join(VERIFICATION, "explorer"))
import build_statements  # noqa: E402  The statement splitter of the explorer.


@njit(cache=True)
def reverse_postorder(ptr, adj, roots, n):
    """The nodes reached from the virtual root n, in reverse postorder of a depth-first walk."""
    offset = np.zeros(n + 1, np.int64)
    seen = np.zeros(n + 1, np.bool_)
    post = np.empty(n + 1, np.int64)
    stack = np.empty(n + 1, np.int64)
    k, top = 0, 0
    stack[0] = n
    seen[n] = True
    while top >= 0:
        v = stack[top]
        lo = 0 if v == n else ptr[v]
        hi = len(roots) if v == n else ptr[v + 1]
        i = offset[v]
        pushed = False
        while lo + i < hi:
            w = roots[i] if v == n else adj[lo + i]
            i += 1
            if not seen[w]:
                seen[w] = True
                offset[v] = i
                top += 1
                stack[top] = w
                pushed = True
                break
        if not pushed:
            post[k] = v
            k += 1
            top -= 1
    return post[:k][::-1].copy()


@njit(cache=True)
def dominators(pptr, pred, count):
    """Immediate dominators by the iteration of Cooper, Harvey and Kennedy. Nodes are numbered in
    reverse postorder, so the root is 0 and a dominator has a smaller number than its node."""
    idom = np.full(count, -1, np.int64)
    idom[0] = 0
    passes, changed = 0, True
    while changed:
        changed = False
        passes += 1
        for b in range(1, count):
            new = -1
            for j in range(pptr[b], pptr[b + 1]):
                p = pred[j]
                if idom[p] == -1:
                    continue
                if new == -1:
                    new = p
                    continue
                a, c = p, new
                while a != c:
                    while a > c:
                        a = idom[a]
                    while c > a:
                        c = idom[c]
                new = a
            if new != idom[b]:
                idom[b] = new
                changed = True
    return idom, passes


@njit(cache=True)
def gather(idom, weight):
    """For every node the sum of the weights in its subtree of the dominator tree, itself included."""
    total = weight.copy()
    for b in range(len(idom) - 1, 0, -1):
        total[idom[b]] += total[b]
    return total


@njit(cache=True)
def depths(idom):
    depth = np.zeros(len(idom), np.int64)
    for b in range(1, len(idom)):
        depth[b] = depth[idom[b]] + 1
    return depth


@njit(cache=True)
def preorder(idom):
    """The place of every node in a walk of the dominator tree that visits a node before the nodes
    below it, so the nodes at and below a node hold consecutive places."""
    count = len(idom)
    start = np.zeros(count + 1, np.int64)
    for b in range(1, count):
        start[idom[b] + 1] += 1
    for b in range(count):
        start[b + 1] += start[b]
    fill, kids = start[:-1].copy(), np.empty(count - 1, np.int64)
    for b in range(1, count):
        kids[fill[idom[b]]] = b
        fill[idom[b]] += 1
    place, stack = np.zeros(count, np.int64), np.empty(count, np.int64)
    top, clock = 0, 0
    stack[0] = 0
    while top >= 0:
        v = stack[top]
        top -= 1
        place[v] = clock
        clock += 1
        for j in range(start[v], start[v + 1]):
            top += 1
            stack[top] = kids[j]
    return place


def load(graph=GRAPH):
    """The graph arrays, and the kind, name and module of every record."""
    g = np.load(os.path.join(graph, "graph.npz"))
    n = len(g["real"])
    kinds, names, modules = [""] * n, [""] * n, [""] * n
    with gzip.open(os.path.join(graph, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        head = f.readline().rstrip("\n").split("\t")
        col = {c: head.index(c) for c in ("id", "module", "kind", "name")}
        for line in f:
            p = line.rstrip("\n").split("\t")
            i = int(p[col["id"]])
            kinds[i], names[i], modules[i] = p[col["kind"]], p[col["name"]], p[col["module"]]
    return g, n, kinds, names, modules


def tree_of(ptr, adj, roots, n):
    """The dominator tree of a graph of n nodes, given as the row starts and the targets of its edges,
    from a virtual root that points to `roots`. Returns the reached nodes in reverse postorder with
    the virtual root first, the immediate dominator of each as a position in that order, the number
    of passes and the number of edges followed."""
    ptr, adj, roots = ptr.astype(np.int64), adj.astype(np.int64), np.asarray(roots, np.int64)
    order = reverse_postorder(ptr, adj, roots, n)
    number = np.full(n + 1, -1, np.int64)
    number[order] = np.arange(len(order))
    src = np.repeat(np.arange(n, dtype=np.int64), np.diff(ptr))
    keep = number[src] >= 0
    a = np.concatenate([np.zeros(len(roots), np.int64), number[src[keep]]])
    b = np.concatenate([number[roots], number[adj[keep]]])
    pred = a[np.argsort(b, kind="stable")]
    pptr = np.zeros(len(order) + 1, np.int64)
    np.cumsum(np.bincount(b, minlength=len(order)), out=pptr[1:])
    idom, passes = dominators(pptr, pred, len(order))
    return order, idom, passes, len(a)


def tree(g, n):
    """The dominator tree of the names graph. The five theorems are the roots, with the commands
    that Lean runs whenever it builds a file."""
    roots = np.concatenate([g["targets"], np.flatnonzero(g["always"])])
    return tree_of(g["strict_ptr"], g["strict"], roots, n)


def statement_of(module, name, cache):
    """The given part and the claim of a declaration, read from the source by the explorer's script."""
    if module not in cache:
        found = build_statements.statements(module)
        cache[module] = {d[1]: d for d in (found[1] if found else [])}
    d = cache[module].get(name)
    return ((d[3] if len(d) > 3 else ""), (d[4] if len(d) > 4 else "")) if d else ("", "")


def outline(nodes, kids, top, limit):
    """The skeleton as indented lines, largest first. A declaration that passes at least 99 % of what
    it gathers on to one declaration hanging from it is a wrapper, and a run of wrappers is folded
    into the line of its first declaration."""
    lines = []

    def walk(i, level):
        first, links = i, 0
        while kids.get(i) and nodes[kids[i][0]]["gathers"] >= WRAPPER * nodes[i]["gathers"]:
            i, links = kids[i][0], links + 1
        node, head = nodes[i], nodes[first]
        line = f"{head['gathers']:>9,}  {'  ' * level}{head['name']}"
        if links:
            line += f"  [{links} more to {node['name']}]"
        lines.append(line)
        for c in kids.get(i, []):
            if nodes[c]["gathers"] >= limit:
                walk(c, level + 1)

    walk(top, 0)
    return lines


def main():
    ap = argparse.ArgumentParser(description="Find the theorems that carry the argument of the proof.")
    ap.add_argument("--min", type=int, default=1000, help="declarations a node of the skeleton gathers at least (default 1000)")
    ap.add_argument("--outline", type=int, default=10000, help="declarations a line of OUTLINE.txt gathers at least (default 10000)")
    args = ap.parse_args()
    t0 = time.time()
    g, n, kinds, names, modules = load()
    order, idom, passes, edges = tree(g, n)
    count = len(order)
    real = np.zeros(count, np.int64)
    real[1:] = g["real"][order[1:]]
    theorem = np.zeros(count, np.int64)
    theorem[1:] = [kinds[v] in THEOREMS for v in order[1:].tolist()]
    below, below_theorems, depth = gather(idom, real), gather(idom, theorem), depths(idom)
    os.makedirs(DATA, exist_ok=True)
    np.savez_compressed(os.path.join(DATA, "tree.npz"), order=order, idom=idom, below=below,
                        below_theorems=below_theorems, depth=depth)
    sys.stderr.write(f"{count - 1:,} records reached, {edges:,} edges, {passes} passes, {time.time() - t0:.0f} s\n")

    # The skeleton: the declarations that gather at least --min declarations, themselves included.
    picked = [int(b) for b in np.flatnonzero(below >= args.min)[1:] if real[b]]
    slot = {b: k for k, b in enumerate(picked)}
    ptr, adj = g["strict_ptr"], g["strict"]
    number = np.full(n + 1, -1, np.int64)
    number[order] = np.arange(count)
    # The folder of a declaration is the first two parts of its module name, such as Development.WeilBound.
    folder_of, folder = {}, np.full(count, -1, np.int64)
    for b in np.flatnonzero(real).tolist():
        key = ".".join(modules[int(order[b])].split(".")[:2])
        folder[b] = folder_of.setdefault(key, len(folder_of))
    folder_names = list(folder_of)
    place = preorder(idom)
    in_walk = np.empty(count, np.int64)
    in_walk[place] = folder
    span = gather(idom, np.ones(count, np.int64))
    cache, nodes, kids = {}, [], {}
    for k, b in enumerate(picked):
        v = int(order[b])
        given, claim = statement_of(modules[v], names[v], cache)
        part = in_walk[place[b]:place[b] + span[b]]
        tally = np.bincount(part[part >= 0], minlength=len(folder_names))
        folders = [[folder_names[i], int(tally[i])] for i in np.argsort(-tally)[:4] if tally[i]]
        parent = slot.get(int(idom[b]))
        uses = sorted({slot[int(number[e])] for e in adj[ptr[v]:ptr[v + 1]].tolist() if int(number[e]) in slot} - {k})
        nodes.append({"name": names[v], "kind": kinds[v], "module": modules[v], "parent": parent,
                      "gathers": int(below[b]), "theorems": int(below_theorems[b]), "depth": int(depth[b]),
                      "uses": uses, "folders": folders, "given": given, "claim": claim})
        if parent is not None:
            kids.setdefault(parent, []).append(k)
    for k, node in enumerate(nodes):
        kids[k] = sorted(kids.get(k, []), key=lambda c: -nodes[c]["gathers"])
        node["own"] = node["gathers"] - 1 - sum(nodes[c]["gathers"] for c in kids[k])
        node["passes"] = round(nodes[kids[k][0]]["gathers"] / node["gathers"], 4) if kids[k] else 0
    top = max((k for k, node in enumerate(nodes) if node["parent"] is None), key=lambda k: nodes[k]["gathers"])
    heads = [k for k, node in enumerate(nodes) if node["passes"] < WRAPPER]

    reached = int(real.sum())
    steps = (100000, 10000, 1000, 100)
    summary = {
        "source": {"declarations": int(g["real"].sum()), "reached": reached, "records_reached": count - 1, "edges": edges},
        "tree": {"passes": passes, "depth": int(depth.max())},
        "gathering_at_least": {str(m): int(((below >= m) & (real > 0)).sum()) for m in steps},
        "skeleton": {"min": args.min, "nodes": len(nodes), "wrappers": len(nodes) - len(heads), "heads": len(heads),
                     "statements_found": sum(1 for node in nodes if node["claim"] or node["given"]),
                     "top": nodes[top]["name"], "top_gathers": nodes[top]["gathers"]},
        "largest": [{"name": nodes[k]["name"], "gathers": nodes[k]["gathers"], "own": nodes[k]["own"],
                     "share_of_reached": round(nodes[k]["gathers"] / reached, 4)}
                    for k in sorted(heads, key=lambda k: -nodes[k]["gathers"])[:40]],
    }
    with open(os.path.join(HERE, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    with open(os.path.join(HERE, "skeleton.json"), "w", encoding="utf-8") as f:
        json.dump({"min": args.min, "top": top, "nodes": nodes}, f, ensure_ascii=False, separators=(",", ":"))
    with open(os.path.join(HERE, "OUTLINE.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(outline(nodes, kids, top, args.outline)) + "\n")
    print(json.dumps({k: summary[k] for k in ("source", "tree", "gathering_at_least", "skeleton")}, indent=1))
    sys.stderr.write(f"done in {time.time() - t0:.0f} s\n")


if __name__ == "__main__":
    main()
