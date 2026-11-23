#!/usr/bin/env python3
"""The skeleton again, with every repeated statement counted once.

Usage: python3 -I verification/skeleton/clean.py

Run build.py of this folder and the scan and check of verification/redundancy first. The file
data/same_checked.tsv of that folder lists theorems that Lean found to state exactly what another
theorem states, as forwarding pairs and as groups with the same statement text. This script
joins such theorems into classes and keeps one theorem of each class, its keeper. It prefers a
keeper that is no forwarding theorem, and among those the one that comes first in the order of
the modules. Every mention of another member of the class is pointed at the keeper, and the
other members are left out with their own proofs.

The script then computes the dominator tree and the skeleton of this smaller graph, as build.py
does for the whole graph, and writes

  clean.json   the figures, the skeleton of the smaller graph, and for every declaration of
               the skeleton of build.py its keeper when it is not its own keeper

The result estimates what the proof would look like after such a cleanup. It is no cleanup of
the source, and no part of it has been compiled.
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

REDUNDANCY = os.path.join(os.path.dirname(HERE), "redundancy", "data")
THEOREMS = ("theorem", "lemma")


def main():
    g, n, kinds, names, modules = build.load()
    real = g["real"]
    by = {}
    for v in np.flatnonzero(real).tolist():
        by.setdefault((modules[v], names[v]), v)
    forwarding = set()
    with gzip.open(os.path.join(REDUNDANCY, "findings.tsv.gz"), "rt", encoding="utf-8") as f:
        head = f.readline().rstrip("\n").split("\t")
        for line in f:
            p = dict(zip(head, line.rstrip("\n").split("\t")))
            if "forward" in p["classes"].split(",") and (p["module"], p["name"]) in by:
                forwarding.add(by[(p["module"], p["name"])])

    # Join the theorems that Lean found to have one statement. Groups F are forwarding pairs and
    # groups T are theorems with the same statement text. Groups D are definitions and stay out.
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    members = collections.defaultdict(list)
    with open(os.path.join(REDUNDANCY, "same_checked.tsv"), encoding="utf-8") as f:
        for line in f:
            group, module, name, found, _, number = line.rstrip("\n").split("\t")
            if group[0] in "FT" and found == "1" and (module, name) in by and kinds[by[(module, name)]] in THEOREMS:
                members[(group, number)].append(by[(module, name)])
    for group in members.values():
        for x in group[1:]:
            a, b = find(group[0]), find(x)
            if a != b:
                parent[b] = a
    classes = collections.defaultdict(list)
    for v in {x for group in members.values() for x in group}:
        classes[find(v)].append(v)
    keeper = np.arange(n, dtype=np.int64)
    for group in classes.values():
        if len(group) > 1:
            best = min(group, key=lambda v: (v in forwarding, v))
            keeper[group] = best
    joined = int((keeper != np.arange(n)).sum())

    # The smaller graph: only keepers have edges, and every edge points at a keeper.
    ptr, adj = g["strict_ptr"].astype(np.int64), g["strict"].astype(np.int64)
    own = keeper == np.arange(n)
    counts = np.where(own, np.diff(ptr), 0)
    new_ptr = np.zeros(n + 1, np.int64)
    np.cumsum(counts, out=new_ptr[1:])
    src = np.repeat(np.arange(n), np.diff(ptr))
    new_adj = keeper[adj[own[src]]]
    roots = keeper[np.concatenate([g["targets"], np.flatnonzero(g["always"])]).astype(np.int64)]
    order, idom, passes, edges = build.tree_of(new_ptr, new_adj, roots, n)
    count = len(order)
    weight = np.zeros(count, np.int64)
    weight[1:] = real[order[1:]]
    below = build.gather(idom, weight)
    reached = int(weight.sum())

    with open(os.path.join(HERE, "skeleton.json"), encoding="utf-8") as f:
        old = json.load(f)
    with open(os.path.join(HERE, "summary.json"), encoding="utf-8") as f:
        before = json.load(f)
    picked = [int(b) for b in np.flatnonzero(below >= old["min"])[1:] if weight[b]]
    slot = {b: k for k, b in enumerate(picked)}
    nodes, kids = [], collections.defaultdict(list)
    for k, b in enumerate(picked):
        v = int(order[b])
        up = slot.get(int(idom[b]))
        nodes.append({"name": names[v], "module": modules[v], "parent": up, "gathers": int(below[b])})
        if up is not None:
            kids[up].append(k)
    wrappers = 0
    for k, node in enumerate(nodes):
        most = max((nodes[c]["gathers"] for c in kids[k]), default=0)
        node["own"] = node["gathers"] - 1 - sum(nodes[c]["gathers"] for c in kids[k])
        node["passes"] = round(most / node["gathers"], 4)
        wrappers += node["passes"] >= build.WRAPPER
    by_name = {}
    for v in np.flatnonzero(real).tolist():
        by_name.setdefault(names[v], v)
    old_ids = [by_name[x["name"]] for x in old["nodes"]]
    kept = {x["name"]: names[int(keeper[v])] for x, v in zip(old["nodes"], old_ids) if keeper[v] != v}
    in_new = {node["name"] for node in nodes}
    steps = (100000, 10000, 1000)
    out = {
        "classes_with_more_than_one_theorem": sum(1 for c in classes.values() if len(c) > 1),
        "theorems_left_out": joined,
        "before": {"reached": before["source"]["reached"], "gathering_at_least": before["gathering_at_least"],
                   "skeleton": len(old["nodes"]), "wrappers": before["skeleton"]["wrappers"], "heads": before["skeleton"]["heads"],
                   "depth": before["tree"]["depth"]},
        "after": {"reached": reached, "gathering_at_least": {str(m): int(((below >= m) & (weight > 0)).sum()) for m in steps},
                  "skeleton": len(nodes), "wrappers": int(wrappers), "heads": len(nodes) - int(wrappers),
                  "depth": int(build.depths(idom).max())},
        "old_skeleton": {"left_out_as_a_repeat": len(kept), "still_in_the_skeleton": sum(1 for x in old["nodes"] if x["name"] in in_new),
                         "kept_but_below_the_limit": sum(1 for x in old["nodes"] if x["name"] not in kept and x["name"] not in in_new)},
        "keeper_of": kept,
        "nodes": nodes,
    }
    with open(os.path.join(HERE, "clean.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    print(json.dumps({k: out[k] for k in ("classes_with_more_than_one_theorem", "theorems_left_out", "before", "after", "old_skeleton")}, indent=1))
    for node in sorted(nodes, key=lambda x: -x["gathers"])[:12]:
        print(f"{node['gathers']:>9,}  {node['name']}")


if __name__ == "__main__":
    main()
