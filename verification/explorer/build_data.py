#!/usr/bin/env python3
"""Build the data for the proof explorer from the module import graph.

Usage: python3 -I verification/explorer/build_data.py

Needs verification/import-graph/{modules,edges}.tsv.gz (run ../import-graph/build.py first) and
networkx. Writes verification/explorer/data/, which is ignored by git and can be rebuilt.

The modules are numbered in preorder of the dominator tree, with each node's children sorted by
the lines below them, largest first. A subtree is then the id range [id, id + size), so a node's
children follow from the sizes alone, and the viewer loads only the chunk it shows.
"""
import collections
import gzip
import json
import os
import re

import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
GRAPH = os.path.join(REPO, "verification", "import-graph")
OUT = os.path.join(HERE, "data")
ROOT = "Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion"
CHUNK = 4000
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:({\[]+)?")
# Uses of the metaprogramming listed in verification/NOTES.md, where the elaborator does not
# check a term against its goal and the kernel is the only check.
FLAGS = [("kexactB", re.compile(r"\bkexactB\b")), ("kcopy", re.compile(r"\bkcopy\b")),
         ("run_tac", re.compile(r"\brun_tac\b")), ("addDecl", re.compile(r"\baddDecl\b"))]


def read_graph():
    lines, imports = {}, collections.defaultdict(list)
    with gzip.open(os.path.join(GRAPH, "modules.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for row in f:
            p = row.rstrip("\n").split("\t")
            if p[5] == "1":
                lines[p[0]] = int(p[1])
    with gzip.open(os.path.join(GRAPH, "edges.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for row in f:
            a, b = row.rstrip("\n").split("\t")
            if b in lines:
                imports[a].append(b)
    return lines, imports


def scan_source(mod):
    path = os.path.join(REPO, "src", *mod.split(".")) + ".lean"
    counts = collections.Counter()
    public = []
    flags = 0
    with open(path, encoding="utf-8") as f:
        text = f.read()
    for line in text.splitlines():
        m = DECL.match(line)
        if m:
            kind = "theorem" if m.group(2) in ("theorem", "lemma") else "def"
            counts[kind] += 1
            if m.group(1) != "private" and m.group(3) and len(public) < 12:
                public.append(m.group(3))
    for bit, (_, rx) in enumerate(FLAGS):
        if rx.search(text):
            flags |= 1 << bit
    return counts["theorem"], counts["def"], public, flags


def main():
    lines, imports = read_graph()
    g = nx.DiGraph()
    g.add_nodes_from(lines)
    g.add_edges_from((a, b) for a, bs in imports.items() for b in bs)
    idom = nx.immediate_dominators(g, ROOT)

    children = collections.defaultdict(list)
    for n, d in idom.items():
        if n != d:
            children[d].append(n)
    post, stack = [], [(ROOT, False)]
    while stack:
        n, done = stack.pop()
        if done:
            post.append(n)
        else:
            stack.append((n, True))
            stack.extend((c, False) for c in children[n])
    size, below = {}, {}
    for n in post:
        size[n] = 1 + sum(size[c] for c in children[n])
        below[n] = lines[n] + sum(below[c] for c in children[n])
    for n in children:
        children[n].sort(key=lambda c: (-below[c], c))

    order, stack = [], [ROOT]
    while stack:
        n = stack.pop()
        order.append(n)
        stack.extend(reversed(children[n]))
    ident = {n: i for i, n in enumerate(order)}
    importers = collections.defaultdict(list)
    for a, bs in imports.items():
        for b in bs:
            importers[b].append(ident[a])

    os.makedirs(OUT, exist_ok=True)
    # Names, prefix-coded against the previous name: [shared prefix length, rest].
    prev, coded = "", []
    for n in order:
        k = len(os.path.commonprefix([prev, n]))
        coded.append([k, n[k:]])
        prev = n
    with open(os.path.join(OUT, "names.json"), "w", encoding="utf-8") as f:
        json.dump(coded, f, ensure_ascii=False, separators=(",", ":"))

    totals = collections.Counter()
    for start in range(0, len(order), CHUNK):
        recs = []
        for i in range(start, min(start + CHUNK, len(order))):
            n = order[i]
            th, df, public, flags = scan_source(n)
            totals["theorems"] += th
            totals["defs"] += df
            for bit, (name, _) in enumerate(FLAGS):
                if flags >> bit & 1:
                    totals[name] += 1
            # [parent, size, own lines, lines below, theorems, defs, flags, imports, importers, public names]
            recs.append([ident[idom[n]] if n != ROOT else -1, size[n], lines[n], below[n], th, df, flags,
                         sorted(ident[b] for b in imports[n]), sorted(importers[n]), public])
        with open(os.path.join(OUT, f"chunk{start // CHUNK}.json"), "w", encoding="utf-8") as f:
            json.dump(recs, f, ensure_ascii=False, separators=(",", ":"))

    meta = {
        "root": ROOT,
        "modules": len(order),
        "lines": below[ROOT],
        "edges": sum(len(v) for v in imports.values()),
        "chunk": CHUNK,
        "chunks": (len(order) + CHUNK - 1) // CHUNK,
        "rootChildren": len(children[ROOT]),
        "flags": [name for name, _ in FLAGS],
        "totals": totals,
        "repo": "https://github.com/markomanninen/riemann-hypothesis/blob/main/src/",
    }
    depth = {ROOT: 0}
    for n in order[1:]:
        depth[n] = depth[idom[n]] + 1
    meta["depth"] = max(depth.values())
    with open(os.path.join(OUT, "meta.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
