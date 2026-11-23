#!/usr/bin/env python3
"""Collect, for every line of the outline, the Lean statement and the definitions it names.

Usage: python3 -I verification/skeleton/dossier.py [--depth N] [--limit N]

Run build.py of this folder first. For the head of each line of OUTLINE.txt the script writes
one file data/dossiers/NN-name.md, which git ignores. A dossier holds

  the statement of the head, with the `variable` lines in scope
  the names and statements of the wrappers folded into its line
  the definitions that the statement names, then the definitions that those name, and so on

A definition is a def, abbrev, structure, class or inductive of the project. The script takes
the definitions that the declaration graph gives for a text and keeps those whose last name
part stands in that text. Definitions at the first two levels are written with their bodies,
deeper ones with their statements only. The dossiers are what a reader needs in order to say
what a line of the outline claims without opening the source.

The script also writes data/dossiers/index.json with the order, names and files of the lines.
"""
import argparse
import json
import os
import re
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build  # noqa: E402

OUT = os.path.join(build.DATA, "dossiers")
DEFINITIONS = ("def", "abbrev", "structure", "class", "inductive")
BODY_DEPTH = 2
BODY_CHARS = 2500


def main():
    ap = argparse.ArgumentParser(description="Collect the statement and the definitions of every outline line.")
    ap.add_argument("--depth", type=int, default=3, help="levels of definitions to follow (default 3)")
    ap.add_argument("--limit", type=int, default=45, help="definitions in one dossier at most (default 45)")
    ap.add_argument("--outline", type=int, default=10000, help="declarations a line gathers at least (default 10000)")
    args = ap.parse_args()
    g, n, kinds, names, modules = build.load()
    real, ptr, adj = g["real"], g["strict_ptr"], g["strict"]
    by_name = {}
    for v in np.flatnonzero(real).tolist():
        by_name.setdefault(names[v], v)
    with open(os.path.join(HERE, "skeleton.json"), encoding="utf-8") as f:
        sk = json.load(f)
    nodes = sk["nodes"]
    kids = {}
    for k, node in enumerate(nodes):
        if node["parent"] is not None:
            kids.setdefault(node["parent"], []).append(k)
    for k in kids:
        kids[k].sort(key=lambda c: -nodes[c]["gathers"])

    cache = {}

    def text_of(v):
        """The contexts, the given part, the claim, the body and the cut flags of a declaration."""
        m = modules[v]
        if m not in cache:
            found = build.build_statements.statements(m)
            cache[m] = (found[0], {d[1]: d for d in found[1]}) if found else ([], {})
        contexts, table = cache[m]
        d = table.get(names[v])
        if d is None:
            return None
        d = list(d) + [""] * (9 - len(d))
        return {"context": contexts[d[2] - 1] if d[2] else "", "given": d[3] or "", "claim": d[4] or "",
                "value": d[5] or "", "cut": bool(d[6] or d[7] or d[8])}

    def named_in(v, text):
        """The definitions that the graph gives for v and whose last name part stands in the text."""
        out = []
        for e in adj[ptr[v]:ptr[v + 1]].tolist():
            targets = [e] if real[e] else [x for x in adj[ptr[e]:ptr[e + 1]].tolist() if real[x]]
            for x in targets:
                if kinds[x] in DEFINITIONS and x != v:
                    last = names[x].rsplit(".", 1)[-1]
                    if re.search(r"(?<![\w'])" + re.escape(last) + r"(?![\w'])", text):
                        out.append(x)
        return sorted(set(out), key=lambda x: names[x])

    def show(v, t, body):
        lines = [f"### `{names[v]}`", "", f"{kinds[v]} in module `{modules[v]}`", ""]
        if t is None:
            return lines + ["The statement splitter did not find this declaration.", ""]
        if t["context"]:
            lines += ["Variables in scope:", "", "```lean", t["context"], "```", ""]
        code = (kinds[v] + " " + names[v].rsplit(".", 1)[-1] + (" " + t["given"] if t["given"] else "")
                + ((" :\n    " + t["claim"]) if t["claim"] else ""))
        if body and t["value"]:
            code += " :=\n" + t["value"][:BODY_CHARS] + ("\n  … (cut)" if len(t["value"]) > BODY_CHARS else "")
        lines += ["```lean", code, "```", ""]
        if t["cut"]:
            lines += ["The text above is cut, because the source text is longer than the splitter keeps.", ""]
        return lines

    os.makedirs(OUT, exist_ok=True)
    for f in os.listdir(OUT):
        os.remove(os.path.join(OUT, f))
    index = []

    def walk(k, level, parent):
        run = [k]
        while kids.get(run[-1]) and nodes[kids[run[-1]][0]]["gathers"] >= build.WRAPPER * nodes[run[-1]]["gathers"]:
            run.append(kids[run[-1]][0])
        head = run[-1]
        v = by_name[nodes[head]["name"]]
        t = text_of(v)
        number = len(index) + 1
        short = re.sub(r"[^\w]+", "_", nodes[head]["name"].rsplit(".", 1)[-1])[:60]
        file = f"{number:02d}-{short}.md"
        lines = [f"# Line {number} of the outline", "",
                 f"Head `{nodes[head]['name']}`, which gathers {nodes[run[0]]['gathers']:,} declarations.", ""]
        if parent:
            lines += [f"It hangs from line {parent[0]}, `{parent[1]}`.", ""]
        lines += ["## The statement", ""] + show(v, t, False)
        if len(run) > 1:
            lines += ["## Wrappers folded into this line", ""]
            for r in run[:-1]:
                lines += show(by_name[nodes[r]["name"]], text_of(by_name[nodes[r]["name"]]), False)
        # The definitions, level by level.
        seen, frontier, listed = {v}, [(v, (t["context"] + " " + t["given"] + " " + t["claim"]) if t else "")], []
        for depth in range(1, args.depth + 1):
            found = []
            for u, text in frontier:
                for x in named_in(u, text):
                    if x not in seen:
                        seen.add(x)
                        found.append(x)
            frontier = []
            for x in found:
                tx = text_of(x)
                listed.append((depth, x, tx))
                if tx:
                    frontier.append((x, tx["context"] + " " + tx["given"] + " " + tx["claim"] + " " + tx["value"]))
            if len(listed) >= args.limit:
                break
        dropped = max(0, len(listed) - args.limit)
        listed = listed[:args.limit]
        for depth in range(1, args.depth + 1):
            here = [(x, tx) for d, x, tx in listed if d == depth]
            if here:
                lines += [f"## Definitions, level {depth}", ""]
                if depth == 1:
                    lines += ["These are the definitions that the statement names.", ""]
                else:
                    lines += [f"These are the definitions that the definitions of level {depth - 1} name.", ""]
                for x, tx in here:
                    lines += show(x, tx, depth <= BODY_DEPTH)
        if dropped:
            lines += [f"{dropped} further definitions were left out, because the dossier holds {args.limit} at most.", ""]
        with open(os.path.join(OUT, file), "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
        index.append({"line": number, "level": level, "name": nodes[head]["name"], "first": nodes[run[0]]["name"],
                      "wrappers": [nodes[r]["name"] for r in run[:-1]], "gathers": nodes[run[0]]["gathers"],
                      "parent": parent[0] if parent else None, "file": file, "definitions": len(listed),
                      "chars": sum(len(x) for x in lines)})
        me = (number, nodes[head]["name"])
        for c in kids.get(head, []):
            if nodes[c]["gathers"] >= args.outline:
                walk(c, level + 1, me)

    walk(sk["top"], 0, None)
    with open(os.path.join(OUT, "index.json"), "w", encoding="utf-8") as f:
        json.dump(index, f, indent=1, ensure_ascii=False)
    print(f"{len(index)} dossiers, {sum(r['chars'] for r in index):,} characters, "
          f"largest {max(r['chars'] for r in index):,}, definitions {sum(r['definitions'] for r in index):,}")


if __name__ == "__main__":
    main()
