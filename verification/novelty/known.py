#!/usr/bin/env python3
"""Place the known results that the source proves on the outline of the proof.

Usage: python3 -I verification/novelty/known.py

Run exact_graph.py of verification/decl-graph, exact_tree.py of verification/skeleton and
statements.py of verification/reuse first, and have audit.json and catalogue.json of
verification/reuse in place.

A known result is one of two things.

  a proposition   that the source labels as a result from the literature, that the five theorems
                  reach and that a theorem of the source states without hypotheses
  a statement     of the catalogue of verification/reuse that its check takes for a named
                  theorem or a standard fact, other than the three forms of the Riemann
                  hypothesis that the source claims

For each known result the script takes the theorem that proves it and finds two things in the
exact graph.

  its line   the lowest line of the outline of verification/skeleton that gathers the proving
             theorem, which is the last line through which every use by the five theorems passes
  its cone   the declarations that the proving theorem rests on

It then counts, for each line of the outline, how many of the declarations that the line
gathers lie in the cone of some known result. It writes known.json next to itself and prints
the figures.
"""
import collections
import gzip
import json
import os
import re
import sys

import numba
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFICATION = os.path.dirname(HERE)
GRAPH = os.path.join(VERIFICATION, "decl-graph", "data")
SKELETON = os.path.join(VERIFICATION, "skeleton")
REUSE = os.path.join(VERIFICATION, "reuse")
# The folder of the skeleton goes first, so that `build` is the script of the skeleton.
sys.path.insert(0, os.path.join(VERIFICATION, "decl-graph"))
sys.path.insert(0, SKELETON)
import build  # noqa: E402
from exact_graph import user_name  # noqa: E402

CLAIMED = {"critAll", "riemannHypothesis", "rhOfAll"}
# Two premises of the route that the commentary of verification/strategy reads as published
# theorems and that the source does not label as results from the literature. The first is the
# existence of Galois representations and the second Green's parametrisation of cuspidal
# characters. They are counted in a second set of figures.
PREMISES = {"Row": "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
            "Green": "PositivityTheory.GreenCharacters.green"}


@numba.njit(cache=True)
def reach(ptr, edges, starts):
    """The nodes that the edges reach from the starts, the starts included."""
    n = len(ptr) - 1
    seen = np.zeros(n, np.bool_)
    stack = np.empty(n, np.int64)
    sp = 0
    for s in starts:
        if not seen[s]:
            seen[s] = True
            stack[sp] = s
            sp += 1
    while sp > 0:
        sp -= 1
        v = stack[sp]
        for j in range(ptr[v], ptr[v + 1]):
            w = edges[j]
            if not seen[w]:
                seen[w] = True
                stack[sp] = w
                sp += 1
    return seen


def main():
    g = np.load(os.path.join(GRAPH, "exact_graph.npz"))
    ptr, edges, row, starts = g["ptr"], g["edges"].astype(np.int64), g["row"], g["starts"]
    n = len(row)
    names, modules, kinds = [None] * n, [None] * n, [None] * n
    with gzip.open(os.path.join(GRAPH, "exact_nodes.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for line in f:
            i, m, name, k, _, _ = line.rstrip("\n").split("\t")
            names[int(i)], modules[int(i)], kinds[int(i)] = name, m, k
    by_user = {}
    for i in range(n):
        if row[i] >= 0:
            by_user.setdefault(user_name(modules[i], names[i]), i)

    # The dominator tree of the exact graph, as exact_tree.py computes it.
    order, idom, _, _ = build.tree_of(ptr, edges, starts, n)
    count = len(order)
    number = np.full(n, -1, np.int64)
    number[order[1:]] = np.arange(1, count)
    rows = np.full(count, -1, np.int64)
    rows[1:] = row[order[1:]]
    real = (rows >= 0).astype(np.int64)
    gathers = build.gather(idom, real)

    # The lines of the outline, with the numbers that READING.md gives them.
    numbers = {}
    for file in ("reading.json", "reading-exact.json"):
        with open(os.path.join(SKELETON, file), encoding="utf-8") as f:
            for r in json.load(f)["lines"]:
                numbers[r["name"]] = r["line"]
    lines, line_of_pos = [], {}
    with open(os.path.join(SKELETON, "OUTLINE-EXACT.txt"), encoding="utf-8") as f:
        for text in f:
            m = re.match(r"\s*([\d,]+)  (\s*)(\S+)(?:\s+\[\d+ more to (\S+)\])?", text)
            if not m:
                continue
            first, head = m.group(3), m.group(4) or m.group(3)
            entry = {"line": numbers[head], "level": len(m.group(2)) // 2, "first": first, "head": head,
                     "gathers": int(m.group(1).replace(",", ""))}
            lines.append(entry)
            # Every node between the first wrapper and the head belongs to the line.
            p, top = int(number[by_user[head]]), int(number[by_user[first]])
            while True:
                line_of_pos[p] = entry["line"]
                if p == top or p == 0:
                    break
                p = int(idom[p])
    by_line = {e["line"]: e for e in lines}

    def line_of(node):
        """The lowest line of the outline that gathers a node, or None."""
        p = int(number[node])
        if p < 0:
            return None
        while p > 0:
            if p in line_of_pos:
                return line_of_pos[p]
            p = int(idom[p])
        return None

    # The known results.
    with open(os.path.join(REUSE, "summary.json"), encoding="utf-8") as f:
        published = [p for p in json.load(f)["published"]["list"] if p["proof"] and p["reached"]]
    with open(os.path.join(REUSE, "audit.json"), encoding="utf-8") as f:
        audit = {e["name"]: e for e in json.load(f)["propositions"]}
    with open(os.path.join(REUSE, "catalogue.json"), encoding="utf-8") as f:
        catalogue = [e for e in json.load(f)["theorems"]
                     if e["check"]["kind"] in ("named theorem", "standard fact")
                     and e["name"].rsplit(".", 1)[-1] not in CLAIMED and e["used"]]
    known, missing = [], []
    for p in published:
        node = by_user.get(p["proof"])
        if node is None:
            missing.append(p["proof"])
            continue
        a = audit.get(p["name"])
        known.append({"source": "proposition", "name": p["name"], "proof": p["proof"], "node": node,
                      "vocabulary": p["vocabulary"], "rests_on": p["proof_rests_on"],
                      "known_as": a["a"]["classical_name"] if a else None,
                      "relation": a["check"]["relation"] if a else None})
    for e in catalogue:
        node = by_user.get(e["name"])
        if node is None:
            missing.append(e["name"])
            continue
        known.append({"source": "catalogue", "name": e["name"], "proof": e["name"], "node": node,
                      "vocabulary": 0, "rests_on": e["rests_on"], "kind": e["check"]["kind"],
                      "known_as": e["check"]["known_as"], "relation": e["check"]["relation"]})
    for k in known:
        k["line"] = line_of(k["node"])
        k["gathers"] = int(gathers[number[k["node"]]]) if number[k["node"]] >= 0 else 0

    # The declarations in the cone of some known result, and their share below each line.
    decl = row >= 0
    cone_all = reach(ptr, edges, np.array([k["node"] for k in known], np.int64))
    cone_prop = reach(ptr, edges, np.array([k["node"] for k in known if k["source"] == "proposition"], np.int64))
    premise_nodes = {k: by_user[v] for k, v in PREMISES.items()}
    cone_wide = cone_all | reach(ptr, edges, np.array(sorted(premise_nodes.values()), np.int64))
    in_cone = np.zeros(count, np.int64)
    in_cone[1:] = (cone_all[order[1:]] & decl[order[1:]]).astype(np.int64)
    below = build.gather(idom, in_cone)
    in_wide = np.zeros(count, np.int64)
    in_wide[1:] = (cone_wide[order[1:]] & decl[order[1:]]).astype(np.int64)
    below_wide = build.gather(idom, in_wide)
    reached = np.zeros(n, bool)
    reached[order[1:]] = True
    for e in lines:
        p = int(number[by_user[e["first"]]])
        e["in_a_cone"] = int(below[p])
        e["share"] = round(e["in_a_cone"] / e["gathers"], 4) if e["gathers"] else 0
        e["in_a_cone_with_premises"] = int(below_wide[p])
        e["share_with_premises"] = round(e["in_a_cone_with_premises"] / e["gathers"], 4) if e["gathers"] else 0
        mine = [k for k in known if k["line"] == e["line"]]
        e["propositions"] = sum(1 for k in mine if k["source"] == "proposition")
        e["catalogue"] = sum(1 for k in mine if k["source"] == "catalogue")
        e["named"] = sorted({k["name"] for k in mine if k.get("kind") == "named theorem"
                             or (k["source"] == "proposition" and k["relation"])})
    total = int((reached & decl).sum())
    for k in known:
        del k["node"]
    summary = {
        "reached_declarations": total,
        "known_results": {"propositions": sum(1 for k in known if k["source"] == "proposition"),
                          "catalogue": sum(1 for k in known if k["source"] == "catalogue"),
                          "not_found": missing},
        "in_the_cone_of_a_known_result": int((cone_all & decl & reached).sum()),
        "in_the_cone_of_a_proposition": int((cone_prop & decl & reached).sum()),
        "share": round(float((cone_all & decl & reached).sum()) / total, 4),
        "premises": {k: {"theorem": PREMISES[k], "line": line_of(v),
                         "rests_on": int((reach(ptr, edges, np.array([v], np.int64)) & decl).sum())}
                     for k, v in premise_nodes.items()},
        "in_a_cone_with_premises": int((cone_wide & decl & reached).sum()),
        "share_with_premises": round(float((cone_wide & decl & reached).sum()) / total, 4),
        "known_results_by_line": dict(collections.Counter(str(k["line"]) for k in known).most_common()),
        "lines": lines,
        "known": sorted(known, key=lambda k: (k["line"] if k["line"] is not None else 0, -k["rests_on"])),
    }
    with open(os.path.join(HERE, "known.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in summary.items() if k not in ("lines", "known")}, indent=1, ensure_ascii=False))
    for e in lines:
        print(f"{e['line']:>3} {'  ' * e['level']}{e['head'].rsplit('.', 1)[-1][:46]:46} gathers {e['gathers']:>8,} "
              f"in a cone {e['share']:6.1%} with premises {e['share_with_premises']:6.1%}  props {e['propositions']:>3} "
              f"cat {e['catalogue']:>3}")


if __name__ == "__main__":
    main()
