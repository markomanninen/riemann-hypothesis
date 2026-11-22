#!/usr/bin/env python3
"""List the statements that the code names as published, and place them on the skeleton.

Usage: python3 -I verification/skeleton/published.py

Run build.py of this folder first. The source keeps many statements from the literature as
definitions of type Prop in namespaces called Published, Pub, Lit, LiteratureTheorems and
Hypotheses₂, such as GlobalTheory.Published.JacquetShalikaRigidity. A theorem that needs such a
result takes the statement as a premise, and another theorem of the project proves it.

The script finds every such statement that has no parameters. For each one it looks at the
theorems whose text names the statement and reads their own statements from the source:

  proves     the theorem has no premises and its claim is the statement
  derives    the claim ends in the statement after premises, so the theorem proves it from them
  takes      the statement stands among the premises of the theorem

It then marks every skeleton declaration with the published statements it takes and the one it
proves or derives. It also counts the declarations whose name or module path holds a name part
that matches an ingredient of the author's note, and counts how many of them lie below each of
four declarations of the outline. The matches are matches of names. They do not show what the
mathematics is.

The script writes published.json and OUTLINE-PUBLISHED.txt next to itself and prints the figures.
OUTLINE-PUBLISHED.txt is OUTLINE.txt with the folder of every declaration and its marks.
"""
import collections
import json
import os
import re
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build  # noqa: E402

MARK = re.compile(r"(?:^|\.)(Published|Pub|Lit|LiteratureTheorems|Hypotheses₂)\.([^.]+)$")
NAME = re.compile(r"@?(?:_root_\.)?([\w.'₀-₉!?«»]+)")
OPENERS, CLOSERS = "([{⟨⦃", ")]}⟩⦄"
THEOREMS = ("theorem", "lemma")
BRANCH = 10000
# The parts of the skeleton that the name matches are counted under. The second lies inside the first.
PARTS = [
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
    "UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound",
    "UpperTheory.One.vwin_of_row",
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
]

# Ingredients of the author's note, each with a pattern for one part of a name or of a module path.
# The choice of patterns is a reading of the note by the author of this script.
TERMS = [
    ("theta lifts", r"Theta(Pair)?Lifts?$|^ThetaCorrespondence$|^ThetaLift"),
    ("definite unitary groups", r"Definite.*Unitary|Unitary.*Definite|^DefiniteSide|^TotallyDefinite"),
    ("Chowla-Selberg", r"[Cc]howla"),
    ("Siegel mass", r"SiegelMass|MassFormula"),
    ("Weyl, with divisibility", r"WeylDivisibility"),
    ("divisibility of the lift", r"^Divisibility(Proofs|Towers)?$|LiftDivisib"),
    ("Iwasawa tower", r"Iwasawa.*Tower|Tower.*Iwasawa"),
    ("seesaw", r"[Ss]eesaw|SeeSaw"),
    ("Bessel period", r"Bessel"),
    ("Rallis", r"Rallis"),
    ("Bost slope inequality", r"Bost|Slope"),
    ("relative trace formula", r"RelativeTrace|^TraceFormula$"),
    ("Poincare series", r"Poincare.?Series"),
    ("GGP periods", r"GGP|GanGross|Ggp"),
    ("weakening of Vandiver", r"[Vv]andiver"),
    ("covolumes", r"[Cc]ovol"),
    ("Behrend", r"[Bb]ehrend"),
    ("Guinand-Weil explicit formula", r"Guinand|ExplicitFormula"),
    ("von Mangoldt sum", r"[Mm]angoldt"),
    ("Stepanov", r"[Ss]tepanov"),
]


def build_words(name):
    """A folder name as words: DivisorProofs reads Divisor Proofs."""
    name = re.sub(r"([A-Z])([A-Z][a-z])", r"\1 \2", name)
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name)


def conclusion(claim):
    """The text of a claim after its last arrow outside brackets."""
    depth, start = 0, 0
    for i, ch in enumerate(claim):
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
        elif ch == "→" and depth == 0:
            start = i + 1
    return claim[start:].strip(), start > 0


def main():
    g, n, kinds, names, modules = build.load()
    tree = np.load(os.path.join(build.DATA, "tree.npz"))
    order, idom, below = tree["order"], tree["idom"], tree["below"]
    number = np.full(n + 1, -1, np.int64)
    number[order] = np.arange(len(order))
    real = g["real"]
    with open(os.path.join(HERE, "skeleton.json"), encoding="utf-8") as f:
        skeleton = json.load(f)["nodes"]
    by_name = {}
    for v in np.flatnonzero(real).tolist():
        by_name.setdefault(names[v], v)
    slot = {int(number[by_name[node["name"]]]): k for k, node in enumerate(skeleton)}

    def nearest(b):
        """The index of the nearest skeleton declaration at or above the tree position b."""
        while b > 0 and b not in slot:
            b = int(idom[b])
        return slot.get(b)

    cache = {}

    def statement(v):
        if modules[v] not in cache:
            found = build.build_statements.statements(modules[v])
            cache[modules[v]] = {d[1]: d for d in (found[1] if found else [])}
        d = cache[modules[v]].get(names[v])
        return ((d[3] if len(d) > 3 else "").strip(), (d[4] if len(d) > 4 else "").strip()) if d else None

    # The published statements: definitions of type Prop without parameters in the marked namespaces.
    stated = {}
    for v in np.flatnonzero(real).tolist():
        if kinds[v] in ("def", "abbrev", "structure") and MARK.search(names[v]):
            s = statement(v)
            if s and not s[0] and s[1] == "Prop":
                stated[v] = MARK.search(names[v]).group(1)
    ptr, adj = g["strict_ptr"], g["strict"]
    src = np.repeat(np.arange(n), np.diff(ptr))
    hit = np.isin(adj, np.fromiter(stated, np.int64, len(stated)))
    users = collections.defaultdict(list)
    for a, b in zip(src[hit].tolist(), adj[hit].tolist()):
        users[b].append(a)

    role = {}  # (theorem, statement) -> proves, derives or takes
    for s in stated:
        last = names[s].rsplit(".", 1)[-1]
        word = re.compile(r"(?<![\w.'])(?:[\w.'₀-₉]+\.)?" + re.escape(last) + r"(?![\w'])")
        for u in users.get(s, ()):
            if kinds[u] not in THEOREMS and kinds[u] != "alias":
                continue
            text = statement(u)
            if not text:
                continue
            given, claim = text
            end, arrows = conclusion(claim)
            m = NAME.fullmatch(end)
            if m and m.group(1).rsplit(".", 1)[-1] == last:
                role[(u, s)] = "derives" if (given or arrows) else "proves"
            elif word.search(given) or word.search(claim):
                role[(u, s)] = "takes"

    statements = []
    for s, mark in stated.items():
        proofs = [u for u in users.get(s, ()) if role.get((u, s)) == "proves"]
        best = max(proofs, key=lambda u: below[number[u]] if number[u] >= 0 else -1, default=None)
        where = nearest(int(number[best])) if best is not None and number[best] >= 0 else None
        statements.append({
            "name": names[s], "namespace": mark, "module": modules[s], "reached": bool(number[s] >= 0),
            "proofs": len(proofs), "derivations": sum(1 for u in users.get(s, ()) if role.get((u, s)) == "derives"),
            "taken_by": sum(1 for u in users.get(s, ()) if role.get((u, s)) == "takes"),
            "proof": names[best] if best is not None else "",
            "proof_gathers": int(below[number[best]]) if best is not None and number[best] >= 0 else 0,
            "below": skeleton[where]["name"] if where is not None else ""})
    statements.sort(key=lambda r: (-r["proof_gathers"], r["name"]))

    marks = []
    for k, node in enumerate(skeleton):
        v = by_name[node["name"]]
        mine = {s: role[(v, s)] for s in adj[ptr[v]:ptr[v + 1]].tolist() if (v, s) in role}
        marks.append({"takes": sorted(names[s] for s, r in mine.items() if r == "takes"),
                      "proves": sorted(names[s] for s, r in mine.items() if r == "proves"),
                      "derives": sorted(names[s] for s, r in mine.items() if r == "derives")})

    # Where the ingredients of the note sit: the branches are the heads that gather at least BRANCH.
    heads = {k for k, node in enumerate(skeleton) if node["gathers"] >= BRANCH and node["passes"] < build.WRAPPER}
    head_at = {b: k for b, k in slot.items() if k in heads}
    owner = np.full(len(order), -1, np.int64)
    for b in range(1, len(order)):
        owner[b] = head_at.get(b, owner[idom[b]])
    place_of = build.preorder(idom)
    size_of = build.gather(idom, np.ones(len(order), np.int64))
    spans = [(int(place_of[number[by_name[x]]]), int(place_of[number[by_name[x]]] + size_of[number[by_name[x]]])) for x in PARTS]
    parts_of = {}
    terms = []
    for label, pattern in TERMS:
        rx = re.compile(pattern)
        total = reached = 0
        inside = [0] * len(PARTS)
        parts, branches = collections.Counter(), collections.Counter()
        for v in np.flatnonzero(real).tolist():
            key = (names[v], modules[v])
            if key not in parts_of:
                parts_of[key] = set(names[v].split(".")) | set(modules[v].split("."))
            found = [p for p in parts_of[key] if rx.search(p)]
            if not found:
                continue
            total += 1
            parts.update(found)
            if number[v] >= 0:
                reached += 1
                branches[int(owner[number[v]])] += 1
                at = int(place_of[number[v]])
                for i, (lo, hi) in enumerate(spans):
                    inside[i] += lo <= at < hi
        terms.append({"ingredient": label, "pattern": pattern, "declarations": total, "reached": reached,
                      "parts": parts.most_common(4), "below": dict(zip(PARTS, inside)),
                      "branches": [[skeleton[k]["name"] if k >= 0 else "", c] for k, c in branches.most_common(3)]})

    # The declarations that lie at or below at least one of the proofs, each counted once.
    place = build.preorder(idom)
    span = build.gather(idom, np.ones(len(order), np.int64))
    under = np.zeros(len(order) + 1, np.int64)
    for s in stated:
        for u in users.get(s, ()):
            if role.get((u, s)) == "proves" and number[u] >= 0:
                b = int(number[u])
                under[place[b]] += 1
                under[place[b] + span[b]] -= 1
    covered = np.cumsum(under[:-1]) > 0
    is_real = np.zeros(len(order), bool)
    is_real[place[1:]] = real[order[1:]]
    proved_inside = int((covered & is_real).sum())

    # The outline of build.py again, with the folder and the marks of every line.
    kids = collections.defaultdict(list)
    for k, node in enumerate(skeleton):
        if node["parent"] is not None:
            kids[node["parent"]].append(k)
    lines = []

    def tag(k):
        m = marks[k]
        got = [f"takes {len(m['takes'])}"] if m["takes"] else []
        got += [f"proves {x.rsplit('.', 1)[-1]}" for x in m["proves"]] + [f"derives {x.rsplit('.', 1)[-1]}" for x in m["derives"]]
        return ", ".join(got)

    def walk(k, level):
        run = [k]
        while kids[run[-1]] and skeleton[max(kids[run[-1]], key=lambda c: skeleton[c]["gathers"])]["gathers"] >= build.WRAPPER * skeleton[run[-1]]["gathers"]:
            run.append(max(kids[run[-1]], key=lambda c: skeleton[c]["gathers"]))
        head = skeleton[run[-1]]
        folder = " › ".join(build_words(x) for x in head["module"].split(".")[1:4])
        tags = " | ".join(t for t in dict.fromkeys(tag(r) for r in run) if t)
        lines.append(f"{skeleton[run[0]]['gathers']:>9,}  {'  ' * level}{head['name'].rsplit('.', 1)[-1]}   [{folder}]" + (f"   {{{tags}}}" if tags else ""))
        for c in sorted(kids[run[-1]], key=lambda c: -skeleton[c]["gathers"]):
            if skeleton[c]["gathers"] >= BRANCH:
                walk(c, level + 1)

    walk(next(k for k, node in enumerate(skeleton) if node["parent"] is None), 0)
    with open(os.path.join(HERE, "OUTLINE-PUBLISHED.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    # The same shares for all reached declarations, as the level that a row of matches is compared with.
    places = place_of[number[np.flatnonzero((number[:n] >= 0) & real)]]
    baseline = {"reached": int(len(places)),
                "below": {x: int(((places >= lo) & (places < hi)).sum()) for x, (lo, hi) in zip(PARTS, spans)}}

    reached = [r for r in statements if r["reached"]]
    summary = {
        "statements": len(statements), "by_namespace": dict(collections.Counter(r["namespace"] for r in statements)),
        "reached": len(reached), "reached_with_a_proof": sum(1 for r in reached if r["proofs"]),
        "reached_with_a_reached_proof": sum(1 for r in reached if r["proof_gathers"]),
        "reached_with_only_derivations": sum(1 for r in reached if not r["proofs"] and r["derivations"]),
        "reached_with_neither": sum(1 for r in reached if not r["proofs"] and not r["derivations"]),
        "declarations_at_or_below_a_proof": proved_inside,
        "skeleton_that_takes": sum(1 for m in marks if m["takes"]),
        "skeleton_that_proves_or_derives": sum(1 for m in marks if m["proves"] or m["derives"]),
        "skeleton_with_no_mark": sum(1 for m in marks if not (m["takes"] or m["proves"] or m["derives"])),
    }
    with open(os.path.join(HERE, "published.json"), "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "statements": statements, "skeleton": marks, "terms": terms,
                   "all_reached": baseline}, f,
                  ensure_ascii=False, indent=1)
    print(json.dumps(summary, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
