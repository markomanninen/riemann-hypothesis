#!/usr/bin/env python3
"""Sort the theorems of the project by what their statements are written with.

Usage: python3 -I verification/reuse/statements.py

Run exact_graph.py, exact_axioms.py and statement_extract.py of verification/decl-graph first.
The script reads these files of verification/decl-graph/data.

  exact_graph.npz, exact_nodes.tsv.gz   every compiled constant of the project, with the project
                                        constants that its type and value mention
  exact/chunk-*.tsv.gz                  the same mentions as names, library constants included
  exact/types-*.tsv.gz                  for every public constant, what its type mentions
  exact/lib-*.tsv.gz                    the constants of Mathlib, the other packages and Lean
  declarations.tsv.gz                   the declarations of the source text

The statement of a theorem is its compiled type. The vocabulary of a statement is the set of
project definitions that the statement needs in order to be read. It is found by following
mentions from the statement. A definition, structure, constructor or other constant that is
not a theorem is followed into everything that its type and its value mention. A theorem that
a definition mentions is followed into its statement only, because a proof does not change
what a definition means.

The script answers four questions and writes summary.json next to itself, with longer lists in
data/, which git ignores.

  1. Which theorems have a statement written with library constants only, so that the statement
     can be read without any definition of the project, and how many declarations does the
     proof of each rest on?
  2. How many project definitions does the statement of a theorem need?
  3. Which areas of Mathlib does a statement touch, directly or through its vocabulary, and in
     particular how many statements involve zeta and L-functions?
  4. What do the statements need that the source labels as results from the literature?
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
VERIFICATION = os.path.dirname(HERE)
GRAPH = os.path.join(VERIFICATION, "decl-graph", "data")
OUT = os.path.join(HERE, "data")
sys.path.insert(0, os.path.join(VERIFICATION, "decl-graph"))
from exact_graph import user_name  # noqa: E402

# An area is a part of Mathlib, named by a prefix of the module that holds a constant. The
# longest matching prefix decides. A library constant outside Mathlib counts as Lean and tools.
AREAS = [
    ("zeta and L-series", ["Mathlib.NumberTheory.LSeries", "Mathlib.NumberTheory.EulerProduct",
                           "Mathlib.NumberTheory.ZetaValues", "Mathlib.NumberTheory.Harmonic.ZetaAsymp",
                           "Mathlib.NumberTheory.NumberField.DedekindZeta"]),
    ("Dirichlet and multiplicative characters", ["Mathlib.NumberTheory.DirichletCharacter", "Mathlib.NumberTheory.MulChar",
                                                 "Mathlib.NumberTheory.GaussSum", "Mathlib.NumberTheory.LegendreSymbol"]),
    ("arithmetic functions", ["Mathlib.NumberTheory.ArithmeticFunction", "Mathlib.NumberTheory.VonMangoldt"]),
    ("number fields", ["Mathlib.NumberTheory.NumberField", "Mathlib.NumberTheory.Cyclotomic",
                       "Mathlib.NumberTheory.ClassNumber", "Mathlib.NumberTheory.RamificationInertia",
                       "Mathlib.NumberTheory.FunctionField", "Mathlib.NumberTheory.KummerDedekind"]),
    ("p-adic numbers", ["Mathlib.NumberTheory.Padics"]),
    ("modular forms", ["Mathlib.NumberTheory.ModularForms"]),
    ("other number theory", ["Mathlib.NumberTheory"]),
    ("algebraic geometry", ["Mathlib.AlgebraicGeometry"]),
    ("representation theory", ["Mathlib.RepresentationTheory"]),
    ("category theory", ["Mathlib.CategoryTheory"]),
    ("algebraic topology", ["Mathlib.AlgebraicTopology"]),
    ("measure theory", ["Mathlib.MeasureTheory"]),
    ("probability", ["Mathlib.Probability"]),
    ("complex analysis", ["Mathlib.Analysis.Complex", "Mathlib.Analysis.Analytic", "Mathlib.Analysis.Meromorphic"]),
    ("inner product spaces", ["Mathlib.Analysis.InnerProductSpace"]),
    ("Fourier analysis", ["Mathlib.Analysis.Fourier", "Mathlib.Analysis.Distribution"]),
    ("special functions", ["Mathlib.Analysis.SpecialFunctions"]),
    ("other analysis", ["Mathlib.Analysis"]),
    ("topology", ["Mathlib.Topology"]),
    ("linear algebra", ["Mathlib.LinearAlgebra"]),
    ("ring theory", ["Mathlib.RingTheory"]),
    ("field theory", ["Mathlib.FieldTheory"]),
    ("group theory", ["Mathlib.GroupTheory"]),
    ("Lie theory", ["Mathlib.Algebra.Lie"]),
    ("homological algebra", ["Mathlib.Algebra.Homology", "Mathlib.Algebra.Category"]),
    ("other algebra", ["Mathlib.Algebra"]),
    ("combinatorics", ["Mathlib.Combinatorics"]),
    ("geometry", ["Mathlib.Geometry"]),
    ("order", ["Mathlib.Order"]),
    ("data structures", ["Mathlib.Data"]),
    ("set theory and logic", ["Mathlib.SetTheory", "Mathlib.Logic", "Mathlib.ModelTheory", "Mathlib.Computability"]),
    ("dynamics", ["Mathlib.Dynamics"]),
    ("other Mathlib", ["Mathlib"]),
    ("Lean and tools", [""]),
]
PREFIXES = sorted(((p, k) for k, (_, ps) in enumerate(AREAS) for p in ps), key=lambda x: -len(x[0]))
SMALL = 20  # a statement has a small vocabulary when it needs at most this many project definitions
BASIC = {"other algebra", "order", "data structures", "set theory and logic", "other Mathlib", "Lean and tools"}


def area_of(module, cache={}):
    k = cache.get(module)
    if k is None:
        k = next(a for p, a in PREFIXES if module == p or module.startswith(p + ".") or p == "")
        cache[module] = k
    return k


@numba.njit(cache=True)
def meaning_graph(is_thm, ptr, edges, tptr, tedges):
    """The edges that a reader follows: the type of a theorem, the type and value of anything else."""
    n = len(is_thm)
    mptr = np.zeros(n + 1, np.int64)
    for i in range(n):
        mptr[i + 1] = mptr[i] + (tptr[i + 1] - tptr[i] if is_thm[i] else ptr[i + 1] - ptr[i])
    medges = np.empty(mptr[n], np.int64)
    for i in range(n):
        k = mptr[i]
        if is_thm[i]:
            for j in range(tptr[i], tptr[i + 1]):
                medges[k] = tedges[j]
                k += 1
        else:
            for j in range(ptr[i], ptr[i + 1]):
                medges[k] = edges[j]
                k += 1
    return mptr, medges


@numba.njit(cache=True)
def reverse(mptr, medges):
    """The same graph with every edge turned round."""
    n = len(mptr) - 1
    indeg = np.zeros(n + 1, np.int64)
    for j in range(len(medges)):
        indeg[medges[j] + 1] += 1
    rptr = np.cumsum(indeg)
    fill = rptr[:-1].copy()
    redges = np.empty(len(medges), np.int64)
    for i in range(n):
        for j in range(mptr[i], mptr[i + 1]):
            w = medges[j]
            redges[fill[w]] = i
            fill[w] += 1
    return rptr, redges


@numba.njit(cache=True)
def spread(rptr, redges, mask):
    """Give every constant the bits of everything that the meaning graph reaches from it."""
    n = len(rptr) - 1
    queue = np.empty(n, np.int64)
    queued = np.ones(n, np.bool_)
    for i in range(n):
        queue[i] = i
    head, tail, size = 0, 0, n
    while size > 0:
        v = queue[head]
        head = (head + 1) % n
        size -= 1
        queued[v] = False
        m = mask[v]
        for j in range(rptr[v], rptr[v + 1]):
            u = redges[j]
            if mask[u] | m != mask[u]:
                mask[u] |= m
                if not queued[u]:
                    queued[u] = True
                    queue[tail] = u
                    tail = (tail + 1) % n
                    size += 1
    return mask


@numba.njit(cache=True)
def users_of(rptr, redges, seeds):
    """The constants from which the meaning graph reaches a seed, the seeds included."""
    n = len(rptr) - 1
    hit = np.zeros(n, np.bool_)
    stack = np.empty(n, np.int64)
    sp = 0
    for s in seeds:
        if not hit[s]:
            hit[s] = True
            stack[sp] = s
            sp += 1
    while sp > 0:
        sp -= 1
        v = stack[sp]
        for j in range(rptr[v], rptr[v + 1]):
            u = redges[j]
            if not hit[u]:
                hit[u] = True
                stack[sp] = u
                sp += 1
    return hit


@numba.njit(cache=True)
def statement_masks(tptr, tedges, tmask, vmask, theorems):
    """The bits of a statement: those of its own mentions and of everything they reach."""
    out = np.zeros(len(theorems), np.uint64)
    for k in range(len(theorems)):
        t = theorems[k]
        b = tmask[t]
        for j in range(tptr[t], tptr[t + 1]):
            b |= vmask[tedges[j]]
        out[k] = b
    return out


@numba.njit(cache=True)
def vocabulary(mptr, medges, tptr, tedges, counted, starts, cap):
    """For each start, the number of counted constants that its statement reaches, up to cap."""
    n = len(mptr) - 1
    mark = np.full(n, -1, np.int64)
    stack = np.empty(n, np.int64)
    out = np.zeros(len(starts), np.int64)
    for k in range(len(starts)):
        t = starts[k]
        sp, c = 0, 0
        for j in range(tptr[t], tptr[t + 1]):
            w = tedges[j]
            if mark[w] != k:
                mark[w] = k
                stack[sp] = w
                sp += 1
        while sp > 0 and c <= cap:
            sp -= 1
            v = stack[sp]
            if counted[v]:
                c += 1
            for j in range(mptr[v], mptr[v + 1]):
                w = medges[j]
                if mark[w] != k:
                    mark[w] = k
                    stack[sp] = w
                    sp += 1
        out[k] = c
    return out


@numba.njit(cache=True)
def rests_on(ptr, edges, counted, starts, cap):
    """For each start, the number of counted constants that it reaches in the whole graph, itself
    included, up to cap. A result above cap means that the count was cut."""
    n = len(ptr) - 1
    mark = np.full(n, -1, np.int64)
    stack = np.empty(n, np.int64)
    out = np.zeros(len(starts), np.int64)
    for k in range(len(starts)):
        sp, c = 1, 0
        stack[0] = starts[k]
        mark[starts[k]] = k
        while sp > 0 and c <= cap:
            sp -= 1
            v = stack[sp]
            if counted[v]:
                c += 1
            for j in range(ptr[v], ptr[v + 1]):
                w = edges[j]
                if mark[w] != k:
                    mark[w] = k
                    stack[sp] = w
                    sp += 1
        out[k] = c
    return out


def main():
    os.makedirs(OUT, exist_ok=True)
    g = np.load(os.path.join(GRAPH, "exact_graph.npz"))
    ptr, edges, row, reached = g["ptr"], g["edges"].astype(np.int64), g["row"], g["reached"]
    n = len(row)
    names, modules, kinds = [None] * n, [None] * n, [None] * n
    with gzip.open(os.path.join(GRAPH, "exact_nodes.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for line in f:
            i, m, name, k, _, _ = line.rstrip("\n").split("\t")
            names[int(i)], modules[int(i)], kinds[int(i)] = name, m, k
    index = {name: i for i, name in enumerate(names)}
    table = []
    with gzip.open(os.path.join(GRAPH, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        col = {c: k for k, c in enumerate(next(f).rstrip("\n").split("\t"))}
        for line in f:
            p = line.rstrip("\n").split("\t")
            table.append((p[col["module"]], p[col["name"]], p[col["kind"]]))
    sys.stderr.write(f"{n:,} constants of the project\n")

    # The area of every library constant.
    lib_area = {}
    for path in sorted(glob.glob(os.path.join(GRAPH, "exact", "lib-*.tsv.gz"))):
        with gzip.open(path, "rt", encoding="utf-8") as f:
            for line in f:
                m, name, _ = line.split("\t", 2)
                if name not in index:
                    lib_area.setdefault(name, area_of(m))
    sys.stderr.write(f"{len(lib_area):,} constants of the libraries\n")

    def bits_of(refs):
        b = 0
        for r in refs:
            a = lib_area.get(r)
            if a is not None:
                b |= 1 << a
        return b

    # What the type and value of each constant mention in the libraries.
    mask = np.zeros(n, np.uint64)
    for path in sorted(glob.glob(os.path.join(GRAPH, "exact", "chunk-*.tsv.gz"))):
        with gzip.open(path, "rt", encoding="utf-8") as f:
            for line in f:
                _, name, _, refs = line.rstrip("\n").split("\t")
                if refs:
                    mask[index[name]] = bits_of(refs.split(" "))
    # What the type of each public constant mentions.
    has_type = np.zeros(n, bool)
    tmask = np.zeros(n, np.uint64)
    tlists = [None] * n
    files = sorted(glob.glob(os.path.join(GRAPH, "exact", "types-*.tsv.gz")))
    if not files:
        sys.exit("no types-*.tsv.gz found, run statement_extract.py first")
    for path in files:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            for line in f:
                _, name, _, refs = line.rstrip("\n").split("\t")
                i = index.get(name)
                if i is None:
                    continue
                has_type[i] = True
                refs = refs.split(" ") if refs else []
                tmask[i] = bits_of(refs)
                tlists[i] = [index[r] for r in refs if r in index]
    tptr = np.zeros(n + 1, np.int64)
    for i in range(n):
        tptr[i + 1] = tptr[i] + (len(tlists[i]) if tlists[i] else 0)
    tedges = np.fromiter((j for t in tlists if t for j in t), np.int64, count=int(tptr[-1]))
    del tlists
    is_thm = np.array([k == "thm" for k in kinds])
    sys.stderr.write(f"{int(has_type.sum()):,} constants with a public type, {int((is_thm & ~has_type).sum()):,} "
                     f"theorems without one\n")

    mptr, medges = meaning_graph(is_thm, ptr, edges, tptr, tedges)
    rptr, redges = reverse(mptr, medges)
    own = np.where(is_thm, tmask, mask)
    vmask = spread(rptr, redges, own.copy())

    decl = row >= 0
    is_theorem = decl & is_thm & has_type            # theorems and lemmas of the source with a public statement
    definition = decl & ~is_thm                      # definitions, structures, instances and the like
    theorems = np.flatnonzero(is_theorem)

    # 1 and 2. The vocabulary of every statement.
    cap = 1000
    vocab = vocabulary(mptr, medges, tptr, tedges, definition, theorems, cap)
    direct = tptr[theorems + 1] - tptr[theorems]
    library_only = direct == 0
    # A theorem names a proposition when its statement is one project constant and nothing else.
    names_one = (direct == 1) & (tmask[theorems] == 0)
    sys.stderr.write(f"{len(theorems):,} theorems, {int(library_only.sum()):,} with a statement in library terms only, "
                     f"{int(names_one.sum()):,} that name one proposition\n")

    # The proofs of the statements with a small vocabulary, by the number of declarations they
    # rest on. The count is raised in steps, and only the proofs above a step go on to the next.
    small = np.flatnonzero(vocab <= SMALL)
    size = np.zeros(len(small), np.int64)
    todo = np.arange(len(small))
    cut_at = 0
    for step in (100, 2000, 50000, n):
        if step == n and len(todo) > 600:
            break
        size[todo] = rests_on(ptr, edges, decl, theorems[small[todo]], step)
        todo = todo[size[todo] > step]
        cut_at = step
        sys.stderr.write(f"  step {step:,}: {len(todo):,} proofs rest on more\n")
    cut = np.zeros(len(small), bool)
    cut[todo] = True

    # Statements that Lean found equal count once.
    at = {(m, name): k for k, (m, name, _) in enumerate(table)}
    group_of = {}
    with gzip.open(os.path.join(VERIFICATION, "redundancy", "data", "same_checked.tsv.gz"), "rt", encoding="utf-8") as f:
        next(f)
        for line in f:
            group, m, name, found, _, statement = line.rstrip("\n").split("\t")
            k = at.get((m, name))
            if found == "1" and k is not None:
                group_of.setdefault(k, group + ":" + statement)

    def area_names(b):
        return [AREAS[k][0] for k in range(len(AREAS)) if int(b) >> k & 1]

    def special(b):
        return [a for a in area_names(b) if a not in BASIC]

    def entry(k):
        """The theorem at position k of `small`."""
        j = int(small[k])
        i = int(theorems[j])
        r = int(row[i])
        e = {"name": user_name(modules[i], names[i]), "module": modules[i], "kind": table[r][2],
             "used": bool(reached[i]), "vocabulary": int(vocab[j]), "rests_on": int(size[k]), "cut": bool(cut[k]),
             "areas": special(smask[j])}
        if names_one[j]:
            e["states"] = user_name(modules[int(tedges[tptr[i]])], names[int(tedges[tptr[i]])])
        return e, group_of.get(r, ("own", r))

    smask = statement_masks(tptr, tedges, tmask, vmask, theorems)
    order = np.argsort(-size)
    lists = {"library_only": [], "small_vocabulary": [], "named_propositions": []}
    seen = {k: set() for k in lists}
    distinct_library_only = set()
    with gzip.open(os.path.join(OUT, "small_vocabulary.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("module\tname\tkind\tused\tvocabulary\trests_on\tcut\tstates\tareas\n")
        for k in order.tolist():
            e, key = entry(k)
            j = int(small[k])
            f.write("\t".join([e["module"], e["name"], e["kind"], str(int(e["used"])), str(e["vocabulary"]),
                               str(e["rests_on"]), str(int(e["cut"])), e.get("states", ""), ", ".join(e["areas"])]) + "\n")
            which = "library_only" if library_only[j] else ("named_propositions" if names_one[j] else "small_vocabulary")
            if library_only[j]:
                distinct_library_only.add(key)
            if key not in seen[which] and len(lists[which]) < 150:
                seen[which].add(key)
                lists[which].append(e)
    lib_pos = np.flatnonzero(library_only[small])
    lib_nodes = theorems[library_only]

    def bins(values, edges_):
        out, lo = {}, None
        for hi in edges_:
            label = f"{hi}" if lo is None or hi == lo + 1 else f"{lo + 1} to {hi}"
            out[label] = int(((values > (lo if lo is not None else -1)) & (values <= hi)).sum())
            lo = hi
        out[f"more than {edges_[-1]}"] = int((values > edges_[-1]).sum())
        return out

    used_thm = reached[theorems]

    # 3. The areas that the statements touch.
    areas = {}
    for k, (label, _) in enumerate(AREAS):
        bit = np.uint64(1) << np.uint64(k)
        hit = (smask & bit) != 0
        direct_hit = (tmask[theorems] & bit) != 0
        areas[label] = {"statements": int(hit.sum()), "used_statements": int((hit & used_thm).sum()),
                        "named_in_the_statement_itself": int(direct_hit.sum())}
    zeta_bit = np.uint64(1) << np.uint64(0)
    char_bit = np.uint64(1) << np.uint64(1)
    zeta = (smask & zeta_bit) != 0
    chars = (smask & char_bit) != 0
    zeta_defs = definition & ((vmask & zeta_bit) != 0)
    by_library = collections.Counter(modules[int(t)].split(".")[0] for t in theorems[zeta].tolist())

    # The lines of the outline of the exact graph.
    outline = []
    path = os.path.join(VERIFICATION, "skeleton", "OUTLINE-EXACT.txt")
    if os.path.exists(path):
        import re
        pos = {int(t): k for k, t in enumerate(theorems.tolist())}
        with open(path, encoding="utf-8") as f:
            for line in f:
                m = re.match(r"\s*([\d,]+)  (\s*)(\S+)(?:\s+\[\d+ more to (\S+)\])?", line)
                if not m:
                    continue
                head = m.group(4) or m.group(3)
                i = index.get(head)
                k = pos.get(i) if i is not None else None
                outline.append({"head": head, "level": len(m.group(2)) // 2,
                                "vocabulary": int(vocab[k]) if k is not None else None,
                                "zeta_and_L_series": bool(zeta[k]) if k is not None else None,
                                "characters": bool(chars[k]) if k is not None else None,
                                "areas": special(smask[k]) if k is not None else None})

    # 4. The statements that the source labels as results from the literature.
    published = []
    path = os.path.join(VERIFICATION, "skeleton", "published.json")
    true_defs = set()
    with gzip.open(os.path.join(VERIFICATION, "redundancy", "data", "true_predicates.tsv.gz"), "rt", encoding="utf-8") as f:
        col = {c: k for k, c in enumerate(next(f).rstrip("\n").split("\t"))}
        for line in f:
            p = line.rstrip("\n").split("\t")
            i = index.get(p[col["name"]])
            if i is not None:
                true_defs.add(i)
    empty = users_of(rptr, redges, np.array(sorted(true_defs), np.int64)) if true_defs else np.zeros(n, bool)
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            pub = json.load(f)["statements"]
        ids = [index.get(s["name"]) for s in pub]
        known = [(s, i) for s, i in zip(pub, ids) if i is not None]
        starts = np.array([i for _, i in known], np.int64)
        # The vocabulary of a definition is counted from its own mentions.
        pv = vocabulary(mptr, medges, mptr, medges, definition, starts, 100000)
        proofs = [index.get(s.get("proof") or "") for s, _ in known]
        have = np.array([p for p in proofs if p is not None], np.int64)
        psize = dict(zip(have.tolist(), rests_on(ptr, edges, decl, have, n).tolist())) if len(have) else {}
        for (s, i), v, p in zip(known, pv.tolist(), proofs):
            b = vmask[i]
            published.append({"name": s["name"], "reached": bool(reached[i]), "vocabulary": int(v),
                              "library_only": bool(mptr[i + 1] == mptr[i]) or int(v) == 0,
                              "needs_an_always_true_definition": bool(empty[i]),
                              "areas": special(b), "proof": s.get("proof"),
                              "proof_rests_on": psize.get(p) if p is not None else None})

    pub_proved = [p for p in published if p["proof"] and p["reached"]]
    summary = {
        "constants": n,
        "theorems_with_a_public_statement": len(theorems),
        "theorems_of_the_source_without_one": int((decl & is_thm & ~has_type).sum()),
        "used_theorems": int(used_thm.sum()),
        "library_only": {
            "statements": int(library_only.sum()),
            "used": int((library_only & used_thm).sum()),
            "distinct_statements": len(distinct_library_only),
            "by_kind": dict(collections.Counter(table[int(row[i])][2] for i in lib_nodes.tolist()).most_common()),
            "by_library": dict(collections.Counter(modules[i].split(".")[0] for i in lib_nodes.tolist()).most_common()),
            "proof_rests_on": bins(size[lib_pos], [1, 10, 100, 1000, 10000]),
            "largest_proofs": lists["library_only"],
        },
        "small_vocabulary": {
            "at_most": SMALL,
            "statements": len(small),
            "used": int(used_thm[small].sum()),
            "proof_rests_on": bins(size, [1, 10, 100, 1000, 10000]),
            "counts_cut_at": cut_at,
            "proofs_whose_count_was_cut": int(cut.sum()),
            "largest_proofs": lists["small_vocabulary"],
        },
        "named_propositions": {
            "theorems_that_name_one": int(names_one.sum()),
            "with_a_small_vocabulary": int(names_one[small].sum()),
            "largest_proofs": lists["named_propositions"],
        },
        "vocabulary_of_a_statement": {
            "cap": cap,
            "all_theorems": bins(vocab, [0, 5, 20, 100, 1000]),
            "used_theorems": bins(vocab[used_thm], [0, 5, 20, 100, 1000]),
            "median": int(np.median(vocab)),
            "median_of_used": int(np.median(vocab[used_thm])),
        },
        "areas": areas,
        "zeta_and_L_series": {
            "statements": int(zeta.sum()),
            "used_statements": int((zeta & used_thm).sum()),
            "share_of_used_statements": round(float((zeta & used_thm).sum()) / max(1, int(used_thm.sum())), 4),
            "definitions_that_involve_them": int(zeta_defs.sum()),
            "statements_by_library": dict(by_library.most_common()),
            "characters_statements": int(chars.sum()),
            "characters_used_statements": int((chars & used_thm).sum()),
            "characters_without_zeta": int((chars & ~zeta & used_thm).sum()),
        },
        "outline": outline,
        "published": {
            "statements": len(published),
            "reached_and_proved": len(pub_proved),
            "library_only": sum(1 for p in pub_proved if p["library_only"]),
            "needing_an_always_true_definition": sum(1 for p in pub_proved if p["needs_an_always_true_definition"]),
            "vocabulary": bins(np.array([p["vocabulary"] for p in pub_proved] or [0]), [0, 5, 20, 100, 1000]),
            "list": sorted(published, key=lambda p: (p["vocabulary"], p["name"])),
        },
    }
    with open(os.path.join(HERE, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    short = {k: ({a: b for a, b in v.items() if a not in ("largest_proofs", "list")} if isinstance(v, dict) else v)
             for k, v in summary.items() if k != "outline"}
    print(json.dumps(short, indent=1, ensure_ascii=False))
    for which, found in lists.items():
        print(f"\n{which}")
        for e in found[:30]:
            print(f"{e['rests_on']:>8,}{'+' if e['cut'] else ' '} {'used' if e['used'] else '    '} v={e['vocabulary']:<3} "
                  f"{e['name']}{' : ' + e['states'] if 'states' in e else ''}  [{', '.join(e['areas'])}]")


if __name__ == "__main__":
    main()
