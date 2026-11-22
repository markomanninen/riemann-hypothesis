"""Compare the text graph with the constants that a built sample really uses.

Usage: python3 -I verification/decl-graph/check_sample.py DEPS_TSV ROOT_MODULE

DEPS_TSV is the file that SampleDeps.lean writes when it is run in a checkout where ROOT_MODULE
has been built. Run build.py first. The script prints how many of the real dependencies each
reading of the text finds, and writes the closure figures to sample-check.json.
"""
import collections, gzip, json, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import build
HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, "data")
deps_path, root_module = sys.argv[1], sys.argv[2]
g = np.load(os.path.join(D, "graph.npz"))
real, auto, always, private, modarr = g["real"], g["auto"], g["always"], g["private"], g["module"]
with gzip.open(os.path.join(D, "modules.txt.gz"), "rt", encoding="utf-8") as f:
    order = f.read().split()
strict, sp = g["strict"], g["strict_ptr"]
fields, fp = g["fields"], g["fields_ptr"]
heads, hp = g["heads"], g["heads_ptr"]
last, parent = g["last"], g["parent"]
pub, priv, name_of, mod_of = {}, {}, {}, {}
with gzip.open(os.path.join(D, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
    next(f)
    for line in f:
        i, m, kind, p, t, name = line.rstrip("\n").split("\t")[:6]
        i = int(i); name_of[i] = name; mod_of[i] = m
        if p == "1": priv[(m, name)] = i
        else: pub.setdefault(name, i)

def to_decl(const, module):
    m = module
    if const.startswith("_private."):
        body = const[len("_private."):]
        m, _, const = body.partition(".0.")
    parts = const.split(".")
    for k in range(len(parts), 0, -1):
        n = ".".join(parts[:k])
        i = priv.get((m, n))
        if i is None: i = pub.get(n)
        if i is not None: return i
    return None

exact = collections.defaultdict(set)
sample_modules, consts, unmapped, unmapped_used = set(), 0, collections.Counter(), 0
const_mod = {}
rows = []
with open(deps_path, encoding="utf-8") as f:
    for line in f:
        m, kind, n, used = line.rstrip("\n").split("\t")
        rows.append((m, kind, n, used.split() if used else []))
        const_mod[n] = m
for m, kind, n, used in rows:
    sample_modules.add(m); consts += 1
    d = to_decl(n, m)
    if d is None:
        unmapped[kind] += 1
        continue
    for u in used:
        e = to_decl(u, const_mod.get(u, m))
        if e is None: unmapped_used += 1
        elif e != d: exact[d].add(e)
sample_ids = [i for i, m in mod_of.items() if m in sample_modules]
print("sample modules", len(sample_modules), "constants", consts, "source declarations", len(sample_ids))
print("constants without a source declaration", dict(unmapped), "uses of such constants", unmapped_used)

by_last = collections.defaultdict(list)
for i in sample_ids:
    if last[i] >= 0: by_last[int(last[i])].append(i)

def text_strict(d):
    out = set()
    for e in strict[sp[d]:sp[d + 1]].tolist():
        if real[e]: out.add(e)
        else: out.update(x for x in strict[sp[e]:sp[e + 1]].tolist() if real[x])
    out.discard(d)
    return out

tot = collections.Counter(); text_edges = 0; text_true = 0; missed = []
for d in sample_ids:
    E = exact.get(d, set()); S = text_strict(d)
    text_edges += len(S); text_true += len(S & E)
    F = None
    for e in E:
        if e in S: tot["names"] += 1; continue
        if F is None:
            F = set(); H = set()
            for c in fields[fp[d]:fp[d + 1]].tolist(): F.update(by_last.get(c, ()))
            for c in heads[hp[d]:hp[d + 1]].tolist(): H.update(by_last.get(c, ()))
        if e in F: tot["fields"] += 1
        elif e in H: tot["loose"] += 1
        elif auto[e]: tot["automation"] += 1
        else:
            tot["missed"] += 1
            if len(missed) < 4000: missed.append((name_of[d], name_of[e]))
n = sum(tot.values())
print("exact edges between source declarations", n)
for k in ("names", "fields", "loose", "automation", "missed"):
    print(f"  found by {k}: {tot[k]} ({100 * tot[k] / n:.2f} %)")
print(f"text name edges {text_edges}, of them real {text_true} ({100 * text_true / max(1, text_edges):.1f} %)")

def closure(edges_of, roots):
    seen, stack = set(roots), list(roots)
    while stack:
        for e in edges_of(stack.pop()):
            if e not in seen: seen.add(e); stack.append(e)
    return seen
roots = [i for i in sample_ids if mod_of[i] == root_module]
RE = closure(lambda d: exact.get(d, ()), roots)

# The text is followed with the rules of build.py's reach(), inside the sample: a candidate of a field
# part or a loose name counts only when its module is in the import closure of the using module, and a
# private candidate only in its own module. Records of `always` kind start reached, and so do the
# automation records in the automation runs.
project = sample_modules & set(order)
imports = {m: [d for d in build.imports_of(build.read(m)) if d in project] for m in project}
clos = {}
def closure_of(m):
    got = clos.get(m)
    if got is None:
        got = clos[m] = {m}
        for d in imports[m]: got |= closure_of(d)
    return got
sys.setrecursionlimit(100000)
sample_idx = {i for i, m in enumerate(order) if m in project}
records = [i for i in range(len(modarr)) if int(modarr[i]) in sample_idx]
sample = set(sample_ids)
def text_reach(use_fields, use_heads, automation):
    seen, stack, waiting = set(), [], collections.defaultdict(list)
    def push(i):
        if i not in seen:
            seen.add(i); stack.append(i)
            for w in waiting.pop(i, ()): push(w)
    def follow(d, c, typed):
        here = order[int(modarr[d])]
        vis = closure_of(here)
        for cand in by_last.get(c, ()):
            m = mod_of[cand]
            if m not in vis or (private[cand] and m != here): continue
            p = int(parent[cand]) if typed else -1
            if p < 0 or p in seen: push(cand)
            else: waiting[p].append(cand)
    for r in roots: push(r)
    for i in records:
        if always[i] or (automation and auto[i]): push(i)
    while stack:
        d = stack.pop()
        for e in strict[sp[d]:sp[d + 1]].tolist():
            if int(modarr[e]) in sample_idx: push(e)
        if use_fields:
            for c in fields[fp[d]:fp[d + 1]].tolist(): follow(d, c, 1)
            if use_heads:
                for c in heads[hp[d]:hp[d + 1]].tolist(): follow(d, c, 0)
    return seen & sample
out = {}
for label, a in (("names", (0, 0, 0)), ("names+automation", (0, 0, 1)), ("fields", (1, 0, 0)), ("fields+automation", (1, 0, 1)), ("loose", (1, 1, 0)), ("loose+automation", (1, 1, 1))):
    R = text_reach(*a)
    out[label] = {"text": len(R), "exact": len(RE), "exact_missing_from_text": len(RE - R), "text_beyond_exact": len(R - RE)}
    print(label, out[label])
    if label == "loose+automation":
        print("still missing:", [name_of[i] for i in list(RE - R)[:30]])
json.dump({"root_module": root_module, "sample_modules": len(sample_modules), "source_declarations": len(sample_ids),
           "exact_closure": len(RE), "exact_edges": n, "edges_found_by": dict(tot), "text_name_edges": text_edges, "text_name_edges_real": text_true,
           "closures": out}, open(os.path.join(HERE, "sample-check.json"), "w"), indent=1)
