#!/usr/bin/env python3
"""Build a declaration graph from the source text and bound what the target theorems use.

Usage: python3 -I verification/decl-graph/build.py

The script reads every file under src/ and does not run Lean. It finds each declaration, reads
the names its text mentions and follows them from the five theorems of Main. It writes
summary.json next to itself and the graph into data/, which git ignores.

A name in the text is followed in three ways, each wider than the one before:

  names     The name resolves, as Lean resolves it, through the namespaces and `open` lines in
            scope to a declaration of the project. A longer name may resolve by its front part,
            so `Foo.bar.symm` leads to `Foo.bar`.
  fields    Also, a name part that follows a dot, as `down` in `s.down h`, leads to every visible
            declaration `T.down` whose `T` is no declaration of the project or is itself already
            reached. Lean resolves such a part through the type of the term before the dot, and
            the text does not tell that type.
  loose     Also, a name that did not resolve leads to every visible declaration whose last part
            is that name. This covers an `open` that the script failed to track.

A declaration is visible from a module when its module is in the import closure of that module,
and a private declaration is visible only in its own module.

Automation uses declarations that the text never names: `simp` uses the lemmas tagged
`@[simp]`, and instance search uses the instances. Each way is therefore run twice, without
them and with every globally tagged declaration and global instance counted as used.
Local instances, local notation and `variable` lines count for the declarations after them in
their module in every run.
"""
import array
import collections
import gzip
import json
import multiprocessing
import os
import re
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SRC = os.path.join(REPO, "src")
DATA = os.path.join(HERE, "data")
TARGET_MODULE = "Main"

COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)
STRING = re.compile(r'"(?:\\.|[^"\\\n])*"')
COMMAND = re.compile(r"^(?=@\[|#\w|(?:import|theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque"
                     r"|axiom|example|open|end|namespace|section|variable|universe|noncomputable|private|protected"
                     r"|public|nonrec|unsafe|partial|set_option|attribute|omit|include|local|scoped|macro"
                     r"|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|elab|elab_rules|mutual"
                     r"|export|alias|initialize|run_cmd|declare_syntax_cat|add_decl_doc|suppress_compilation"
                     r"|unseal|seal|meta|module|deriving)\b)", re.M)
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
SECTION = re.compile(ATTRS + r"(?:(?:noncomputable|public|private|meta|protected)\s+)*(?:section|mutual)\b")
PREFIX = re.compile(r"(omit|include|variable|open|set_option|attribute)\b[^\n]*?\s+in\s*(?:\n|$)")
NOTATION = re.compile(r"((?:local|scoped)\s+)?(?:notation3|notation|unif_hint|infixl?|infixr|prefix|postfix|macro_rules|macro|syntax"
                      r"|elab_rules|elab)\b")
HEAD = re.compile("(" + ATTRS + r")((?:(?:private|protected|noncomputable|nonrec|unsafe|partial|public|scoped|local)\s+)*)"
                  r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom|alias)\b[ \t]*")
PRIORITY = re.compile(r"\(priority[^)]*\)\s*")
NAME = re.compile(r"((?:[^\s:({\[⦃«]|«[^»]*»)+?)(\.\{[^}]*\})?(?=[\s:({\[⦃]|$)")
IDENT = re.compile(r"\.?[^\W\d][\w'!?]*(?:\.(?:[^\W\d][\w'!?]*|\d+))*")
ATTR_ONLY = re.compile(r"(?:@\[[^\]]*\]\s*)+")
ATTR_CMD = re.compile(r"attribute\s*\[([^\]]*)\]")
ATTR_ITEM = re.compile(r"@\[([^\]]*)\]")
# Attributes that add nothing to what automation can pick up.
INERT = {"reducible", "instance_reducible", "irreducible", "semireducible", "elab_as_elim", "nolint", "inline",
         "specialize", "deprecated", "always_inline", "noinline", "macro_inline", "match_pattern", "pp_nodot",
         "pp_dot", "stacks"}
# Attributes that create declarations under derived names, such as foo_assoc and foo_apply.
GENERATING = ("reassoc", "simps", "to_additive")
SKIP = {"import", "universe", "set_option", "example", "module", "public", "meta", "suppress_compilation",
        "unseal", "seal", "add_decl_doc", "declare_syntax_cat", "include", "omit"}
THEOREMS = ("theorem", "lemma")

# Filled in the parent before the second pass and inherited by the forked workers.
PUB, NSSET, LAST, BASE, PRIV = {}, None, {}, {}, {}
# Later copies of a public name, the module index of every record, the index of every module and the import closure.
ALT, MODIDX, INDEX, CLOSURE = {}, None, {}, None


def read(module):
    path = os.path.join(SRC, *module.split(".")) + ".lean"
    with open(path, encoding="utf-8") as f:
        raw = f.read()
    return raw


def imports_of(raw):
    out = []
    for line in raw.split("\n"):
        words = line.split()
        if words[:1] == ["import"] or words[:2] in (["public", "import"], ["meta", "import"]):
            out.append(words[-1])
        elif words and words[0] not in ("prelude", "module"):
            break
    return out


def attr_class(attrs, mods, kind):
    """How automation can reach a declaration: '' not at all, 'local' in its module, 'global' anywhere."""
    names = [a.strip() for block in ATTR_ITEM.findall(attrs) for a in block.split(",") if a.strip()]
    active = [a for a in names if a.split()[0] not in INERT and not a.startswith("-")]
    if kind == "instance":
        return "local" if "local" in mods.split() else "global"
    if not active:
        return ""
    return "local" if all(a.startswith("local ") for a in active) else "global"


def parse(module):
    """The declarations and the other reference-carrying commands of one module, in order.

    Each record is (what, name, kind, private, reach, generating, prefixes, tokens). `what` is
    'decl' or 'pseudo'. `reach` says who uses the record without naming it: 'local' for the
    later declarations of the module, 'global' for automation anywhere, 'always' for a command
    that runs at build time, '' for nobody. `prefixes` are the namespaces a name is tried under.
    """
    raw = read(module)
    text = STRING.sub('""', COMMENT.sub("", raw))
    starts = [m.start() for m in COMMAND.finditer(text)] + [len(text)]
    # An attribute block on a line of its own belongs to the command on the next line.
    starts = [a for k, a in enumerate(starts) if k == 0 or not ATTR_ONLY.fullmatch(text, starts[k - 1], a)]
    scopes = [{"ns": "", "opens": [], "ctx": set()}]
    pending_opens, pending_ctx, records, unnamed = [], set(), [], 0

    def namespace():
        return ".".join(s["ns"] for s in scopes if s["ns"])

    def ns_prefixes(ns):
        parts = ns.split(".") if ns else []
        return [".".join(parts[:i]) + "." for i in range(len(parts), 0, -1)] + [""]

    def opened(names):
        out = []
        for x in names:
            for p in ns_prefixes(namespace()):
                if NSSET is None or p + x in NSSET:
                    out.append(p + x + ".")
        return out

    def open_names(cmd):
        body = re.sub(r"\([^)]*\)", " ", cmd)
        body = re.split(r"\b(?:hiding|renaming)\b", body)[0]
        return [w for w in body.split()[1:] if w not in ("scoped", "in")]

    def prefixes_for(ns):
        seen, out = set(), []
        for p in ns_prefixes(ns) + [o for s in scopes for o in s["opens"]] + pending_opens:
            if p not in seen:
                seen.add(p)
                out.append(p)
        return tuple(out)

    for a, b in zip(starts, starts[1:]):
        cmd = text[a:b]
        while True:
            p = PREFIX.match(cmd)
            if not p:
                break
            if p.group(1) == "open":
                pending_opens.extend(opened(open_names(p.group())))
            elif p.group(1) == "variable":
                pending_ctx.update(IDENT.findall(p.group()))
            elif p.group(1) == "attribute":
                pending_ctx.update(IDENT.findall(p.group())[1:])
            cmd = cmd[p.end():]
        if not cmd.strip():
            continue
        word = cmd.split(None, 1)[0]
        if word == "namespace":
            scopes.append({"ns": cmd.split()[1], "opens": [], "ctx": set()})
        elif word == "end":
            if len(scopes) > 1:
                scopes.pop()
        elif SECTION.match(cmd):
            scopes.append({"ns": "", "opens": [], "ctx": set()})
        elif word in ("open", "export"):
            scopes[-1]["opens"].extend(opened(open_names(cmd)))
        elif word == "variable":
            scopes[-1]["ctx"].update(IDENT.findall(cmd))
        elif word in SKIP:
            continue
        elif NOTATION.match(cmd):
            local = (NOTATION.match(cmd).group(1) or "").strip() == "local"
            records.append(("pseudo", "", "notation", False, "local" if local else "always", False,
                            prefixes_for(namespace()), set(IDENT.findall(cmd))))
        elif word == "attribute":
            m = ATTR_CMD.match(cmd)
            what = m.group(1).strip() if m else ""
            if what.startswith("-") or what.split()[:1] and what.split()[0] in INERT or what.startswith("local irreducible"):
                continue
            reach = "local" if what.startswith("local") else "global"
            records.append(("pseudo", "", "attribute", False, reach, False, prefixes_for(namespace()),
                            set(IDENT.findall(cmd[m.end():] if m else cmd))))
        else:
            m = HEAD.match(cmd)
            if not m:
                # A command the script does not know, such as #print, run_cmd or deriving.
                records.append(("pseudo", "", "command", False, "always", False, prefixes_for(namespace()),
                                set(IDENT.findall(cmd))))
                continue
            attrs, mods, kind = m.group(1), m.group(2), m.group(3)
            rest = cmd[m.end():]
            pr = PRIORITY.match(rest)
            if pr:
                rest = rest[pr.end():]
            nm = NAME.match(rest)
            name = nm.group(1) if nm else ""
            if name.startswith("_root_."):
                name = name[7:]
            elif name:
                name = ".".join(x for x in (namespace(), name) if x)
            else:
                unnamed += 1
                name = f"«unnamed {kind} {unnamed} of {module}»"
            ns = name.rsplit(".", 1)[0] if "." in name and not name.startswith("«") else namespace()
            tokens = set(IDENT.findall(rest[nm.end():] if nm else rest))
            for s in scopes:
                tokens |= s["ctx"]
            tokens |= pending_ctx
            records.append(("decl", name, kind, "private" in mods.split(), attr_class(attrs, mods, kind),
                            any(g in attrs for g in GENERATING), prefixes_for(ns), tokens))
            pending_opens, pending_ctx = [], set()
    return raw, records


def first_pass(module):
    raw, records = parse(module)
    return module, imports_of(raw), raw.count("\n") + (1 if raw and not raw.endswith("\n") else 0), [r[:6] for r in records]


def derived(name):
    """Shorter names that a generated name may come from: foo_assoc and foo_apply from foo, fooCpt from foo."""
    if name.endswith("Cpt"):
        yield name[:-3]
    head, _, last = name.rpartition(".")
    pieces = last.split("_")
    for i in range(len(pieces) - 1, 0, -1):
        yield (head + "." if head else "") + "_".join(pieces[:i])


def visible(n, priv, mi):
    """The declaration that the full name n means in module number mi: a private one of the module, or a
    public one whose module is in the import closure of the module."""
    i = priv.get(n)
    if i is not None:
        return i
    i = PUB.get(n)
    if i is None:
        return None
    for c in (i, *ALT.get(n, ())):
        m = int(MODIDX[c])
        if (CLOSURE[mi, m >> 3] >> (m & 7)) & 1:
            return c
    return None


def resolve(token, prefixes, priv, cache, mi):
    key = (token, prefixes)
    got = cache.get(key)
    if got is not None:
        return got
    lead = token[0] == "."
    parts = [p for p in token.split(".") if p]
    if parts[0] == "_root_":
        parts, prefixes = parts[1:], ("",)
    hits, used = [], 0
    if not lead and parts:
        for j in range(len(parts), 0, -1):
            if parts[j - 1][0].isdigit():
                continue
            tail = ".".join(parts[:j])
            for ns in prefixes:
                n = ns + tail
                i = visible(n, priv, mi)
                if i is None and j == len(parts):
                    for shorter in derived(n):
                        i = visible(shorter, priv, mi)
                        if i is not None:
                            break
                if i is not None:
                    hits.append(i)
            if hits:
                used = j
                break
    fields = [LAST[p] for p in (parts[used:] if hits or lead else parts[1:]) if p in LAST]
    heads = [LAST[parts[0]]] if not hits and not lead and parts and parts[0] in LAST else []
    got = (hits, fields, heads)
    cache[key] = got
    return got


def second_pass(module):
    """For every record of a module: the declarations its names resolve to, its field parts and its loose names."""
    _, records = parse(module)
    base, mi = BASE[module], INDEX[module]
    priv = PRIV.get(module, {})
    cache, out, ambient = {}, array.array("i"), []
    for k, (what, name, kind, private, reach, gen, prefixes, tokens) in enumerate(records):
        me = base + k
        strict, fields, heads = set(ambient), set(), set()
        for t in tokens:
            h, f, hd = resolve(t, prefixes, priv, cache, mi)
            strict.update(h)
            fields.update(f)
            heads.update(hd)
        strict.discard(me)
        for part in (strict, fields, heads):
            out.append(len(part))
            out.extend(sorted(part))
        if reach in ("local", "always") or (what == "pseudo" and kind in ("notation", "command")):
            ambient.append(me)
    return module, out.tobytes()


def topological(modules, imports):
    order, state = [], {}
    for start in modules:
        if start in state:
            continue
        stack = [(start, iter(imports[start]))]
        state[start] = 1
        while stack:
            mod, it = stack[-1]
            for dep in it:
                if dep in imports and dep not in state:
                    state[dep] = 1
                    stack.append((dep, iter(imports[dep])))
                    break
            else:
                stack.pop()
                order.append(mod)
    return order


class Graph:
    pass


def reach(g, fields, loose, automation):
    """The records reached from the targets. Returns a boolean array over all records."""
    n = len(g.module)
    seen = np.zeros(n, dtype=bool)
    stack, waiting, done_pairs = [], collections.defaultdict(list), set()

    def push(i):
        if not seen[i]:
            seen[i] = True
            stack.append(i)
            for w in waiting.pop(i, ()):
                push(w)

    for i in g.targets:
        push(i)
    for i in np.flatnonzero(g.always):
        push(int(i))
    if automation:
        for i in np.flatnonzero(g.auto):
            push(int(i))
    ncomp = len(g.by_last)

    def follow(m, comp, typed):
        key = (m * ncomp + comp) * 2 + typed
        if key in done_pairs:
            return
        done_pairs.add(key)
        cands = g.by_last[comp]
        mods = g.module[cands]
        ok = ((g.closure[m, mods >> 3] >> (mods & 7)) & 1).astype(bool)
        ok &= ~g.private[cands] | (mods == m)
        for c in cands[ok].tolist():
            if seen[c]:
                continue
            p = g.parent[c] if typed else -1
            if p < 0 or seen[p]:
                push(c)
            else:
                waiting[int(p)].append(c)

    while stack:
        d = stack.pop()
        for e in g.strict[g.strict_ptr[d]:g.strict_ptr[d + 1]].tolist():
            push(e)
        if fields:
            m = int(g.module[d])
            for c in g.fields[g.fields_ptr[d]:g.fields_ptr[d + 1]].tolist():
                follow(m, c, 1)
            if loose:
                for c in g.heads[g.heads_ptr[d]:g.heads_ptr[d + 1]].tolist():
                    follow(m, c, 0)
    return seen


def run(args):
    name, fields, loose, automation = args
    t = time.time()
    seen = reach(G, fields, loose, automation)
    sys.stderr.write(f"{name}: {int(seen[G.real].sum()):,} declarations in {time.time() - t:.0f} s\n")
    return name, np.packbits(seen)


def main():
    global PUB, NSSET, LAST, BASE, PRIV, G, MODIDX, INDEX, CLOSURE
    os.makedirs(DATA, exist_ok=True)
    t0 = time.time()
    modules = sorted(os.path.relpath(os.path.join(d, f), SRC)[:-5].replace(os.sep, ".")
                     for d, _, fs in os.walk(SRC) for f in fs if f.endswith(".lean"))
    # Challenge.lean was added by the checkers and restates the targets, so it is left out.
    modules = [m for m in modules if m != "Challenge"]
    ctx = multiprocessing.get_context("fork")
    imports, lines, recs = {}, {}, {}
    with ctx.Pool() as pool:
        for mod, imps, n, records in pool.imap_unordered(first_pass, modules, chunksize=200):
            imports[mod], lines[mod], recs[mod] = imps, n, records
    order = topological(modules, imports)
    index = {m: i for i, m in enumerate(order)}
    sys.stderr.write(f"first pass: {len(modules):,} modules in {time.time() - t0:.0f} s\n")

    names, kinds, module, private, real, auto, always, clashes = [], [], [], [], [], [], [], 0
    for m in order:
        BASE[m] = len(names)
        for what, name, kind, priv, reach_, gen in recs[m]:
            i = len(names)
            names.append(name)
            kinds.append(kind)
            module.append(index[m])
            private.append(priv)
            real.append(what == "decl")
            auto.append(reach_ == "global")
            always.append(reach_ == "always")
            if what == "decl" and not name.startswith("«"):
                if priv:
                    PRIV.setdefault(m, {})[name] = i
                elif name in PUB:
                    clashes += 1
                    ALT.setdefault(name, []).append(i)
                else:
                    PUB[name] = i
    NSSET = set()
    for name, r in zip(names, real):
        if r and not name.startswith("«"):
            parts = name.split(".")
            for k in range(1, len(parts)):
                NSSET.add(".".join(parts[:k]))
    last_of = []
    for name, r in zip(names, real):
        if r and not name.startswith("«"):
            last = name.rsplit(".", 1)[-1]
            last_of.append(LAST.setdefault(last, len(LAST)))
        else:
            last_of.append(-1)

    t2 = time.time()
    width = (len(order) + 7) // 8
    INDEX, MODIDX = index, np.array(module, dtype=np.int32)
    CLOSURE = np.zeros((len(order), width), dtype=np.uint8)
    for i, m in enumerate(order):
        row = CLOSURE[i]
        for d in imports[m]:
            if d in index:
                np.bitwise_or(row, CLOSURE[index[d]], out=row)
        row[i >> 3] |= 1 << (i & 7)
    sys.stderr.write(f"import closure in {time.time() - t2:.0f} s\n")


    t1 = time.time()
    parts = {}
    with ctx.Pool() as pool:
        for mod, blob in pool.imap_unordered(second_pass, modules, chunksize=200):
            parts[mod] = np.frombuffer(blob, dtype=np.int32)
    sys.stderr.write(f"second pass in {time.time() - t1:.0f} s\n")

    n = len(names)
    lists = ([], [], [])
    counts = (np.zeros(n, dtype=np.int64), np.zeros(n, dtype=np.int64), np.zeros(n, dtype=np.int64))
    for m in order:
        flat, pos, i = parts[m], 0, BASE[m]
        while pos < len(flat):
            for k in range(3):
                c = int(flat[pos])
                lists[k].append(flat[pos + 1:pos + 1 + c])
                counts[k][i] = c
                pos += 1 + c
            i += 1
    del parts

    g = Graph()
    g.module = np.array(module, dtype=np.int32)
    g.private = np.array(private, dtype=bool)
    g.real = np.array(real, dtype=bool)
    g.auto = np.array(auto, dtype=bool)
    g.always = np.array(always, dtype=bool)
    for k, label in enumerate(("strict", "fields", "heads")):
        setattr(g, label, np.concatenate(lists[k]) if lists[k] else np.zeros(0, dtype=np.int32))
        setattr(g, label + "_ptr", np.concatenate(([0], np.cumsum(counts[k]))))
    last_arr = np.array(last_of, dtype=np.int64)
    by = np.argsort(last_arr, kind="stable")
    by = by[last_arr[by] >= 0]
    cuts = np.searchsorted(last_arr[by], np.arange(len(LAST) + 1))
    g.by_last = [by[cuts[c]:cuts[c + 1]] for c in range(len(LAST))]
    g.parent = np.array([PUB.get(nm.rsplit(".", 1)[0], -1) if r and "." in nm and not nm.startswith("«") else -1
                         for nm, r in zip(names, real)], dtype=np.int64)
    g.targets = [BASE[TARGET_MODULE] + k for k, r in enumerate(recs[TARGET_MODULE]) if r[0] == "decl"]

    g.closure = CLOSURE

    G = g
    runs = [("names", 0, 0, 0), ("names+automation", 0, 0, 1), ("fields", 1, 0, 0),
            ("fields+automation", 1, 0, 1), ("loose", 1, 1, 0), ("loose+automation", 1, 1, 1)]
    with ctx.Pool(len(runs)) as pool:
        results = dict(pool.map(run, runs))
    seen = {k: np.unpackbits(v)[:n].astype(bool) for k, v in results.items()}

    libs = [order[i].split(".")[0] for i in range(len(order))]
    lib_of = np.array([libs[m] for m in module])
    is_thm = np.array([k in THEOREMS for k in kinds])
    summary = {
        "modules": len(order), "lines": sum(lines.values()),
        "declarations": int(g.real.sum()), "theorems": int((g.real & is_thm).sum()),
        "other_records": {k: int(c) for k, c in collections.Counter(
            kd for kd, r in zip(kinds, real) if not r).items()},
        "public_name_clashes": clashes,
        "globally_tagged_or_instance": int((g.auto & g.real).sum()),
        "targets": [names[i] for i in g.targets],
        "edges": {"names": int(len(g.strict)), "field_parts": int(len(g.fields)), "loose_names": int(len(g.heads))},
        "runs": {},
    }
    for name, _, _, _ in runs:
        s = seen[name] & g.real
        mods_hit = np.unique(g.module[s])
        summary["runs"][name] = {
            "declarations": int(s.sum()),
            "share": round(float(s.sum()) / int(g.real.sum()), 4),
            "theorems": int((s & is_thm).sum()),
            "modules_with_a_reached_declaration": int(len(mods_hit)),
            "lines_of_those_modules": int(sum(lines[order[i]] for i in mods_hit)),
            "by_library": {lib: [int((s & (lib_of == lib)).sum()), int((g.real & (lib_of == lib)).sum())]
                           for lib in sorted(set(libs))},
        }
    with open(os.path.join(HERE, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)

    level = np.zeros(n, dtype=np.int8)
    for code, name in ((6, "loose+automation"), (5, "loose"), (4, "fields+automation"), (3, "fields"),
                       (2, "names+automation"), (1, "names")):
        level[seen[name]] = code
    # The runs are not nested in one chain, so the columns are written one by one as well.
    with gzip.open(os.path.join(DATA, "declarations.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("id\tmodule\tkind\tprivate\ttagged\tname\t" + "\t".join(r[0] for r in runs) + "\n")
        cols = [seen[r[0]] for r in runs]
        for i in range(n):
            if real[i]:
                f.write(f"{i}\t{order[module[i]]}\t{kinds[i]}\t{int(private[i])}\t{int(auto[i])}\t{names[i]}\t"
                        + "\t".join(str(int(c[i])) for c in cols) + "\n")
    np.savez_compressed(os.path.join(DATA, "graph.npz"), module=g.module, private=g.private, real=g.real,
                        auto=g.auto, always=g.always, strict=g.strict, strict_ptr=g.strict_ptr, fields=g.fields,
                        fields_ptr=g.fields_ptr, heads=g.heads, heads_ptr=g.heads_ptr, parent=g.parent,
                        last=last_arr, targets=np.array(g.targets), **{"seen_" + k.replace("+", "_"): v
                                                                       for k, v in seen.items()})
    with gzip.open(os.path.join(DATA, "modules.txt.gz"), "wt", encoding="utf-8") as f:
        f.write("\n".join(order) + "\n")
    print(json.dumps(summary, indent=1, ensure_ascii=False))
    sys.stderr.write(f"total {time.time() - t0:.0f} s\n")


if __name__ == "__main__":
    main()
