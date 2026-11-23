#!/usr/bin/env python3
"""Scan the source text for statements and proofs that add little: tautologies, one-step proofs,
theorems that only pass another theorem on, and statements written more than once.

Usage: python3 -I verification/redundancy/scan.py

Run verification/decl-graph/build.py first. This script reads its module list and its reach
columns, reads every source file and writes summary.json next to itself and the findings into
data/, which git ignores. It works on the text and does not run Lean.

Classes of a theorem or lemma, by its statement:

  reflexive     the claim, after its leading quantifiers and premises, is `X = X`, `X ↔ X`,
                `X ≤ X` or `X ⊆ X` with the two sides written the same
  premise       the claim's conclusion is written the same as one of its own premises
  true          the conclusion is `True`

and by its proof:

  rfl           the whole proof is `rfl`, `Iff.rfl`, `le_rfl`, `trivial` or the like
  one_tactic    the whole proof is one closing tactic without arguments, such as `by simp`
  returns_premise  the whole proof is the name of one of the theorem's premises
  forward       the whole proof is one other declaration applied to the theorem's own
                variables, so the theorem passes that declaration on under a new name

A group of duplicates is a set of declarations whose statements are the same text once
whitespace is normalised and the bound variables are numbered in order.
"""
import collections
import gzip
import hashlib
import json
import multiprocessing
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFICATION = os.path.dirname(HERE)
GRAPH = os.path.join(VERIFICATION, "decl-graph", "data")
DATA = os.path.join(HERE, "data")
sys.path.insert(0, os.path.join(VERIFICATION, "explorer"))
import build_statements as bs  # noqa: E402

THEOREMS = ("theorem", "lemma")
RFL = {"rfl", "Iff.rfl", "le_rfl", "trivial", "by rfl", "by trivial", "by exact rfl", "Eq.refl _", ".rfl",
       "le_refl _", "by exact le_rfl", "by exact Iff.rfl", "by exact trivial", "HEq.rfl", "by constructor",
       "⟨⟩", "True.intro", "by exact True.intro", "Subset.rfl", "subset_rfl", "by with_reducible rfl", "by intros; rfl",
       "by intro; rfl"}
ONE_TACTIC = re.compile(r"by (simp|norm_num|omega|decide|tauto|aesop|ring|linarith|positivity|exact\?|grind|"
                        r"simp_all|norm_cast|push_cast|field_simp|nlinarith|ring_nf|abel|group|fun_prop|"
                        r"continuity|measurability|infer_instance|assumption|contradiction|exact inferInstance)$")
IDENT = r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*"
FORWARD_HEAD = re.compile(r"(?:by\s+(?:exact|apply|refine)\s+)?@?")
FULL_IDENT = re.compile(IDENT)
# The project's own wrapper: `by first | exact @X | exact X | (intros; apply X <;> assumption)`.
FIRST = re.compile(r"by first \| exact @(\S+) \| exact \1 \| \(intros; apply \1 <;> assumption\)")
PLAIN = re.compile(r"[^\W\d][\w']*")
# Terms that start a search or a construction and name no theorem.
NOT_A_DECLARATION = {"inferInstance", "inferInstanceAs", "rfl", "trivial", "this", "absurd", "id"}
BINDER_WORDS = (" ∀ ", " ∃ ", " ∃! ", " fun ", " λ ")


def forward(body, names):
    """The declaration that a proof passes on, when the proof is that declaration applied to bound variables."""
    if len(body) > 2000:
        return ""
    m = FIRST.fullmatch(body)
    if m:
        return m.group(1)
    words = body[FORWARD_HEAD.match(body).end():].split(" ")
    head = words[0]
    if not FULL_IDENT.fullmatch(head) or head.split(".")[0] in names or head in NOT_A_DECLARATION:
        return ""
    if all(w == "_" or (w in names and PLAIN.fullmatch(w)) for w in words[1:]):
        return head
    return ""


BINDER = re.compile(r"[(\[{⦃]\s*([^:()\[\]{}⦃⦄]+?)\s*:")
RELATIONS = (" = ", " ↔ ", " ≤ ", " ⊆ ", " ≥ ", " ⊇ ")
OPENERS, CLOSERS = "([{⟨⦃", ")]}⟩⦄"


def norm(text):
    return " ".join(text.split())


def split_full(kind, sig):
    """Like build_statements.split, and also returns the text after the statement: the proof or value."""
    depth, colon, end, how = 0, -1, -1, ""
    for t in bs.TOKEN.finditer(sig):
        s = t.group()
        if s in OPENERS:
            depth += 1
        elif s in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if s == ":":
                if colon < 0:
                    colon = t.start()
            elif s == ":=":
                if bs.LET.search(sig, max(sig.rfind(";", 0, t.start()), sig.rfind("\n", 0, t.start())) + 1, t.start()):
                    continue
                end, how = t.start(), s
                break
            elif s == "where":
                end, how = t.start(), s
                break
            elif s[0] == "\n":
                if colon >= 0 and not sig[colon + 1:t.start()].strip():
                    continue
                line_end = sig.find("\n", t.end())
                line = sig[t.end():line_end if line_end >= 0 else len(sig)]
                arrow = line.find("=>")
                head = line[:arrow]
                if kind in bs.BRANCHING or (arrow >= 0 and all(head.count(o) == head.count(c)
                                                              for o, c in zip(OPENERS, CLOSERS))):
                    end, how = t.start(), "|"
                    break
    stop = end if end >= 0 else len(sig)
    given, claim = (sig[:colon], sig[colon + 1:stop]) if colon >= 0 else (sig[:stop], "")
    body = "" if end < 0 else sig[end if how == "|" else end + len(how):]
    return norm(given), norm(claim), norm(body)


def top_split(text, sep):
    """Split text at every `sep` that stands outside brackets."""
    parts, depth, last, i, n = [], 0, 0, 0, len(sep)
    while i < len(text):
        ch = text[i]
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(sep, i):
            parts.append(text[last:i])
            last = i + n
            i += n
            continue
        i += 1
    parts.append(text[last:])
    return parts


def strip_parens(text):
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        for i, ch in enumerate(text):
            depth += ch == "("
            depth -= ch == ")"
            if depth == 0 and i < len(text) - 1:
                return text
        text = text[1:-1].strip()
    return text


def top_find(text, seps):
    """The first position outside brackets where one of seps starts, or -1."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0 and ch == " " and text.startswith(seps, i):
            return i
    return -1


def conclusion(claim):
    """The premises written with arrows and the final conclusion of a claim, leading quantifiers removed.

    A quantifier reaches to the end of the claim. An arrow after a quantifier that stands inside a
    conjunction, as in `A ∧ ∀ x, B → C`, therefore belongs to that conjunct and is left in place.
    """
    premises, rest = [], claim
    while True:
        rest = rest.strip()
        if re.match(r"∀\s", rest):
            cut = top_split(rest, ", ")
            if len(cut) < 2:
                break
            premises += [strip_parens(t.split(":", 1)[1]) for t in re.findall(r"\(([^()]*:[^()]*)\)", cut[0])]
            rest = ", ".join(cut[1:])
            continue
        at = top_find(rest, BINDER_WORDS)
        head, tail = (rest[:at], rest[at:].strip()) if at >= 0 else (rest, "")
        if tail and head.rstrip().endswith("→"):
            premises += [strip_parens(p) for p in top_split(head.rstrip()[:-1].rstrip(), " → ")]
            rest = tail
            continue
        parts = top_split(head, " → ")
        if len(parts) > 1:
            premises += [strip_parens(p) for p in parts[:-1]]
            rest = (parts[-1] + " " + tail).strip()
            if tail:
                break
            continue
        break
    return premises, strip_parens(rest)


def binders(given):
    """The variable names bound in the text before the colon, and the types of the round-bracket ones."""
    names, types, depth, start = [], [], 0, -1
    for i, ch in enumerate(given):
        if ch in OPENERS:
            if depth == 0:
                start = i
            depth += 1
        elif ch in CLOSERS:
            depth = max(0, depth - 1)
            if depth == 0 and start >= 0:
                inner = given[start + 1:i]
                head, sep, typ = inner.partition(":")
                if sep and not typ.startswith("="):
                    for nm in head.split():
                        names.append(nm)
                        if given[start] == "(":
                            types.append((nm, strip_parens(typ)))
                start = -1
    return names, types


def alpha(names, text):
    """Number the bound variables in order of binding, so two statements that differ only in names agree."""
    names = [n for n in dict.fromkeys(names) if re.fullmatch(r"[^\W\d][\w']*", n)]
    if not names:
        return text
    order = {n: f"§{k}" for k, n in enumerate(names)}
    pat = re.compile(r"(?<![\w'.])(" + "|".join(re.escape(n) for n in sorted(names, key=len, reverse=True)) + r")(?![\w'])")
    return pat.sub(lambda m: order[m.group(1)], text)


def digest(text):
    return hashlib.blake2b(text.encode("utf-8"), digest_size=8).digest()


def scan(module):
    path = os.path.join(bs.REPO, "src", *module.split(".")) + ".lean"
    with open(path, encoding="utf-8") as f:
        text = bs.COMMENT.sub("", f.read())
    starts = [m.start() for m in bs.COMMAND.finditer(text)] + [len(text)]
    scopes = [{"ns": "", "lines": []}]
    pending, out = [], []
    for a, b in zip(starts, starts[1:]):
        cmd = text[a:b]
        while True:
            p = bs.PREFIX.match(cmd)
            if not p:
                break
            if p.group(1) in ("omit", "include", "variable"):
                pending.append(norm(p.group()))
            cmd = cmd[p.end():]
        if not cmd.strip():
            continue
        word = cmd.split(None, 1)[0]
        if word == "namespace":
            scopes.append({"ns": cmd.split()[1], "lines": []})
        elif word == "end":
            if len(scopes) > 1:
                scopes.pop()
        elif bs.SECTION.match(cmd):
            scopes.append({"ns": "", "lines": []})
        elif word in ("variable", "include", "omit") or bs.NOTATION.match(cmd):
            scopes[-1]["lines"].append(norm(cmd))
        else:
            m = bs.HEAD.match(cmd)
            if not m:
                continue
            kind = m.group(2)
            rest = cmd[m.end():]
            pr = bs.PRIORITY.match(rest)
            if pr:
                rest = rest[pr.end():]
            nm = bs.NAME.match(rest)
            name = nm.group(1) if nm else ""
            sig = rest[nm.end():] if nm else rest
            ctx = "\n".join([l for s in scopes for l in s["lines"]] + pending)
            pending = []
            if not name:
                continue
            if name.startswith("_root_."):
                name = name[7:]
            else:
                name = ".".join([s["ns"] for s in scopes if s["ns"]] + [name])
            given, claim, body = split_full(kind, sig)
            names, typed = binders(given)
            scope = set(names) | set(binders(ctx)[0])
            classes, target = [], ""
            if kind in THEOREMS and claim:
                premises, concl = conclusion(claim)
                premises += [t for _, t in typed]
                for rel in RELATIONS:
                    sides = top_split(concl, rel)
                    if len(sides) == 2 and strip_parens(sides[0]) == strip_parens(sides[1]) and sides[0].strip():
                        classes.append("reflexive")
                        break
                if concl in premises:
                    classes.append("premise")
                if concl == "True":
                    classes.append("true")
                if body in RFL:
                    classes.append("rfl")
                elif ONE_TACTIC.fullmatch(body):
                    classes.append("one_tactic")
                else:
                    core = re.sub(r"^by\s+(?:exact|apply)\s+", "", body)
                    if core in {n for n, _ in typed} or core in ("id", "fun h => h", "by assumption"):
                        classes.append("returns_premise")
                    else:
                        target = forward(body, scope)
                        if target:
                            classes.append("forward")
            statement = alpha(names, given + " : " + claim)
            key = digest(("T" if kind in THEOREMS else kind) + "|" + ctx + "|" + statement +
                         ("" if kind in THEOREMS else " := " + alpha(names, body)))
            out.append((name, kind, ",".join(classes), target, key, digest(body), len(body),
                        body.count(" ") + 1 if body else 0))
    return module, out


def main():
    os.makedirs(DATA, exist_ok=True)
    with gzip.open(os.path.join(GRAPH, "modules.txt.gz"), "rt", encoding="utf-8") as f:
        modules = f.read().split()
    reach, ident, decl = {}, {}, {}
    with gzip.open(os.path.join(GRAPH, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        cols = next(f).rstrip("\n").split("\t")
        a, b = cols.index("names"), cols.index("loose+automation")
        for line in f:
            r = line.rstrip("\n").split("\t")
            reach[(r[1], r[5])] = (r[a] == "1", r[b] == "1")
            ident[(r[1], r[5])] = int(r[0])
            decl[int(r[0])] = (r[1], r[5])
    import numpy as np
    graph = np.load(os.path.join(GRAPH, "graph.npz"))
    strict, ptr = graph["strict"], graph["strict_ptr"]
    rows = []
    with multiprocessing.get_context("fork").Pool() as pool:
        for module, out in pool.imap_unordered(scan, modules, chunksize=200):
            for name, kind, classes, target, key, proof, chars, words in out:
                rn, rw = reach.get((module, name), (False, False))
                rows.append((module, name, kind, classes, target, key, proof, chars, words, rn, rw))
    rows.sort(key=lambda r: (r[0], r[1]))
    last_names = collections.defaultdict(list)
    for i, r in enumerate(rows):
        last_names[r[1].rsplit(".", 1)[-1]].append(i)

    def tally(pick):
        chosen = [r for r in rows if pick(r)]
        return {"all": len(chosen), "reached_by_names": sum(r[9] for r in chosen),
                "reached_by_widest_run": sum(r[10] for r in chosen)}

    thms = [r for r in rows if r[2] in THEOREMS]
    summary = {"declarations": len(rows), "theorems": tally(lambda r: r[2] in THEOREMS), "classes": {}}
    for c in ("reflexive", "premise", "true", "rfl", "one_tactic", "returns_premise", "forward"):
        summary["classes"][c] = tally(lambda r, c=c: c in r[3].split(","))
    summary["classes"]["any_statement_class"] = tally(lambda r: any(c in r[3].split(",") for c in ("reflexive", "premise", "true")))
    summary["classes"]["any_class"] = tally(lambda r: bool(r[3]))

    # A forwarding theorem names its target. The target is a project declaration when one of the names
    # that the declaration graph resolves in the theorem, with its import and namespace rules, is the
    # target or the target without its last one or two name parts, as in `X.symm` and `X.le.trans`.
    row_of = {(r[0], r[1]): i for i, r in enumerate(rows)}
    forward_project, forward_same, pairs = [], [], []
    for i, r in enumerate(rows):
        if "forward" not in r[3].split(","):
            continue
        me = ident.get((r[0], r[1]))
        if me is None:
            continue
        used = [decl[e] for e in strict[ptr[me]:ptr[me + 1]].tolist() if e in decl]
        t = r[4][7:] if r[4].startswith("_root_.") else r[4]
        parts = t.split(".")
        for cut in range(len(parts), max(0, len(parts) - 3), -1):
            c = ".".join(parts[:cut])
            hits = [u for u in used if u[1] == c or u[1].endswith("." + c)]
            if hits:
                forward_project.append(i)
                same = [u for u in hits if u in row_of and rows[row_of[u]][5] == r[5]] if cut == len(parts) else []
                if same:
                    forward_same.append(i)
                if cut == len(parts) and r[2] in THEOREMS:
                    u = (same or hits)[0]
                    pairs.append((r[0], r[1], u[0], u[1], int(bool(same))))
                break
    fp, fs = set(forward_project), set(forward_same)
    index = {id(r): i for i, r in enumerate(rows)}
    summary["forward"] = {
        "to_a_project_declaration": tally(lambda r: index[id(r)] in fp),
        "to_a_project_declaration_with_the_same_statement": tally(lambda r: index[id(r)] in fs),
        "to_a_library_declaration": tally(lambda r: "forward" in r[3].split(",") and index[id(r)] not in fp),
    }

    def groups(pick, key):
        g = collections.defaultdict(list)
        for i, r in enumerate(rows):
            if pick(r):
                g[key(r)].append(i)
        return [v for v in g.values() if len(v) > 1]

    dup = {}
    for label, pick, key in (
            ("theorems_same_statement", lambda r: r[2] in THEOREMS, lambda r: r[5]),
            ("theorems_same_statement_and_proof", lambda r: r[2] in THEOREMS, lambda r: r[5] + r[6]),
            ("definitions_same_text", lambda r: r[2] in ("def", "abbrev"), lambda r: r[5])):
        gs = groups(pick, key)
        members = [i for g in gs for i in g]
        dup[label] = {"groups": len(gs), "declarations": len(members), "beyond_the_first_of_each_group": len(members) - len(gs),
                      "largest_group": max((len(g) for g in gs), default=0),
                      "reached_by_names": sum(rows[i][9] for i in members),
                      "reached_by_widest_run": sum(rows[i][10] for i in members),
                      "beyond_the_first_reached_by_widest_run": sum(max(0, sum(rows[i][10] for i in g) - 1) for g in gs)}
        if label != "theorems_same_statement_and_proof":
            with gzip.open(os.path.join(DATA, label + ".tsv.gz"), "wt", encoding="utf-8") as f:
                f.write("group\tmodule\tname\tsame_proof_as_first\treached_by_names\treached_by_widest_run\n")
                for k, g in enumerate(sorted(gs, key=len, reverse=True)):
                    for i in g:
                        r = rows[i]
                        f.write(f"{k}\t{r[0]}\t{r[1]}\t{int(r[6] == rows[g[0]][6])}\t{int(r[9])}\t{int(r[10])}\n")
    summary["duplicates"] = dup

    sizes = sorted(r[8] for r in thms)
    summary["proof_words"] = {"median": sizes[len(sizes) // 2], "at_most_5": sum(s <= 5 for s in sizes),
                              "at_most_20": sum(s <= 20 for s in sizes), "over_500": sum(s > 500 for s in sizes)}
    with gzip.open(os.path.join(DATA, "findings.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("module\tname\tkind\tclasses\tforward_target\tforward_to_project\tproof_words\treached_by_names\treached_by_widest_run\n")
        for i, r in enumerate(rows):
            if r[3]:
                f.write(f"{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{r[4]}\t{int(i in fp)}\t{r[8]}\t{int(r[9])}\t{int(r[10])}\n")
    with gzip.open(os.path.join(DATA, "forward_pairs.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("module\tname\ttarget_module\ttarget_name\tsame_statement_text\n")
        for row in pairs:
            f.write("\t".join(map(str, row)) + "\n")
    with open(os.path.join(HERE, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    print(json.dumps(summary, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
