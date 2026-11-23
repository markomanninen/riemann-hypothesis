"""Find the definitions that are the proposition True on every input, and see who uses them.

Usage: python3 -I verification/redundancy/true_predicates.py

Run decl-graph/build.py first. A definition counts when its whole value is `True`, or a
function that takes any arguments and returns `True`, as in

    def anyGeometry : GeoP := fun _ _ _ => True

The script reads the source text and does not run Lean, so it misses a definition that only
reduces to True after unfolding another one.

For each such definition it lists the declarations that the declaration graph resolves as its
users, and says for each user whether the name stands in the user's statement or only in its
proof or value. It also looks in the first published source, commit 40e56bab, for definitions
of the same declared type in the same file, since such a sibling can be the condition that the
always-true definition stands in for.

It writes true-predicates.json with the counts and data/true_predicates.tsv.gz with one row per
definition.
"""
import collections, gzip, json, multiprocessing, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import scan as sc

bs = sc.bs
GRAPH = os.path.join(HERE, "..", "decl-graph", "data")
DATA = os.path.join(HERE, "data")
ORIGINAL = "40e56bab"
ALWAYS_TRUE = re.compile(r"(?:(?:fun|λ)\s+[^=]*?=>\s*)*True")
WORD = re.compile(r"[^\W\d][\w'.₀-₉]*")


def declarations(module, text=None):
    """Every named declaration of a module as (name, kind, statement, value)."""
    if text is None:
        path = os.path.join(bs.REPO, "src", *module.split(".")) + ".lean"
        with open(path, encoding="utf-8") as f:
            text = f.read()
    text = bs.COMMENT.sub("", text)
    starts = [m.start() for m in bs.COMMAND.finditer(text)] + [len(text)]
    scopes, out = [""], []
    for a, b in zip(starts, starts[1:]):
        cmd = text[a:b]
        while True:
            p = bs.PREFIX.match(cmd)
            if not p:
                break
            cmd = cmd[p.end():]
        if not cmd.strip():
            continue
        word = cmd.split(None, 1)[0]
        if word == "namespace":
            scopes.append(cmd.split()[1])
        elif word == "end":
            if len(scopes) > 1:
                scopes.pop()
        elif bs.SECTION.match(cmd):
            scopes.append("")
        else:
            m = bs.HEAD.match(cmd)
            if not m:
                continue
            kind, rest = m.group(2), cmd[m.end():]
            pr = bs.PRIORITY.match(rest)
            if pr:
                rest = rest[pr.end():]
            nm = bs.NAME.match(rest)
            if not nm or not nm.group(1):
                continue
            name, sig = nm.group(1), rest[nm.end():]
            name = name[7:] if name.startswith("_root_.") else ".".join([s for s in scopes if s] + [name])
            given, claim, body = sc.split_full(kind, sig)
            out.append((name, kind, sc.norm(given + " : " + claim), sc.norm(body)))
    return out


def find(module):
    return module, [(n, k, s) for n, k, s, v in declarations(module) if k in ("def", "abbrev") and ALWAYS_TRUE.fullmatch(v)]


def uses(job):
    """For the users in one module, say where each wanted short name stands."""
    module, wanted = job
    out = []
    for name, kind, statement, value in declarations(module):
        if name in wanted:
            for target, short in wanted[name]:
                in_statement = short in {w.rsplit(".", 1)[-1] for w in WORD.findall(statement)}
                out.append((module, name, kind, target, in_statement))
    return out


def main():
    with gzip.open(os.path.join(GRAPH, "modules.txt.gz"), "rt", encoding="utf-8") as f:
        modules = f.read().split()
    ident, row = {}, {}
    with gzip.open(os.path.join(GRAPH, "declarations.tsv.gz"), "rt", encoding="utf-8") as f:
        cols = next(f).rstrip("\n").split("\t")
        a, b = cols.index("names"), cols.index("loose+automation")
        for line in f:
            r = line.rstrip("\n").split("\t")
            ident[(r[1], r[5])] = int(r[0])
            row[int(r[0])] = (r[1], r[5], r[2], r[a] == "1", r[b] == "1")
    import numpy as np
    g = np.load(os.path.join(GRAPH, "graph.npz"))
    strict, ptr = g["strict"], g["strict_ptr"]

    found = {}
    with multiprocessing.get_context("fork").Pool() as pool:
        for module, hits in pool.imap_unordered(find, modules, chunksize=200):
            for name, kind, statement in hits:
                if (module, name) in ident:
                    found[ident[(module, name)]] = (module, name, kind, statement)
    # The users of each found definition, from the resolved name edges of the declaration graph.
    users = collections.defaultdict(list)
    for d in range(len(ptr) - 1):
        if d in row:
            for e in set(strict[ptr[d]:ptr[d + 1]].tolist()):
                if e in found and e != d:
                    users[e].append(d)
    jobs = collections.defaultdict(lambda: collections.defaultdict(list))
    for target, ds in users.items():
        for d in ds:
            m, n = row[d][0], row[d][1]
            jobs[m][n].append((target, found[target][1].rsplit(".", 1)[-1]))
    where = collections.defaultdict(list)
    with multiprocessing.get_context("fork").Pool() as pool:
        for part in pool.imap_unordered(uses, [(m, dict(w)) for m, w in jobs.items()], chunksize=50):
            for module, name, kind, target, in_statement in part:
                where[target].append((module, name, kind, in_statement))

    rows = []
    for d, (module, name, kind, statement) in sorted(found.items(), key=lambda kv: kv[1]):
        us = where.get(d, [])
        path = "src/" + module.replace(".", "/") + ".lean"
        old = subprocess.run(["git", "show", f"{ORIGINAL}:{path}"], capture_output=True, text=True, cwd=bs.REPO)
        siblings = []
        declared = statement.rsplit(" : ", 1)[-1] if " : " in statement else ""
        if old.returncode == 0 and declared:
            short = name.rsplit(".", 1)[-1]
            for n, k, s, v in declarations(module, old.stdout):
                if k in ("def", "abbrev") and n.rsplit(".", 1)[-1] != short and s.rsplit(" : ", 1)[-1] == declared \
                        and not ALWAYS_TRUE.fullmatch(v):
                    siblings.append(n.rsplit(".", 1)[-1])
        rows.append({"module": module, "name": name, "kind": kind, "statement": statement,
                     "used_by_main_names": row[d][3], "used_by_main_widest": row[d][4],
                     "users": len(us), "users_theorems": sum(k in sc.THEOREMS for _, _, k, _ in us),
                     "users_with_it_in_statement": sum(s for _, _, _, s in us),
                     "users_reached": sum(row[ident[(m, n)]][4] for m, n, _, _ in us if (m, n) in ident),
                     "siblings_in_original": siblings,
                     "example_users": [n for _, n, _, _ in us[:3]]})
    os.makedirs(DATA, exist_ok=True)
    with gzip.open(os.path.join(DATA, "true_predicates.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("module\tname\tkind\tstatement\tused_by_main_names\tused_by_main_widest\tusers\tusers_theorems\t"
                "users_with_it_in_statement\tusers_reached\tsiblings_in_original\texample_users\n")
        for r in rows:
            f.write("\t".join(str(int(v)) if isinstance(v, bool) else " ".join(v) if isinstance(v, list) else str(v)
                              for v in r.values()) + "\n")
    summary = {
        "definitions_that_are_always_true": len(rows),
        "used_by_main_names": sum(r["used_by_main_names"] for r in rows),
        "used_by_main_widest": sum(r["used_by_main_widest"] for r in rows),
        "with_no_user": sum(r["users"] == 0 for r in rows),
        "with_a_user_that_names_it_in_its_statement": sum(r["users_with_it_in_statement"] > 0 for r in rows),
        "named_only_in_proofs_or_values": sum(r["users"] > 0 and r["users_with_it_in_statement"] == 0 for r in rows),
        "with_a_sibling_of_the_same_type_in_the_original": sum(bool(r["siblings_in_original"]) for r in rows),
        "users_in_total": sum(r["users"] for r in rows),
    }
    with open(os.path.join(HERE, "true-predicates.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
