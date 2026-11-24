#!/usr/bin/env python3
"""List the axioms that the five theorems of Main rest on, with a path to each, from the compiled files.

Usage: python3 -I verification/decl-graph/exact_axioms.py PROJECT [NAME ...]

PROJECT is the checkout that exact_extract.py read. The project's own constants come from the
chunks in data/exact. This script also reads, with ExactGraph.lean, every compiled module of the
packages under PROJECT/.lake/packages and of Lean's own library in the toolchain, and writes
them to data/exact/lib-NAME.tsv.gz. A library file that exists is not read again.

It then follows every mention from the five theorems of Main through the project and the
libraries, and from an inductive type to its constructors, as Lean's `#print axioms` does, and lists each reached constant of kind axiom with
one shortest chain of mentions that leads to it. The result goes to exact-axioms.json.

With one or more NAMEs after PROJECT the script makes the same search from each named constant
alone, prints the axioms that it reaches and leaves exact-axioms.json as it is.

The search reads what the compiled terms mention. It does not check any proof.
"""
import collections
import glob
import gzip
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "data", "exact")
TARGETS = ["LFunction_ne_zero_of_half_lt_re", "riemannHypothesis", "riemannZeta_eq_zero_re",
           "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]


def modules_under(root):
    mods = []
    for dirpath, _, files in os.walk(root):
        for f in files:
            if f.endswith(".olean"):
                rel = os.path.relpath(os.path.join(dirpath, f), root)[:-len(".olean")]
                mods.append(rel.replace(os.sep, "."))
    return sorted(mods)


def extract(project, name, root):
    final = os.path.join(OUT, f"lib-{name}.tsv.gz")
    if os.path.exists(final):
        return final
    mods = modules_under(root)
    mods_path = os.path.join(OUT, f"lib-{name}.modules")
    raw = os.path.join(OUT, f"lib-{name}.tsv")
    with open(mods_path, "w", encoding="utf-8") as f:
        f.write("\n".join(mods) + "\n")
    subprocess.run(["lake", "env", "lean", "--run", os.path.join(HERE, "ExactGraph.lean"), root, mods_path, raw],
                   cwd=project, check=True)
    with open(raw, "rb") as src, gzip.open(final + ".part", "wb", compresslevel=6) as dst:
        shutil.copyfileobj(src, dst)
    os.replace(final + ".part", final)
    os.remove(raw)
    os.remove(mods_path)
    print(f"{name}: {len(mods)} modules", flush=True)
    return final


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    project = os.path.abspath(sys.argv[1])
    sysroot = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=project, check=True,
                             capture_output=True, text=True).stdout.strip()
    libraries = {"lean": os.path.join(sysroot, "lib", "lean")}
    for pkg in sorted(glob.glob(os.path.join(project, ".lake", "packages", "*"))):
        libraries[os.path.basename(pkg)] = os.path.join(pkg, ".lake", "build", "lib", "lean")
    files = sorted(glob.glob(os.path.join(OUT, "chunk-*.tsv.gz")))
    for name, root in libraries.items():
        files.append(extract(project, name, root))

    refs, kind, module = {}, {}, {}
    for path in files:
        with gzip.open(path, "rt", encoding="utf-8") as f:
            for line in f:
                m, n, k, r = line.rstrip("\n").split("\t")
                # A name compiled in two places keeps its first entry, the project's.
                if n not in refs:
                    refs[n], kind[n], module[n] = r, k, m

    # An inductive type leads to its constructors, as in Lean's `#print axioms`.
    ctors = {}
    for c, k in kind.items():
        if k == "ctor":
            owner = c.rsplit(".", 1)[0]
            if kind.get(owner) == "ind":
                ctors.setdefault(owner, []).append(c)

    def search(roots):
        parent = {t: None for t in roots}
        queue = collections.deque(roots)
        missing = set()
        while queue:
            n = queue.popleft()
            r = refs.get(n)
            if r is None:
                missing.add(n)
                continue
            for x in (r.split(" ") if r else []) + ctors.get(n, []):
                if x not in parent:
                    parent[x] = n
                    queue.append(x)
        return parent, missing

    if len(sys.argv) > 2:
        for name in sys.argv[2:]:
            if name not in refs:
                print(f"{name}: no compiled constant of this name")
                continue
            parent, missing = search([name])
            found = sorted(n for n in parent if kind.get(n) == "axiom")
            print(f"{name}: {len(parent):,} constants reached, {len(missing)} without a compiled entry, "
                  f"axioms {', '.join(found) or 'none'}")
        return
    parent, missing = search(TARGETS)

    def chain(n):
        out = []
        while n is not None:
            out.append(n)
            n = parent[n]
        return out[::-1]

    axioms = sorted(n for n in parent if kind.get(n) == "axiom")
    summary = {
        "libraries": {name: root for name, root in libraries.items()},
        "constants_read": len(refs),
        "constants_reached": len(parent),
        "reached_names_without_a_compiled_entry": sorted(missing),
        "axioms": {a: {"module": module[a], "chain": chain(a)} for a in axioms},
    }
    with open(os.path.join(HERE, "exact-axioms.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "libraries"}, indent=1)[:6000])


if __name__ == "__main__":
    main()
