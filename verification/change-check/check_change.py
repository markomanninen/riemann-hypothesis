#!/usr/bin/env python3
"""Check what a change to the source does to the proof of the five theorems of Main.

Usage:
  python3 -I verification/change-check/check_change.py plan   [--base REV] [--what-if FILE ...]
  python3 -I verification/change-check/check_change.py build  --project DIR [--base REV | --patch FILE]
                                                             [--all | --target MODULE ...]
  python3 -I verification/change-check/check_change.py axioms --project DIR

The change is the difference between the commit REV, by default HEAD, and the working tree of
this checkout, new files included.

plan    needs no build. It lists the changed files, warns when the change touches a file that
        fixes what the five theorems state, and counts the modules that Lake has to compile
        again, from the imports in the working tree. It also names the modules that still
        import a deleted module. --what-if FILE counts as if those files changed, which
        needs no change in the checkout.

build   applies the change to DIR, a second checkout of REV in which the compiled files are
        in place, for example after `lake exe cache get`. It then runs `lake build Main`, which
        compiles the changed modules and every module between them and Main, and checks the
        axioms as `axioms` does. With --all it runs `lake build`, which also compiles the
        modules that Main does not import. --patch FILE applies a patch instead, for example
        one that `gh pr diff N > FILE` writes for a pull request. --target MODULE builds only
        the named modules and skips the axiom check.

axioms  runs `#print axioms` on the five theorems in DIR and passes when each of them rests on
        no axiom other than propext, Classical.choice and Quot.sound.

A build that passes shows that Lean's kernel accepts every changed proof. It does not show that
the five theorems state what they stated before. `plan` checks that the files which fix the
statements are unchanged, and `lake comparator`, as the README of the repository describes,
checks the statements and the axioms against Challenge.lean in full.
"""
import argparse
import collections
import os
import re
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = "src"
THEOREMS = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
            "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Files that fix what the five theorems state, or how the project is built and checked.
# The lakefile, the manifest and the toolchain pin Lean and Mathlib, whose definitions the
# statements use.
STATEMENT_FILES = {"src/Main.lean", "src/Statements.lean", "src/Challenge.lean",
                   "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
SETUP_FILES = {"comparator.json", "export-targets.txt"}
IMPORT = re.compile(r"^\s*(?:public\s+|meta\s+|private\s+)*import\s+(.+?)\s*(?:--.*)?$")


def git(*args, cwd=ROOT, check=True):
    # quotepath off keeps names such as `AdelicLattices₂` as they are, and precomposeunicode
    # makes git compare them in one Unicode form on macOS.
    out = subprocess.run(["git", "-c", "core.quotepath=off", "-c", "core.precomposeunicode=true", *args],
                         cwd=cwd, capture_output=True, text=True)
    if check and out.returncode != 0:
        sys.exit(f"git {' '.join(args)} failed in {cwd}:\n{out.stderr.strip()}")
    return out.stdout


def module_of(path):
    """src/A/B.lean is the module A.B."""
    return path[len(SRC) + 1:-len(".lean")].replace("/", ".")


def changes(base):
    """The changed paths with their kind of change, A, M, D or R, new untracked files included."""
    paths = SETUP_FILES | STATEMENT_FILES | {SRC}
    out = {}
    for line in git("diff", "--name-status", "-M", base, "--", *sorted(paths)).splitlines():
        parts = line.split("\t")
        kind = parts[0][0]
        if kind == "R":
            out[parts[1]] = "D"
            out[parts[2]] = "A"
        else:
            out[parts[1]] = kind
    for path in git("ls-files", "--others", "--exclude-standard", "--", SRC).splitlines():
        if not os.path.basename(path).startswith("._"):
            out[path] = "A"
    return out


def imports_of_tree():
    """For every module of the working tree, the modules it imports."""
    imports = {}
    for dirpath, _, files in os.walk(os.path.join(ROOT, SRC)):
        for f in files:
            # macOS writes ._ files beside each file on disks without its own metadata, such as exFAT.
            if not f.endswith(".lean") or f.startswith("._"):
                continue
            path = os.path.relpath(os.path.join(dirpath, f), ROOT)
            found, depth = [], 0
            with open(os.path.join(ROOT, path), encoding="utf-8") as fh:
                for line in fh:
                    # The imports stand before the first command, after the header and comments.
                    opened, closed = line.count("/-"), line.count("-/")
                    if depth or opened:
                        depth += opened - closed
                        continue
                    m = IMPORT.match(line)
                    if m:
                        found += m.group(1).split()
                    elif line.strip() and not line.strip().startswith(("--", "module", "prelude")):
                        break
            imports[module_of(path)] = found
    return imports


def plan(args):
    base = args.base
    if getattr(args, "what_if", None):
        changed = {}
        for p in args.what_if:
            p = os.path.relpath(os.path.abspath(p), ROOT)
            changed[p] = "M" if os.path.exists(os.path.join(ROOT, p)) else "A"
        base = "the files named with --what-if"
    else:
        changed = changes(base)
    if not changed:
        print(f"No change to the source or the build setup against {base}.")
        return 0
    start = time.time()
    imports = imports_of_tree()
    importers = collections.defaultdict(list)
    for m, deps in imports.items():
        for d in deps:
            importers[d].append(m)

    src_changed = {p: k for p, k in changed.items() if p.startswith(SRC + "/") and p.endswith(".lean")}
    seeds = [module_of(p) for p in src_changed]
    deleted = [module_of(p) for p, k in src_changed.items() if k == "D"]
    rebuild, stack = set(), [m for m in seeds if m in imports]
    rebuild.update(stack)
    while stack:
        for x in importers.get(stack.pop(), ()):
            if x not in rebuild:
                rebuild.add(x)
                stack.append(x)
    for m in deleted:
        for x in importers.get(m, ()):
            if x not in rebuild:
                rebuild.add(x)
    closure_of_main, stack = {"Main"}, ["Main"]
    while stack:
        for d in imports.get(stack.pop(), ()):
            if d in imports and d not in closure_of_main:
                closure_of_main.add(d)
                stack.append(d)

    print(f"Change against {base}, imports read in {time.time() - start:.0f} s.\n")
    kinds = {"A": "added", "M": "changed", "D": "deleted"}
    for p, k in sorted(changed.items()):
        print(f"  {kinds.get(k, k):8} {p}")
    print()
    status = 0
    touched = sorted(p for p in changed if p in STATEMENT_FILES)
    if touched:
        status = 2
        print("WARNING. The change touches " + ", ".join(touched) + ". These files fix what the five")
        print("theorems state, or the Lean and Mathlib versions that the statements use, so a passing")
        print("build no longer shows that the same claim is proved. Run lake comparator before relying")
        print("on the change. A change of the lakefile, the manifest or the toolchain can also make Lake")
        print("compile every module again.\n")
    setup = sorted(p for p in changed if p in SETUP_FILES)
    if setup:
        print("NOTE. The change touches " + ", ".join(setup) + ", which configure lake comparator.\n")
    broken = sorted({x for m in deleted for x in importers.get(m, ())})
    if broken:
        status = max(status, 1)
        print(f"ERROR. {len(broken)} modules still import a deleted module, for example {broken[0]}.\n")
    in_main = rebuild & closure_of_main
    print(f"Modules to compile again: {len(rebuild):,} of {len(imports):,}.")
    print(f"Of these, {len(in_main):,} lie below Main.lean, so `lake build Main` compiles them.")
    if rebuild and not in_main:
        print("No changed module lies below Main.lean, so the change cannot affect the five theorems.")
    by_lib = collections.Counter(m.split(".")[0] for m in rebuild)
    if by_lib:
        print("By library: " + ", ".join(f"{k} {v:,}" for k, v in by_lib.most_common()) + ".")
    return status


def run(cmd, cwd):
    print("$ " + " ".join(cmd), flush=True)
    start = time.time()
    code = subprocess.run(cmd, cwd=cwd).returncode
    print(f"({time.time() - start:.0f} s, exit {code})\n", flush=True)
    return code


def axioms(args):
    project = os.path.abspath(args.project)
    text = "import Main\n" + "".join(f"#print axioms {t}\n" for t in THEOREMS)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=tempfile.gettempdir()) as f:
        f.write(text)
        path = f.name
    start = time.time()
    out = subprocess.run(["lake", "env", "lean", path], cwd=project, capture_output=True, text=True)
    os.remove(path)
    seen = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out.stdout):
        seen[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", out.stdout):
        seen[m.group(1)] = set()
    ok = out.returncode == 0
    for t in THEOREMS:
        found = seen.get(t)
        if found is None:
            ok = False
            print(f"  {t}: no answer")
        else:
            extra = sorted(found - AXIOMS)
            ok = ok and not extra
            print(f"  {t}: " + (", ".join(sorted(found)) or "no axioms") + (f"   EXTRA {', '.join(extra)}" if extra else ""))
    if out.returncode != 0:
        print(out.stdout[-3000:] + out.stderr[-3000:])
    print(f"\nAxiom check {'passed' if ok else 'FAILED'} in {time.time() - start:.0f} s.")
    return 0 if ok else 1


def build(args):
    project = os.path.abspath(args.project)
    if git("status", "--porcelain", "--", SRC, *sorted(SETUP_FILES), cwd=project).strip():
        sys.exit(f"{project} has changes of its own in src or the build setup. Commit or remove them first.")
    if args.patch:
        # A patch, such as `gh pr diff N` writes, is applied as it is. The plan counts its files
        # with the imports of this checkout, before the patch.
        with open(args.patch, "rb") as f:
            diff = f.read()
        stat = subprocess.run(["git", "apply", "--numstat", "-z"], cwd=project, input=diff, capture_output=True)
        if stat.returncode != 0:
            sys.exit(f"{args.patch} is not a patch that git can read.")
        paths = sorted({x.split(b"\t")[-1].decode() for x in stat.stdout.split(b"\0") if b"\t" in x})
        args.what_if, untracked = [os.path.join(ROOT, p) for p in paths], []
    else:
        base = args.base
        if git("rev-parse", f"{base}:src") != git("rev-parse", "HEAD:src", cwd=project):
            sys.exit(f"{project} is not a checkout of the source of {base}. Check out the same commit there first.")
        paths = sorted(changes(base))
        diff = subprocess.run(["git", "diff", "--binary", base, "--", *paths], cwd=ROOT, capture_output=True).stdout
        untracked = [p for p in paths if p in set(git("ls-files", "--others", "--exclude-standard", "--", SRC).splitlines())]
    status = plan(args)
    if status == 1:
        sys.exit("The plan found an error, so nothing was built.")
    if diff:
        if subprocess.run(["git", "apply", "--check", "--whitespace=nowarn"], cwd=project, input=diff).returncode != 0:
            sys.exit("The change does not apply to the project checkout, so nothing was changed there.")
        subprocess.run(["git", "apply", "--whitespace=nowarn"], cwd=project, input=diff, check=True)
    for p in untracked:
        os.makedirs(os.path.dirname(os.path.join(project, p)), exist_ok=True)
        with open(os.path.join(ROOT, p), "rb") as src, open(os.path.join(project, p), "wb") as dst:
            dst.write(src.read())
    print(f"The change is applied to {project}. `git -C {project} checkout -- . && git -C {project} clean -fd src`")
    print("undoes it there, and the next build then compiles the same modules back.\n")
    targets = [] if args.all else (args.target or ["Main"])
    code = run(["lake", "build", *targets], project)
    if code != 0:
        print("The build FAILED, so at least one proof or definition no longer compiles.")
        return 1
    print("The build passed.\n")
    if args.target and not args.all:
        print("The build covered only the targets named with --target, so the axioms were not checked.")
        return 2 if status == 2 else 0
    return axioms(args) or (2 if status == 2 else 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan", help="list the change and count what has to be compiled again")
    p.add_argument("--base", default="HEAD")
    p.add_argument("--what-if", nargs="+", metavar="FILE",
                   help="count as if these files changed, without reading the working tree for changes")
    b = sub.add_parser("build", help="apply the change to a compiled checkout, build it and check the axioms")
    b.add_argument("--project", required=True)
    b.add_argument("--base", default="HEAD")
    b.add_argument("--all", action="store_true", help="build every module, not only those below Main")
    b.add_argument("--patch", metavar="FILE", help="apply this patch instead of the change in this checkout")
    b.add_argument("--target", nargs="+", metavar="MODULE", help="build only these modules instead of Main")
    a = sub.add_parser("axioms", help="check the axioms of the five theorems in a compiled checkout")
    a.add_argument("--project", required=True)
    args = ap.parse_args()
    sys.exit({"plan": plan, "build": build, "axioms": axioms}[args.command](args))


if __name__ == "__main__":
    main()
