#!/usr/bin/env python3
"""Build the module import graph of the submission and the part of it below a root module.

Usage: python3 -I verification/import-graph/build.py [ROOT_MODULE]

Reads only the `import` lines at the top of every file under src/ and writes its results
next to this script. The default root is the module that proves `allChi`'s statement,
`UpperTheory.FinalTheorems.everyCharacter`.
"""
import collections
import gzip
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SRC = os.path.join(REPO, "src")
ROOT = sys.argv[1] if len(sys.argv) > 1 else "Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion"
MAIN = "Main"
GROUP_DEPTH = 2  # Development.AutomorphicArithmetic, Formalism.LocalToGlobal, ...


def scan():
    imports, lines = {}, {}
    for dirpath, _, files in os.walk(SRC):
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            mod = os.path.relpath(path, SRC)[:-5].replace(os.sep, ".")
            imps, n, header = [], 0, True
            with open(path, encoding="utf-8") as f:
                for line in f:
                    n += 1
                    if header:
                        s = line.strip()
                        words = s.split()
                        if words[:1] in (["import"],) or words[:2] in (["public", "import"], ["meta", "import"]):
                            imps.append(words[-1])
                        elif s and s != "prelude" and not s.startswith("module"):
                            header = False
            imports[mod], lines[mod] = imps, n
    return imports, lines


def closure(root, imports):
    seen, stack = {root}, [root]
    while stack:
        for m in imports.get(stack.pop(), ()):
            if m in imports and m not in seen:
                seen.add(m)
                stack.append(m)
    return seen


def heights(nodes, imports):
    """Longest chain of project imports from each module down to a module that imports only outside libraries."""
    h = {}
    for start in nodes:
        if start in h:
            continue
        stack = [(start, iter(imports[start]))]
        onpath = {start}
        while stack:
            mod, it = stack[-1]
            for dep in it:
                if dep in imports and dep not in h:
                    if dep in onpath:
                        raise SystemExit(f"import cycle through {dep}")
                    onpath.add(dep)
                    stack.append((dep, iter(imports[dep])))
                    break
            else:
                stack.pop()
                onpath.discard(mod)
                h[mod] = 1 + max((h[d] for d in imports[mod] if d in imports), default=-1)
    return h


def group(mod):
    return ".".join(mod.split(".")[:GROUP_DEPTH])


def main():
    imports, lines = scan()
    if ROOT not in imports:
        raise SystemExit(f"root module {ROOT} not found")
    below_root = closure(ROOT, imports)
    below_main = closure(MAIN, imports)
    h = heights(below_main, imports)

    imported_by = collections.Counter(d for m in below_root for d in imports[m] if d in below_root)
    external = collections.Counter(d for m in below_root for d in imports[m] if d not in imports)

    with gzip.open(os.path.join(HERE, "modules.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("module\tlines\timports\timported_by_below_root\theight\tbelow_root\tbelow_main\n")
        for m in sorted(imports):
            f.write(f"{m}\t{lines[m]}\t{len(imports[m])}\t{imported_by[m]}\t{h.get(m, '')}\t"
                    f"{int(m in below_root)}\t{int(m in below_main)}\n")

    with gzip.open(os.path.join(HERE, "edges.tsv.gz"), "wt", encoding="utf-8") as f:
        f.write("importer\timported\n")
        for m in sorted(below_root):
            for d in imports[m]:
                f.write(f"{m}\t{d}\n")

    groups = collections.defaultdict(lambda: [0, 0, 0, 0])
    for m in imports:
        g = groups[group(m)]
        g[0] += 1
        g[1] += lines[m]
        if m in below_root:
            g[2] += 1
            g[3] += lines[m]
    with open(os.path.join(HERE, "groups.tsv"), "w", encoding="utf-8") as f:
        f.write("group\tfiles\tlines\tfiles_below_root\tlines_below_root\n")
        for k, (a, b, c, d) in sorted(groups.items(), key=lambda kv: -kv[1][3]):
            f.write(f"{k}\t{a}\t{b}\t{c}\t{d}\n")

    gedges = collections.Counter()
    for m in below_root:
        for d in imports[m]:
            if d in below_root and group(m) != group(d):
                gedges[(group(m), group(d))] += 1
    with open(os.path.join(HERE, "groups.dot"), "w", encoding="utf-8") as f:
        f.write("digraph imports {\n  rankdir=TB;\n  node [shape=box, fontname=Helvetica, fontsize=10];\n")
        for k, (_, _, c, d) in groups.items():
            if c:
                f.write(f'  "{k}" [label="{k}\\n{c} files, {d:,} lines"];\n')
        for (a, b), n in sorted(gedges.items()):
            f.write(f'  "{a}" -> "{b}" [label="{n}", fontsize=8];\n')
        f.write("}\n")
    if shutil.which("dot"):
        subprocess.run(["dot", "-Tsvg", "groups.dot", "-o", "groups.svg"], cwd=HERE, check=True)

    top_imported = imported_by.most_common(25)
    root_children = {d: len(closure(d, imports)) for d in imports[ROOT] if d in imports}
    summary = {
        "root": ROOT,
        "project_modules": len(imports),
        "project_lines": sum(lines.values()),
        "import_lines": sum(len(v) for v in imports.values()),
        "below_main": {"modules": len(below_main), "lines": sum(lines[m] for m in below_main)},
        "below_root": {
            "modules": len(below_root),
            "lines": sum(lines[m] for m in below_root),
            "project_edges": sum(1 for m in below_root for d in imports[m] if d in imports),
            "height_of_root": h[ROOT],
        },
        "root_imports_with_closure_size": root_children,
        "only_below_main": sorted(below_main - below_root - {MAIN}),
        "not_below_main": sorted(set(imports) - below_main),
        "external_imports": dict(external.most_common()),
        "most_imported_below_root": top_imported,
        "group_edges": len(gedges),
    }
    with open(os.path.join(HERE, "summary.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in summary.items() if k not in ("only_below_main", "not_below_main")} |
                     {"only_below_main_count": len(summary["only_below_main"]),
                      "not_below_main_count": len(summary["not_below_main"])}, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
