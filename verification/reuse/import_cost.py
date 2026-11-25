#!/usr/bin/env python3
"""Count the modules of the project that come along when one theorem of the catalogue is used.

Usage: python3 -I verification/reuse/import_cost.py

A Lean file that uses a theorem imports the module of the theorem, and Lean then loads every
module that this module imports, directly or through others. The script reads the `import`
lines of every file of `src`, follows them from the module of each statement of CATALOGUE.md
and counts the modules of the project that it reaches, the module itself left out. It counts
the same for `Main`, and writes import_cost.json next to itself. Run catalogue.py of this
folder first, since the list of statements is data/catalogue/index.json.
"""
import json
import multiprocessing
import os
import re
import statistics

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(os.path.dirname(os.path.dirname(HERE)), "src")
IMPORT = re.compile(r"^(?:(?:public|meta|private)\s+)*import\s+(?:all\s+)?(\S+)", re.MULTILINE)


def imports_of(module):
    with open(os.path.join(SRC, *module.split(".")) + ".lean", encoding="utf-8") as f:
        return module, IMPORT.findall(f.read())


def closure(imports, start):
    """The modules of the project that the imports reach from a module, the module left out."""
    seen, stack = {start}, [start]
    while stack:
        for dep in imports[stack.pop()]:
            if dep in imports and dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return len(seen) - 1


def main():
    modules = sorted(os.path.relpath(os.path.join(d, f), SRC)[:-5].replace(os.sep, ".")
                     for d, _, fs in os.walk(SRC) for f in fs if f.endswith(".lean"))
    with multiprocessing.get_context("fork").Pool() as pool:
        imports = dict(pool.imap_unordered(imports_of, modules, chunksize=500))
    with open(os.path.join(HERE, "data", "catalogue", "index.json"), encoding="utf-8") as f:
        index = json.load(f)
    cost = {m: closure(imports, m) for m in sorted({r["module"] for r in index})}
    rows = [{"number": r["number"], "name": r["name"], "module": r["module"], "rests_on": r["rests_on"],
             "imports": cost[r["module"]]} for r in index]
    counts = [r["imports"] for r in rows]
    out = {"modules_of_the_project": len(modules), "main_imports": closure(imports, "Main"),
           "median": statistics.median(counts), "smallest": min(counts), "largest": max(counts),
           "at_most_1000": sum(1 for c in counts if c <= 1000), "statements": rows}
    with open(os.path.join(HERE, "import_cost.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
    print(json.dumps({k: v for k, v in out.items() if k != "statements"}, indent=1))


if __name__ == "__main__":
    main()
