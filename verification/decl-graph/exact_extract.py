#!/usr/bin/env python3
"""Read the exact declaration graph out of the compiled files of the whole project.

Usage: python3 -I verification/decl-graph/exact_extract.py PROJECT

PROJECT is a checkout of the same source in which the compiled files are present, for example
after `lake exe cache get`. The script takes the module list from data/modules.txt.gz, which
build.py writes, and runs ExactGraph.lean on it inside PROJECT in chunks of 10,000 modules.
Each finished chunk goes to data/exact/chunk-NNN.tsv.gz. A chunk whose file exists is skipped,
so after an interruption the same command continues from the first unfinished chunk.

One line of a chunk holds a module, a constant of that module, its kind and the names of all
constants that its type and its value mention. The constants of Mathlib and the other packages
appear only as names that are mentioned.
"""
import gzip
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
OUT = os.path.join(DATA, "exact")
CHUNK = 10_000


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    project = os.path.abspath(sys.argv[1])
    root = os.path.join(project, ".lake", "build", "lib", "lean")
    with gzip.open(os.path.join(DATA, "modules.txt.gz"), "rt", encoding="utf-8") as f:
        modules = [line.strip() for line in f if line.strip()]
    os.makedirs(OUT, exist_ok=True)
    chunks = [modules[i:i + CHUNK] for i in range(0, len(modules), CHUNK)]
    for k, part in enumerate(chunks):
        final = os.path.join(OUT, f"chunk-{k:03d}.tsv.gz")
        if os.path.exists(final):
            continue
        mods_path = os.path.join(OUT, f"chunk-{k:03d}.modules")
        raw = os.path.join(OUT, f"chunk-{k:03d}.tsv")
        with open(mods_path, "w", encoding="utf-8") as f:
            f.write("\n".join(part) + "\n")
        start = time.time()
        subprocess.run(["lake", "env", "lean", "--run", os.path.join(HERE, "ExactGraph.lean"), root, mods_path, raw],
                       cwd=project, check=True)
        seen = set()
        with open(raw, encoding="utf-8") as f:
            for line in f:
                seen.add(line.split("\t", 1)[0])
        if seen != set(part):
            # A module without constants writes no line, so only modules that are missing from
            # the chunk's list are an error.
            extra = seen - set(part)
            if extra:
                sys.exit(f"chunk {k} has lines of modules outside its list, for example {sorted(extra)[:3]}")
        tmp = final + ".part"
        with open(raw, "rb") as src, gzip.open(tmp, "wb", compresslevel=6) as dst:
            shutil.copyfileobj(src, dst)
        os.replace(tmp, final)
        os.remove(raw)
        os.remove(mods_path)
        print(f"chunk {k + 1} of {len(chunks)}: {len(part)} modules, {len(seen)} with constants, "
              f"{time.time() - start:.0f} s", flush=True)


if __name__ == "__main__":
    main()
