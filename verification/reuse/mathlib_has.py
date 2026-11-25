#!/usr/bin/env python3
"""Ask Mathlib's search and automation for statements of the project in library terms.

Usage: python3 -I verification/reuse/mathlib_has.py prepare COMPILED catalogue
       python3 -I verification/reuse/mathlib_has.py prepare COMPILED sample [N] [SEED]
       python3 -I verification/reuse/mathlib_has.py prepare COMPILED medium
       python3 -I verification/reuse/mathlib_has.py prepare PROBE control [N] [SEED]
       python3 -I verification/reuse/mathlib_has.py run PROBE SET [SHARDS]
       python3 -I verification/reuse/mathlib_has.py retry PROBE SET [SHARDS] [BEATS]
       python3 -I verification/reuse/mathlib_has.py collect SET
       python3 -I verification/reuse/mathlib_has.py names PROBE

COMPILED is a compiled checkout of this repository. PROBE is a Lake project that requires the
Mathlib revision of this repository and nothing else, with the compiled files of Mathlib in
place (`lake exe cache get`). SET is `catalogue`, `sample`, `medium` or `control`.

prepare  writes the list of a set to data/mathlib-has/SET/list.json. For the first three sets
         it copies the public compiled file of each module that holds a statement to
         data/mathlib-has/olean.
         catalogue  the 159 statements of CATALOGUE.md
         sample     N theorems drawn at random, with the seed SEED, from the theorems in
                    library terms of data/small_vocabulary.tsv.gz, one for each group of
                    statements that Lean found equal
         medium     every theorem in library terms of that file whose proof rests on 11 to
                    100 declarations, one for each group of statements that Lean found equal
         control    N modules of Mathlib drawn at random. MathlibHas.lean picks one theorem of
                    each, so the control asks the search for theorems that Mathlib holds.

run      starts SHARDS runs of MathlibHas.lean in PROBE, each on at most 150 lines of the list,
         and starts them again until every statement has an answer for every tactic. A tactic
         that was started and has no answer when its run ends is recorded as `crashed`. The
         control runs `exact?` alone.

retry    runs once more, with BEATS heartbeats in place of 400,000, every tactic whose answer
         is `limit`. The new answer replaces the old one.

collect  reads the answers and writes mathlib_has.json for the catalogue, mathlib_sample.json
         for the sample, mathlib_medium.json for the set medium or mathlib_control.json for
         the control, next to this script.

names    searches the source text of Mathlib in PROBE, comments included, for the names of
         the published results that the named theorems of the catalogue are read as, and
         writes the files that match to mathlib_names.json. The search patterns are in NAMES
         below. A match says that a file uses the words, and MATHLIB.md says what the matching
         files state.
"""
import collections
import gzip
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data", "mathlib-has")
OLEAN = os.path.join(DATA, "olean")
TACTICS = ["exact?", "simp_all", "aesop", "grind"]
BEATS = 400000
# The most lines that one Lean session gets. The memory of a session grows with every
# statement, so a long list is worked through in several rounds of fresh sessions.
CHUNK = 150
RESULT = {"catalogue": "mathlib_has.json", "sample": "mathlib_sample.json", "medium": "mathlib_medium.json",
          "control": "mathlib_control.json"}
# The published results that the check of the catalogue names for its named theorems, each with
# the numbers of the catalogue entries and a pattern for the words that a file on it would use.
NAMES = [
    ("the Kronecker-Weber theorem, global and local", [7, 8, 14], r"Kronecker.{0,3}Weber"),
    ("Stein factorisation", [9], r"Stein factori[sz]ation"),
    ("Zariski's connectedness theorem", [10, 17, 20], r"Zariski.{0,40}connected|connectedness theorem"),
    ("Borel's finiteness of class numbers", [26], r"Borel.{0,30}finiteness|class number.{0,40}algebraic group"),
    ("Landherr's classification of hermitian forms", [36], r"Landherr|[Hh]ermitian forms?.{0,60}classif"),
    ("purity of the branch locus", [45, 50, 56, 57, 65], r"purity of the branch|branch locus|Zariski.{0,3}Nagata"),
    ("Chevalley's theorem on units", [49, 54], r"Chevalley.{0,60}(unit|congruence)|congruence subgroup.{0,60}unit"),
    ("Serre's vanishing theorem", [59], r"Serre.{0,12}vanishing"),
    ("analytic normality", [62], r"analytically (normal|unramified|irreducible)|analytic normality"),
    ("the first inequality of class field theory", [78], r"(first|second|fundamental) inequality"),
    ("addition and duplication of the Weierstrass function", [95, 100], r"weierstrassP|Weierstrass.{0,3}℘"),
    ("L-functions of ideal and Hecke characters", [104, 118, 154], r"Hecke character|Gr(ö|oe)(ß|ss)en|ray class|[Ii]deal character"),
    ("the product formula", [108], r"[Pp]roduct formula"),
    ("singular moduli and complex multiplication", [126], r"singular modul|[Cc]omplex multiplication"),
    ("continuation of the Dedekind zeta function", [138, 148], r"dedekindZeta"),
    ("connectedness of a complex variety", [145], r"irreducible.{0,80}connected.{0,80}(analytic|classical|complex)"),
]


def mathlib_lib(probe):
    return os.path.join(probe, ".lake", "packages", "mathlib", ".lake", "build", "lib", "lean")


def catalogue_rows():
    with open(os.path.join(HERE, "data", "catalogue", "index.json"), encoding="utf-8") as f:
        return [{"module": r["module"], "name": r["name"], "rests_on": r["rests_on"], "used": r["used"]}
                for r in json.load(f)]


def library_rows():
    """The theorems in library terms, one for each group of statements that Lean found equal."""
    rows, groups = [], set()
    with gzip.open(os.path.join(HERE, "data", "small_vocabulary.tsv.gz"), "rt", encoding="utf-8") as f:
        col = {c: k for k, c in enumerate(next(f).rstrip("\n").split("\t"))}
        for line in f:
            p = line.rstrip("\n").split("\t")
            if p[col["library_terms"]] != "1":
                continue
            group = p[col["same_as"]]
            if group and group in groups:
                continue
            groups.add(group)
            rows.append({"module": p[col["module"]], "name": p[col["name"]],
                         "rests_on": int(p[col["rests_on"]]), "used": p[col["used"]] == "1"})
    rows.sort(key=lambda r: (r["module"], r["name"]))
    return rows


def sample_rows(n, seed):
    rows = library_rows()
    return len(rows), random.Random(seed).sample(rows, n)


def control_rows(probe, n, seed):
    lib = mathlib_lib(probe)
    modules = []
    for folder, _, files in os.walk(os.path.join(lib, "Mathlib")):
        for file in files:
            if file.endswith(".olean"):
                modules.append(os.path.relpath(os.path.join(folder, file), lib)[:-len(".olean")].replace(os.sep, "."))
    modules.sort()
    return len(modules), [{"module": m, "name": "*"} for m in random.Random(seed).sample(modules, n)]


def prepare(source, which, n=None, seed=1):
    population = None
    if which == "catalogue":
        rows = catalogue_rows()
    elif which == "sample":
        population, rows = sample_rows(n or 1000, seed)
    elif which == "medium":
        rows = [r for r in library_rows() if 11 <= r["rests_on"] <= 100]
    else:
        population, rows = control_rows(source, n or 300, seed)
    folder = os.path.join(DATA, which)
    os.makedirs(folder, exist_ok=True)
    copied = 0
    if which != "control":
        root = os.path.join(source, ".lake", "build", "lib", "lean")
        for m in sorted({r["module"] for r in rows}):
            rel = os.path.join(*m.split(".")) + ".olean"
            target = os.path.join(OLEAN, rel)
            if not os.path.exists(target):
                os.makedirs(os.path.dirname(target), exist_ok=True)
                # A copy that is cut short leaves no file under the final name.
                shutil.copyfile(os.path.join(root, rel), target + ".part")
                os.replace(target + ".part", target)
                copied += 1
    with open(os.path.join(folder, "list.json"), "w", encoding="utf-8") as f:
        json.dump({"set": which, "population": population, "seed": seed if population else None, "rows": rows}, f, indent=1)
    print(f"{len(rows)} lines in {len({r['module'] for r in rows})} modules, {copied} compiled files copied"
          + (f", drawn from {population:,}" if population else ""))


def answers(folder):
    """The latest end line for each module, name and tactic, and the tactics that were started
    and have no end line."""
    done, started = {}, set()
    for file in sorted(os.listdir(folder)):
        if not file.startswith("answers"):
            continue
        with open(os.path.join(folder, file), encoding="utf-8", errors="replace") as f:
            for line in f:
                p = line.rstrip("\n").split("\t")
                if len(p) == 4 and p[3] == "start":
                    started.add((p[0], p[1], p[2]))
                elif len(p) >= 5:
                    p += [""] * (8 - len(p))
                    key = (p[0], p[1], p[2])
                    entry = {"answer": p[3], "ms": int(p[4]), "theorems": p[5].split(), "text": p[6],
                             "beats": int(p[7] or BEATS)}
                    # A retry with more heartbeats replaces an answer, and nothing replaces a retry.
                    if key not in done or entry["beats"] >= done[key]["beats"]:
                        done[key] = entry
    return done, started - set(done)


def left(rows, done, tactics):
    modules = {key[0] for key in done}
    out = []
    for r in rows:
        if r["name"] == "*":
            if r["module"] not in modules:
                out.append((r["module"], "*", tactics))
            continue
        if (r["module"], r["name"], "*") in done:
            continue
        todo = [t for t in tactics if (r["module"], r["name"], t) not in done]
        if todo:
            out.append((r["module"], r["name"], todo))
    return out


def launch(probe, folder, root, todo, shards, beats, tag=""):
    script = os.path.join(HERE, "MathlibHas.lean")
    procs = []
    for k in range(min(shards, len(todo))):
        list_file = os.path.join(folder, f"part{tag}{k}.tsv")
        with open(list_file, "w", encoding="utf-8") as f:
            for m, name, tactics in todo[k::shards]:
                f.write(f"{m}\t{name}\t{','.join(tactics)}\n")
        env = dict(os.environ, PROBE_ROOT=root, PROBE_LIST=list_file, PROBE_BEATS=str(beats),
                   PROBE_OUT=os.path.join(folder, f"answers{tag}{k}.tsv"))
        log = open(os.path.join(folder, f"log{tag}{k}.txt"), "a", encoding="utf-8")
        procs.append(subprocess.Popen(["lake", "env", "lean", script], cwd=probe, env=env, stdout=log, stderr=log))
    return [p.wait() for p in procs]


def mark_crashed(folder, hanging):
    with open(os.path.join(folder, "answers-crashed.tsv"), "a", encoding="utf-8") as f:
        for module, name, tactic in sorted(hanging):
            f.write(f"{module}\t{name}\t{tactic}\tcrashed\t0\t\tthe run ended during this tactic\t{10 ** 9}\n")


def run(probe, which, shards=4):
    folder = os.path.join(DATA, which)
    with open(os.path.join(folder, "list.json"), encoding="utf-8") as f:
        rows = json.load(f)["rows"]
    root = mathlib_lib(probe) if which == "control" else OLEAN
    tactics = ["exact?"] if which == "control" else TACTICS
    for attempt in range(1, 200):
        done, hanging = answers(folder)
        if hanging:
            mark_crashed(folder, hanging)
            done, _ = answers(folder)
        todo = left(rows, done, tactics)
        print(f"round {attempt}: {len(todo)} lines left", flush=True)
        if not todo:
            return
        codes = launch(probe, folder, root, todo[:shards * CHUNK], shards, BEATS)
        print(f"round {attempt}: exit codes {codes}", flush=True)
        after, hanging = answers(folder)
        if len(after) == len(done) and not hanging:
            sys.exit("a round added no answer, see the log files in " + folder)


def retry(probe, which, shards=4, beats=2000000):
    folder = os.path.join(DATA, which)
    root = mathlib_lib(probe) if which == "control" else OLEAN
    done, _ = answers(folder)
    again = collections.defaultdict(list)
    for (module, name, tactic), entry in sorted(done.items()):
        if entry["answer"] == "limit" and entry["beats"] < beats:
            again[(module, name)].append(tactic)
    todo = [(m, name, tactics) for (m, name), tactics in again.items()]
    print(f"{sum(len(t) for _, _, t in todo)} tactics on {len(todo)} statements run again with {beats:,} heartbeats", flush=True)
    if todo:
        print("exit codes", launch(probe, folder, root, todo, shards, beats, tag="-retry"), flush=True)
        _, hanging = answers(folder)
        if hanging:
            mark_crashed(folder, hanging)


def wilson(k, n):
    """The 95 % interval of Wilson for a share k of n."""
    if not n:
        return [0, 0]
    z, p = 1.96, k / n
    mid, half = p + z * z / (2 * n), z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return [max(0.0, round((mid - half) / (1 + z * z / n), 4)), round((mid + half) / (1 + z * z / n), 4)]


def slim(entry):
    """An answer without the text of a failure, which is a long report of the tactic."""
    if entry and entry["answer"] != "closed":
        return {k: v for k, v in entry.items() if k not in ("text", "theorems")}
    return entry


def collect(which):
    folder = os.path.join(DATA, which)
    with open(os.path.join(folder, "list.json"), encoding="utf-8") as f:
        listed = json.load(f)
    done, hanging = answers(folder)
    head = {"set": which, "population": listed["population"], "seed": listed["seed"]}
    if which == "control":
        rows = [{"module": m, "name": name, "theorems": [], **slim(entry)}
                for (m, name, tactic), entry in sorted(done.items()) if tactic == "exact?"]
        closed = [r for r in rows if r["answer"] == "closed"]
        summary = {"modules": len(listed["rows"]),
                   "modules_without_a_theorem": sum(1 for (m, name, t) in done if name == "*"),
                   "theorems": len(rows), "closed": len(closed), "share": round(len(closed) / len(rows), 4),
                   "interval": wilson(len(closed), len(rows)),
                   "closed_with_the_theorem_itself": sum(1 for r in closed if r["name"] in r["theorems"]),
                   "answers": dict(collections.Counter(r["answer"] for r in rows))}
        out = {**head, "tactics": ["exact?"], "summary": summary, "theorems": rows}
    else:
        kinds = {}
        if which == "catalogue":
            with open(os.path.join(HERE, "catalogue.json"), encoding="utf-8") as f:
                kinds = {e["name"]: (e["number"], e["check"]["kind"], e["check"]["known_as"]) for e in json.load(f)["theorems"]}
        rows = []
        for r in listed["rows"]:
            entry = dict(r)
            if r["name"] in kinds:
                entry["number"], entry["kind"], entry["known_as"] = kinds[r["name"]]
            if (r["module"], r["name"], "*") in done:
                entry["skipped"] = done[(r["module"], r["name"], "*")]["text"]
            else:
                entry["tactics"] = {t: slim(done.get((r["module"], r["name"], t))) for t in TACTICS}
                entry["closed_by"] = [t for t in TACTICS if (entry["tactics"][t] or {}).get("answer") == "closed"]
            rows.append(entry)
        posed = [r for r in rows if "tactics" in r]
        some = sum(1 for r in posed if r["closed_by"])
        summary = {
            "statements": len(rows), "posed": len(posed), "skipped": len(rows) - len(posed),
            "closed_by_some_tactic": some, "share": round(some / len(posed), 4), "interval": wilson(some, len(posed)),
            "closed_by": {t: sum(1 for r in posed if t in r["closed_by"]) for t in TACTICS},
            "closed_by_exact_share": round(sum(1 for r in posed if "exact?" in r["closed_by"]) / len(posed), 4),
            "closed_by_exact_interval": wilson(sum(1 for r in posed if "exact?" in r["closed_by"]), len(posed)),
            "answers": {t: dict(collections.Counter((r["tactics"][t] or {"answer": "none"})["answer"] for r in posed))
                        for t in TACTICS},
            "by_rests_on": {},
        }
        for label, low, high in (("1", 1, 1), ("2 to 10", 2, 10), ("11 to 100", 11, 100), ("more than 100", 101, 10 ** 9)):
            part = [r for r in posed if low <= r["rests_on"] <= high]
            summary["by_rests_on"][label] = {"posed": len(part), "closed": sum(1 for r in part if r["closed_by"]),
                                             "closed_by_exact": sum(1 for r in part if "exact?" in r["closed_by"])}
        if kinds:
            summary["by_kind"] = {k: {"posed": sum(1 for r in posed if r["kind"] == k),
                                      "closed": sum(1 for r in posed if r["kind"] == k and r["closed_by"])}
                                  for k in ("named theorem", "standard fact", "technical step")}
        out = {**head, "tactics": TACTICS, "summary": summary, "statements": rows}
    with open(os.path.join(HERE, RESULT[which]), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
    print(json.dumps(summary, indent=1))
    if hanging:
        print(f"{len(hanging)} tactics were started and have no answer yet")


def names(probe):
    root = os.path.join(probe, ".lake", "packages", "mathlib")
    texts = {}
    for folder, _, files in os.walk(os.path.join(root, "Mathlib")):
        for file in files:
            if file.endswith(".lean"):
                path = os.path.join(folder, file)
                with open(path, encoding="utf-8") as f:
                    texts[os.path.relpath(path, root)] = f.read()
    out = []
    for result, numbers, pattern in NAMES:
        rx = re.compile(pattern)
        hits = sorted(path for path, text in texts.items() if rx.search(text))
        out.append({"result": result, "entries": numbers, "pattern": pattern, "files": hits})
        print(f"{len(hits):>3} files  {result}")
    with open(os.path.join(HERE, "mathlib_names.json"), "w", encoding="utf-8") as f:
        json.dump({"files_searched": len(texts), "results": out}, f, indent=1, ensure_ascii=False)
    print(f"{len(texts):,} files of Mathlib searched")


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) >= 3 and a[0] == "prepare" and a[2] in RESULT:
        prepare(a[1], a[2], *(int(x) for x in a[3:5]))
    elif len(a) >= 3 and a[0] == "run" and a[2] in RESULT:
        run(a[1], a[2], *(int(x) for x in a[3:4]))
    elif len(a) >= 3 and a[0] == "retry" and a[2] in RESULT:
        retry(a[1], a[2], *(int(x) for x in a[3:5]))
    elif len(a) == 2 and a[0] == "collect" and a[1] in RESULT:
        collect(a[1])
    elif len(a) == 2 and a[0] == "names":
        names(a[1])
    else:
        sys.exit(__doc__)
