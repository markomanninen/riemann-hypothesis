"""Have Lean compare the compiled statements of the declarations that scan.py takes as the same.

Usage: python3 -I verification/redundancy/check_same.py PROJECT [--summary-only]

PROJECT is a checkout of the same source in which the compiled files are present, for example
after `lake exe cache get`. Run scan.py first. The script writes the candidates to
data/same_groups.tsv, runs CheckSame.lean on them inside PROJECT, and writes Lean's answers to
data/same_checked.tsv.gz and the counts to same-check.json.

A candidate group is a forwarding theorem with its target, a group of theorems with the same
statement text, or a group of definitions with the same text. Lean compares the compiled
statements as terms, without unfolding any definition.
"""
import collections, gzip, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")


def rows(name):
    with gzip.open(os.path.join(DATA, name), "rt", encoding="utf-8") as f:
        next(f)
        for line in f:
            yield line.rstrip("\n").split("\t")


def write_groups(path):
    """Write the candidates and return the text verdict of each forwarding pair."""
    text_same = {}
    with open(path, "w", encoding="utf-8") as f:
        for i, (m, n, tm, tn, same) in enumerate(rows("forward_pairs.tsv.gz")):
            text_same[f"F{i}"] = same == "1"
            f.write(f"F{i}\t{m}\t{n}\nF{i}\t{tm}\t{tn}\n")
        for prefix, name in (("T", "theorems_same_statement.tsv.gz"), ("D", "definitions_same_text.tsv.gz")):
            for r in rows(name):
                f.write(f"{prefix}{r[0]}\t{r[1]}\t{r[2]}\n")
    return text_same


def summarise(checked, text_same):
    groups = collections.OrderedDict()
    for line in checked:
        g, module, name, found, kind, number = line.rstrip("\n").split("\t")
        groups.setdefault(g, []).append((found == "1", int(number)))
    out = {}
    pairs = {"same_text": collections.Counter(), "other_text": collections.Counter()}
    for g, members in groups.items():
        if not g.startswith("F"):
            continue
        c = pairs["same_text" if text_same[g] else "other_text"]
        c["pairs"] += 1
        if not all(m[0] for m in members):
            c["a_constant_not_found"] += 1
        elif members[0][1] == members[1][1]:
            c["same_statement"] += 1
        else:
            c["different_statement"] += 1
    out["forward_pairs"] = {k: dict(v) for k, v in pairs.items()}
    for prefix, label in (("T", "theorems_same_statement_text"), ("D", "definitions_same_text")):
        c = collections.Counter()
        for g, members in groups.items():
            if not g.startswith(prefix):
                continue
            found = collections.Counter(m[1] for m in members if m[0])
            missing = len(members) - sum(found.values())
            c["groups"] += 1
            c["members"] += len(members)
            c["members_not_found"] += missing
            c["groups_with_one_statement"] += len(found) == 1 and not missing
            c["groups_with_several_statements"] += len(found) > 1
            c["groups_with_a_member_not_found"] += missing > 0
            c["copies_beyond_the_first_of_each_statement"] += sum(v - 1 for v in found.values())
        out[label] = dict(c)
    return out


def main():
    project = os.path.abspath(sys.argv[1])
    groups_path = os.path.join(DATA, "same_groups.tsv")
    out_path = os.path.join(DATA, "same_checked.tsv")
    text_same = write_groups(groups_path)
    if "--summary-only" not in sys.argv:
        # Lean writes its answers batch by batch. With --resume the groups that an interrupted run
        # already answered in full are kept, and only the others are sent to Lean.
        kept = []
        if "--resume" in sys.argv and os.path.exists(out_path):
            with open(out_path, encoding="utf-8") as f:
                kept = f.readlines()
            answered = collections.Counter(line.split("\t", 1)[0] for line in kept)
            with open(groups_path, encoding="utf-8") as f:
                wanted = collections.Counter(line.split("\t", 1)[0] for line in f)
            full = {g for g, n in answered.items() if wanted.get(g) == n}
            kept = [line for line in kept if line.split("\t", 1)[0] in full]
            rest_path = groups_path + ".rest"
            with open(groups_path, encoding="utf-8") as f, open(rest_path, "w", encoding="utf-8") as r:
                r.writelines(line for line in f if line.split("\t", 1)[0] not in full)
            todo, part_path = rest_path, out_path + ".part"
        else:
            todo, part_path = groups_path, out_path + ".part"
        subprocess.run(["lake", "env", "lean", "--run", os.path.join(HERE, "CheckSame.lean"), "terms",
                        os.path.join(project, ".lake", "build", "lib", "lean"), todo, part_path],
                       cwd=project, check=False)
        with open(part_path, encoding="utf-8") as f:
            kept += f.readlines()
        with open(out_path, "w", encoding="utf-8") as f:
            f.writelines(kept)
        with open(groups_path, encoding="utf-8") as f:
            total = sum(1 for _ in f)
        if len(kept) < total:
            sys.exit(f"{len(kept)} of {total} rows answered, run again with --resume")
    with open(out_path, encoding="utf-8") as f:
        checked = f.readlines()
    with gzip.open(out_path + ".gz", "wt", encoding="utf-8") as f:
        f.write("group\tmodule\tname\tfound\tkind\tstatement\n")
        f.writelines(checked)
    summary = summarise(checked, text_same)
    with open(os.path.join(HERE, "same-check.json"), "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
