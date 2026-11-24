#!/usr/bin/env python3
"""Check README.md of this folder against the exact graph and the source tree.

Usage: python3 -I verification/strategy/check.py [--write] [FILE]

FILE is a document of this folder, README.md when it is left out. The counts are checked for
README.md alone, and the names and the links for any document.

The script makes three checks and prints what fails.

  names   Every name in code font is looked up among the compiled constants of the project, as
          a full name or as the end of one from a dot onwards. A name that the project does not
          hold has to stand in NOT_PROJECT below with the reason. The check tells that a
          constant of that name exists. When several constants end in the name, it does not
          tell which of them the document means.
  counts  The number of declarations that each theorem of cones.json rests on is computed again
          with cone.py and compared with the stored number. The document has to show the number
          in the paragraph or table row that names the theorem.
  links   Every relative link of the document has to lead to a file or folder that exists.

With --write the script writes the counts of cones.json anew and makes no check. To give the
count of one more theorem in the document, add its full name to cones.json with any number and
run the script with --write.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cone  # noqa: E402

# Names in code font that are no constants of the project.
NOT_PROJECT = {
    "structure": "a Lean keyword",
    "True": "a proposition of Lean's library",
    "trivial": "a proof of Lean's library",
    "Nonempty": "a proposition of Lean's library",
    "propext": "an axiom of Lean's library",
    "Classical.choice": "an axiom of Lean's library",
    "Quot.sound": "an axiom of Lean's library",
    "src": "a folder",
    "RiemannHypothesis": "a proposition of Mathlib",
    "what₂.Word": "the type Word of the field what₂ of a datum",
    "Divisibility": "a folder of the source",
    "HarderNarasimhan": "a folder of the source",
    "MeanSquareBounds": "a folder of the source",
    "GlobalTheory.Published": "a namespace of the source",
    "R.m": "the field m of the record R of a datum",
    "div.RR": "the field RR of the record div of a datum",
    "hVC": "a hypothesis of the definition TopShapeAlt",
    "nR": "a hypothesis of the definition TopShapeAlt",
    "hX": "a premise of every_character_of_theta_integrals_local_matching",
    "hθ1": "a hypothesis of zeroFree_of_rpow_window",
    "la": "a variable of the statement FormB",
    "u": "a field of the record HCParam",
    "v": "a field of the record HCParam",
    "b": "a field of the record HCParam",
    "e": "a field of the record HCParam",
    "o": "a field of the record Level",
}
FILE_END = (".lean", ".py", ".json", ".txt", ".md", ".npz", ".gz")
IDENT = re.compile(r"^[^\W\d][\w.'!?]*$")


def blocks(text):
    """The paragraphs of the document, with every table row as a block of its own."""
    out = []
    for para in re.split(r"\n\s*\n", text):
        lines = para.split("\n")
        if all(line.lstrip().startswith("|") for line in lines if line.strip()):
            out.extend(lines)
        else:
            out.append(para)
    return out


def main():
    write = "--write" in sys.argv[1:]
    files = [a for a in sys.argv[1:] if not a.startswith("--")]
    target = files[0] if files else "README.md"
    with open(os.path.join(HERE, target), encoding="utf-8") as f:
        text = f.read()
    with open(os.path.join(HERE, "cones.json"), encoding="utf-8") as f:
        stored = json.load(f)
    g = cone.Graph()
    bad = 0

    counts = {}
    for name in stored["rests_on"] if (write or target == "README.md") else []:
        hits = g.by_name.get(name, [])
        if len(hits) != 1:
            print("cones.json  %s names %d constants" % (name, len(hits)))
            bad += 1
            continue
        counts[name] = g.rests_on(hits[0])
    if write:
        stored["rests_on"] = dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))
        with open(os.path.join(HERE, "cones.json"), "w", encoding="utf-8") as f:
            json.dump(stored, f, ensure_ascii=False, indent=1)
            f.write("\n")
        print("wrote the counts of %d theorems to cones.json" % len(counts))
        return

    prose = re.sub(r"```.*?```", "", text, flags=re.S)
    parts = blocks(prose)
    for name, n in counts.items():
        if n != stored["rests_on"][name]:
            print("count  %s rests on %s, and cones.json says %s" % (name, format(n, ","), format(stored["rests_on"][name], ",")))
            bad += 1
        shown = False
        for part in parts:
            if format(n, ",") not in part:
                continue
            for tok in re.findall(r"`([^`\n]+)`", part):
                if name == tok or name.endswith("." + tok):
                    shown = True
        if not shown:
            print("count  the document does not show %s next to %s" % (format(n, ","), name))
            bad += 1

    names = 0
    for tok in sorted(set(re.findall(r"`([^`\n]+)`", prose))):
        if not IDENT.match(tok) or tok.endswith(FILE_END) or tok in NOT_PROJECT:
            continue
        names += 1
        if not g.find(tok.replace("…", "")):
            print("name   %s is no constant of the project" % tok)
            bad += 1

    links = 0
    for target in re.findall(r"\]\(([^)\s]+)\)", text):
        if re.match(r"[a-z]+://", target):
            continue
        links += 1
        if not os.path.exists(os.path.normpath(os.path.join(HERE, target.split("#")[0]))):
            print("link   %s leads nowhere" % target)
            bad += 1

    print("%d names, %d counts and %d links checked, %d failures" % (names, len(counts), links, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
