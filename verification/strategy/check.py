#!/usr/bin/env python3
"""Check README.md of this folder against the exact graph and the source tree.

Usage: python3 -I verification/strategy/check.py [--write] [FILE]

FILE is a document of this folder, README.md when it is left out. The counts are checked for
README.md alone, and the names and the links for any document.

The script makes four checks and prints what fails.

  names   Every name in code font is looked up among the compiled constants of the project, as
          a full name or as the end of one from a dot onwards. A name that the project does not
          hold has to stand in NOT_PROJECT below with the reason. The check tells that a
          constant of that name exists. When several constants end in the name, it does not
          tell which of them the document means.
  counts  The number of declarations that each theorem of cones.json rests on is computed again
          with cone.py and compared with the stored number. The document has to show the number
          in the paragraph or table row that names the theorem.
  links   Every relative link of the document has to lead to a file or folder that exists.
  calcs   The calculations of README.md that are plain arithmetic of fractions are computed again,
          and each result has to stand in the document as the function calculations writes it.

With --write the script writes the counts of cones.json anew and makes no check. To give the
count of one more theorem in the document, add its full name to cones.json with any number and
run the script with --write.
"""
import json
import os
import re
import sys
from fractions import Fraction as Fr

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


def calculations():
    """The calculations of README.md that are plain arithmetic of fractions.

    Each entry is a description, whether the calculation holds, and the result as the document
    writes it. An exponent of x is a pair (a, b) that stands for a + b * eps.
    """
    def add(*terms):
        return (sum(t[0] for t in terms), sum(t[1] for t in terms))

    half = Fr(1, 2)
    m_low, m_high = (half, Fr(-1)), (half, half)            # RestSize and a premise of ch_core
    n_over_nT = (Fr(0), Fr(1, 8))                           # n / nT is at most 2 * x^(eps / 8)
    k_over_n2 = (half, Fr(-1))                              # k is at most n^2 * x^(1/2 - eps)
    term1 = add((Fr(1), Fr(0)), (-m_low[0], -m_low[1]))     # 2 * x / m at the lowest m
    factor3 = add((Fr(0), Fr(1)), n_over_nT)                # 2 * n * x^eps / nT
    term3 = add(m_high, factor3)                            # times the highest m
    term4 = add(k_over_n2, (Fr(0), Fr(2)), n_over_nT)       # nT2 * k * x^(2 eps) / (n^2 * nT)
    sigma = Fr(1, 20)
    out = [
        ("term 1 of the division at the lowest m", term1 == (half, Fr(1)), "2·x^(1/2 + ε)"),
        ("the factor of term 3", factor3 == (Fr(0), Fr(9, 8)), "4·m·x^(9ε/8)"),
        ("term 3 of the division at the highest m", term3 == (half, Fr(13, 8)), "4·x^(1/2 + 13ε/8)"),
        ("term 4 of the division", term4 == (half, Fr(9, 8)), "2·x^(1/2 + 9ε/8)"),
        ("the sum of the four coefficients", 2 + 2 + 4 + 2 == 10, "10·x^(1/2 + 13ε/8)"),
        ("the exponent after the division", Fr(13, 8) + 1 + Fr(3, 8) == 3, "(C + 13/8 + 1 + 3/8)"),
        ("the exponent of ch_core", Fr(13, 8) + 1 + Fr(3, 8) == 3, "1/2 + (C + 3)·ε"),
        ("the fifth term after the division by half of the ratio", 2 / half == 4, "4·x^ε/x"),
        ("the count of bad primes of the first kind", Fr(1, 4) * (half + 1) == Fr(3, 8), "U^(3/8)"),
        ("the share of the first kind", Fr(3, 8) - Fr(9, 10) == Fr(-21, 40), "U^(−21/40)"),
        ("the square of the threshold of the second kind", 2 * half == 1 and 2 ** 2 == 4, "y^(1 + 2τ)/4"),
        ("the constant of a block", 4 * 4 * 2 == 32, "(32·C₂/τ)"),
        ("the largest squarefree number", 2 * 400 == 800, "A′ = 800K"),
        ("the saving of the truncation", 400 * Fr(1, 400) == 1, "Z^(−1/400)"),
        ("the number that takes the place of eta", 5 + 1 == 6, "at most 6σ"),
        ("columns against rows", 1 / (sigma * (1 + sigma / 2)) >= 19, "at least 19 times"),
        ("columns of the maps against rows", Fr(3, 4) / (sigma * (1 + sigma / 2)) >= 14,
         "at least 14 times"),
    ]
    landau = all((1 + d / 2) * (4 * (1 + d) / d) / (4 * (1 + d) / d - 2) == 1 + d
                 for d in (half, Fr(1, 3), Fr(2), Fr(7, 5)))
    out.append(("the peak of the Landau weight at the limit of sigma", landau, "4(1 + δ)/δ"))
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
    for link in re.findall(r"\]\(([^)\s]+)\)", text):
        if re.match(r"[a-z]+://", link):
            continue
        links += 1
        if not os.path.exists(os.path.normpath(os.path.join(HERE, link.split("#")[0]))):
            print("link   %s leads nowhere" % link)
            bad += 1

    calcs = 0
    if target == "README.md":
        flat = re.sub(r"\s+", " ", text)
        for what, holds, shown in calculations():
            calcs += 1
            if not holds:
                print("calc   %s does not come out as the document says" % what)
                bad += 1
            elif shown not in flat:
                print("calc   the document does not show %s for %s" % (shown, what))
                bad += 1

    print("%d names, %d counts, %d links and %d calculations checked, %d failures"
          % (names, len(counts), links, calcs, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
