#!/usr/bin/env python3
"""Collect the units whose novelty is to be judged, and split them into batches.

Usage: python3 -I verification/novelty/units.py

A unit is one statement about the proof that a reader can compare with the literature. The
script takes two kinds of units.

  claims    the rows of the tables of verification/strategy/CLAIMS.md, each with its number,
            what the Lean text states and the declarations that state it
  timeline  the 20 entries of the timeline in the author's note, https://alpo.ge/remark.pdf,
            each with its number, its date and a paraphrase written for this script

It writes units.json next to itself, with the units in batches. A batch holds the rows of one
step of CLAIMS.md or ten entries of the timeline.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
CLAIMS = os.path.join(os.path.dirname(HERE), "strategy", "CLAIMS.md")

# The entries of the timeline on pages 3 and 4 of the note, paraphrased. The dates are those of
# the note, written as month/day/year there.
TIMELINE = [
    ("2026-10-06", "A determinant in the manner of Stepanov."),
    ("2026-10-09", "On a curve with complex multiplication by a field K and a prime p inert in K, the p-th power "
                   "of the invariant derivation vanishes modulo p, and the a-th derivative of a theta value at 0, "
                   "divided by the a-th power of a period, is divisible by p to a power of about a/p + a/p^3."),
    ("2026-10-19", "An identity q·N = M^k + R for an exponential sum over a quadric of path shape, "
                   "x1·x2 + … + x(k−1)·xk, where the sign of one side gives a proof of the Weil and Deligne bound "
                   "from signs alone, and the wish that N be automorphic through a theta function on a sixfold "
                   "cover of GL5."),
    ("2026-10-06", "Positivity of the Weil functional W on the indicator of a set S, obtained from a "
                   "determinant and read as Stepanov's argument with multiplicity one, with a bootstrap."),
    ("2026-10-20", "The switch to the smoothed von Mangoldt sum, the sum of Λ(n)·(X/n − 1) over n ≤ X with "
                   "the main terms X·log X − (1 + γ)·X subtracted, the sign in the explicit formula of Guinand "
                   "and Weil, and a variance trick with a test function."),
    ("2026-10-08", "Positivity of W on the indicator of (0, 1] plus about X^η times the indicator of (0, 1/X] "
                   "gives zero-freeness to the right of 1 − η."),
    ("2026-10-14", "Determinants for values of W that contain periods of Gan, Gross and Prasad, whose "
                   "values 0 and 1 correspond to interlacing weights, or up to m weights that do not interlace."),
    ("2026-11-15", "Iterated theta lifts U(X0) → U(X1) → … → U(Xm) between totally definite unitary groups, "
                   "each adding a block μ_j[t] to the representation, which win multiplicity m, with m about √X."),
    ("2026-11-15", "The norms and the level of the lifts, and the cancellation of the terms of order m, with a "
                   "divisibility proved through the Chowla-Selberg formula, the Weyl dimension formula and the "
                   "Siegel mass formula."),
    ("2026-11-15", "A sufficient lower bound for the divisibility of the m-fold iterated lift."),
    ("2026-10-06", "An Iwasawa tower, by analogy with a pigeonhole argument on the extension F_(q^n) over F_q."),
    ("2026-11-15", "A seesaw identity in the manner of Rallis. The period of the iterated lift is a Bessel "
                   "period that does not depend on the Hecke characters."),
    ("2026-10-06", "The slope inequality of Bost."),
    ("2026-11-15", "The exact cost of each lift, which shows that the method alone would stop at the exponent "
                   "2/3, and the need for a main term and for a division."),
    ("2026-11-15", "An integral structure glued together across Hecke characters, which acts as a greatest "
                   "common divisor and gives an extra averaging."),
    ("2026-10-14", "A relative trace formula, reduced by the Cauchy-Schwarz inequality to a bound on the norm "
                   "of a projected Poincaré series, and approximate orthogonality of the columns of the "
                   "integral structure."),
    ("2026-11-15", "For the classes in H^1(o_E[1/ℓ], Q_ℓ/Z_ℓ(−e)) that twisting does not remove, a "
                   "substantial weakening of the Vandiver conjecture."),
    ("2026-11-15", "The computation of covolumes, of the index of theta series, and of congruences between "
                   "lifts and forms."),
    ("2026-10-19", "The exact choice of the Iwasawa tower, which uses a result of Behrend."),
    ("2026-11-16", "The conclusion, the generalized Riemann hypothesis."),
]


def claims():
    batches, step = [], None
    with open(CLAIMS, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"## (Step \d+, .+|The supply of the premises)\s*$", line)
            if m:
                step = {"title": m.group(1), "units": []}
                batches.append(step)
                continue
            if line.startswith("## "):
                step = None
                continue
            m = re.match(r"\| (\d+\.\d+) \| (.+?) \| (.+?) \| (.+?) \| (.+?) \|\s*$", line)
            if m and step is not None:
                step["units"].append({"id": m.group(1), "kind": "claim", "states": m.group(2),
                                      "declarations": re.findall(r"`([^`]+)`", m.group(3)), "read": m.group(4)})
    return [b for b in batches if b["units"]]


def main():
    batches = []
    for k, b in enumerate(claims(), 1):
        batches.append({"batch": f"claims{k:02d}", "title": b["title"], "units": b["units"]})
    entries = [{"id": f"T{k}", "kind": "timeline", "date": date, "paraphrase": text}
               for k, (date, text) in enumerate(TIMELINE, 1)]
    batches.append({"batch": "timeline01", "title": "Entries 1 to 10 of the timeline of the note", "units": entries[:10]})
    batches.append({"batch": "timeline02", "title": "Entries 11 to 20 of the timeline of the note", "units": entries[10:]})
    with open(os.path.join(HERE, "units.json"), "w", encoding="utf-8") as f:
        json.dump({"claims": "verification/strategy/CLAIMS.md", "note": "https://alpo.ge/remark.pdf",
                   "batches": batches}, f, indent=1, ensure_ascii=False)
    for b in batches:
        print(f"{b['batch']}: {len(b['units'])} units, {b['title']}")
    print(sum(len(b["units"]) for b in batches), "units")


if __name__ == "__main__":
    main()
