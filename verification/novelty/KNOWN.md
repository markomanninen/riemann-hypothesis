# Where the known results sit in the proof

The five theorems of [`Main.lean`](../../src/Main.lean) use 800,348 declarations. Of these,
215,161, which is 26.9 %, are used in the proof of some result that the source labels as known
or that the catalogue of [`../reuse`](../reuse/CATALOGUE.md) names. The count rises to 307,302,
which is 38.4 %, when two further results, `Row` and `Green`, are counted as known too. The
source proves both without a label, and the commentary of the strategy reads them as published
theorems. One branch of the proof holds the chain of steps that the strategy follows, and this
document calls it the branch of the route. It has 326,657 declarations, and 322 of them, 0.1 %,
are used in the proof of a known result.

The figures show where the source proves results that it labels as known or that the catalogue
names, and where it does something else. They do not show what is new. A declaration outside
the proof of every known result can still be a standard lemma that carries no label, and the
source's proof of a known result can itself be new. The search of the literature that
[`README.md`](README.md) describes asks the question of novelty step by step, and this document
tells that search where the labelled results end.

A script, [`known.py`](known.py), computed the figures from the exact graph of
[`../decl-graph`](../decl-graph/README.md), in which a compiled constant points to every
constant that its type and its proof mention. The names of 90 of the known results, and the
relations of all, come from readings by a language model, which
[`../reuse`](../reuse/AUDIT.md) describes. No mathematician has checked those readings.

## Words used here

- A declaration is a theorem, a definition or another item of the source text. The five
  theorems use a declaration when a chain of mentions leads from one of them to it.
- The outline is a list of 40 theorems that mark the largest steps of the proof, which the
  [README of the skeleton](../skeleton/README.md) defines. Each of them is a line, with the
  number that [`READING.md`](../skeleton/READING.md) gives it. A line gathers a declaration when
  the five theorems use the declaration only by way of the theorem of that line. A line hangs
  below another when the upper line gathers it.
- A known result is one of two things. The first kind is a proposition that the source labels
  as a result from the literature, that the five theorems reach and that a theorem of the
  source states without hypotheses. There are 206. The second kind is a statement of the
  catalogue of `../reuse`, which lists the theorems that are written with definitions of
  Mathlib alone. The statement counts when the check of the catalogue has classed it as a named
  theorem or a standard fact, when the five theorems use it, and when it is not itself a form
  of the Riemann hypothesis. There are 90. Together they are 296 known results.
- The proving theorem of a known result is the theorem of the source that states it.
- The cone of a known result is the set of declarations that its proving theorem rests on, the
  theorem itself included. A declaration is in a cone when it is in the cone of at least one of
  the 296 known results.
- The line of a known result is the lowest line of the outline that gathers its proving
  theorem. Every use of the result by the five theorems passes through that line.
- `Row` and `Green` are two propositions that the source proves and does not label as results
  from the literature. The [commentary of the strategy](../strategy/README.md) reads `Row` as
  the existence of Galois representations for certain automorphic representations over CM
  fields and `Green` as the parametrisation of the cuspidal characters of the general linear
  groups over prime fields. The proving theorem of `Row` is the theorem of line 33 and rests on
  195,181 declarations. The proving theorem of `Green` lies at line 3 and rests on 598.

## The four branches and the rest

Four lines of the outline head the branches of the proof. Line 4 derives the statement of the
first theorem of `Main.lean`, that no Dirichlet L-function has a zero with real part above 1/2,
from seven hypotheses, and the chain of steps of the strategy lies below it. Line 24 derives a
bound on covolumes, line 30 derives a bound `VWin` on lengths of Galois cohomology groups, and
line 33 states `Row`. The table gives the declarations that each of the four lines gathers and
how many of them are in a cone. The rest are the declarations that none of the four lines
gathers, because more than one branch uses them or because the lines above use them directly.

| Part of the outline | Declarations | In a cone | Share | In a cone with `Row` and `Green` | Share |
|---|---:|---:|---:|---:|---:|
| Line 4, the branch of the route | 326,657 | 322 | 0.1 % | 322 | 0.1 % |
| Line 24, the covolume bound | 54,038 | 599 | 1.1 % | 599 | 1.1 % |
| Line 30, the bound `VWin` | 56,755 | 8,721 | 15.4 % | 8,721 | 15.4 % |
| Line 33, the statement `Row` | 56,554 | 1,762 | 3.1 % | 56,554 | 100 % |
| The rest | 306,344 | 203,757 | 66.5 % | 241,106 | 78.7 % |
| All declarations that the five theorems use | 800,348 | 215,161 | 26.9 % | 307,302 | 38.4 % |

The table says three things.

- Two thirds of the rest lie in a cone, and almost four fifths with `Row` and `Green`. A cone
  also holds the general lemmas that a proving theorem uses, so the shares give the most that
  the proofs of known results take of the rest.
- Only 322 of the 326,657 declarations of the branch of the route are used in the proof of a
  known result. The branch holds 40.8 % of all declarations that the five theorems use. It
  holds the proving theorems of 13 known results, and line 4 takes further known results as
  hypotheses, whose proving theorems lie above it.
- Counting `Row` and `Green` adds 92,141 declarations, 54,792 of line 33 and 37,349 of the
  rest. The other declarations of the two cones were in a cone already.

With `Row` and `Green` counted, 493,046 declarations are in no cone. The branch of the route
holds 326,335 of them, the branch of the covolume bound 53,439, the branch of `VWin` 48,034 and
the rest 65,238.

## Where the known results attach

The line of a known result tells which part of the proof needs it.

| Line of the known result | Known results |
|---|---:|
| Line 1, 2 or 3, above the four branches | 222 |
| Line 4 or a line below it, the branch of the route | 13 |
| Line 24 or a line below it, the covolume bound | 9 |
| Line 30 or a line below it, the bound `VWin` | 30 |
| Line 33 or a line below it, the statement `Row` | 21 |
| No line | 1 |

The 222 results above the four branches are used by more than one branch or by the top lines
directly. Line 3 has 106 of them, line 1 has 78 and line 2 has 38. The one result without a
line is the proposition `PoincareDeRhamDuality`. The five theorems reach the proposition, and
they do not use the theorem that states it. Among the results at or below a branch are these,
with the names that the readers of `../reuse` gave.

- At lines 30 to 32 lie both forms of the Kronecker-Weber theorem, the proposition
  `FerreroWashington`, the criterion of Néron, Ogg and Shafarevich and the proposition
  `JacquetShalikaRigidity`.
- At lines 34 to 38 lie five statements of the purity of the branch locus,
  Borel's finiteness of class numbers and the propositions `ArthurClozelStrongTC` and
  `GrothendieckDeformation`.
- At lines 5 to 18, below line 4, lie the 13 known results of the branch of the route. One is
  the labelled proposition `HeckeEntire`. The other 12 are statements of the catalogue, among
  them the addition theorem and the duplication formula of the Weierstrass ℘-function.

[`known.json`](known.json) lists all 296 with their lines.

## Limits

- The shares measure one definition of known and are neither lower nor upper bounds for the
  part of the proof that proves known results. The source proves further results that are
  known and carry no label, as `Row` and `Green` show, which makes the shares too low. A cone
  holds everything that a proving theorem rests on, general lemmas that the route uses as well
  included, which makes them too high.
- A declaration in a cone helps to prove a result whose statement is known. The proof that the
  source gives for that result was not compared with the published proof.
- The audit of `../reuse` read 70 of the 206 labelled propositions and took most of those 70
  for special cases or weaker forms of the published theorems. All 206 count as known here.
- That 90 of the known results are known rests on the reading of the catalogue by a language
  model, which no mathematician has checked.
- The lines of the outline come from the dominator tree of the exact graph, which counts what
  the compiled proofs mention. The compiled files come from the build cache of the repository.

## Running it

```bash
python3 -I verification/novelty/known.py    # about one minute
```

The script needs the files of `exact_graph.py` of `../decl-graph`, the outline and the readings
of `../skeleton` and the files `summary.json`, `audit.json` and `catalogue.json` of `../reuse`.

## Files

| File | Content |
|---|---|
| `known.py` | places the known results on the outline and counts their cones |
| `known.json` | the figures of this document, the 40 lines with their shares and the 296 known results with their lines |
