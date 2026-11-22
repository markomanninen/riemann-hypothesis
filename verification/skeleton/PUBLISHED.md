# Published statements, and the terms of the author's note located on the skeleton

The source labels 361 named propositions as results from the literature, and the five theorems
of [`Main.lean`](../../src/Main.lean) reach 292 of them. For 206 of the 292, a theorem of the
project proves the proposition without premises. The proving theorems together gather 39,190
declarations, which is 5.1 % of the 760,989 declarations that the five theorems reach. That
figure counts only what the five theorems reach solely through those proofs, so it is a lower
limit for what the proofs rest on. Of the 590 declarations of the skeleton, 132 have at least
one of the 361 propositions among their premises.

These figures count what the code places in namespaces for results from the literature. Such a
proposition is a known result that the code states, and the project may still prove it itself.
The figures do not show which part of the argument is new.

The author of the proof announced it in a four-page note. The second half of this document
searches the names of the source for the terms of that note and reports where on the skeleton
the matching names lie.

[`README.md`](README.md) defines the skeleton, its heads, the verbs reach and gather, and the
statement of a declaration. The figures come from the source after the merge of upstream main
on 2026-11-22, and the scripts read text and do not run Lean.

## Words used here

- A published statement is a definition of type `Prop` without parameters whose name has the
  form `….Published.X`, `….Pub.X`, `….Lit.X`, `….LiteratureTheorems.X` or `….Hypotheses₂.X`.
  An example is `GlobalTheory.Published.JacquetShalikaRigidity`. Such a definition states a
  result and proves nothing. Of the 361, 350 lie in a namespace `Published`, four in
  `Hypotheses₂`, three in `Lit`, two in `Pub` and two in `LiteratureTheorems`.
- The claim of a theorem is the part of its statement after the first colon outside brackets,
  and its end is the part after the last arrow outside brackets. The end of a claim without
  an arrow is the whole claim. The premises of a theorem are the hypotheses written before that
  colon and the parts of the claim before its end.
- A theorem proves a published statement when the theorem has no premises and its claim is the
  published statement.
- A theorem derives a published statement when the end of its claim is the published statement
  and the theorem has premises.
- A theorem takes a published statement when the published statement stands among its premises.
- Proves, derives and takes are the three roles. The marks of a skeleton declaration are the
  roles it has towards published statements.

## How the script finds them

[`published.py`](published.py) lists the published statements. For each one, the declaration
graph gives the theorems whose text names it. The script reads from the source the text of each
such theorem before its proof and finds the role by looking for the last part of the published
statement's name, so it looks for `JacquetShalikaRigidity` in a theorem that names
`GlobalTheory.Published.JacquetShalikaRigidity`.

## What the code labels as published

| Published statements | Number |
|---|---:|
| All | 361 |
| In a namespace `Published` | 350 |
| Reached by the five theorems | 292 |
| Reached, and a theorem proves it | 206 |
| Reached, and theorems only derive it | 60 |
| Reached, and the script finds neither | 26 |

The 69 published statements that the five theorems do not reach are left out of the rest of
this document. For 202 of the 206 published statements of the fourth row, the five theorems
also reach a theorem that proves it. For the other four, they reach only the statement.

For the 60 published statements of the fifth row, every theorem that the script finds
concludes the statement from premises. The script does not follow where those premises are
proved in turn, so that row does not show how the project completes the proof.

The five theorems reach the 26 published statements of the last row, and the script finds no
theorem that proves or derives them. A published statement can be supplied in a form that the
definitions of proves and derives miss, for example as a field of a structure or through a
definition that unfolds to another proposition. The last name parts of the 26 are
`BaseChangeIsobaric`, `CaraianiLocalGlobalDual`, `CaraianiTempered`, `CharacterRegularity`,
`ChebotarevOpenNormal`, `CohDimTwo`, `DelignePappasModel`, `DepthZeroCuspidalLL`,
`DepthZeroTypeInertia`, `DiscreteSeriesCharacter`, `DiscreteSpectrumResidual`,
`GaloisRepOfPolarizedPair`, `GoetzkyKoecher`, `GoodChernNumbers`, `HarishChandraCharacters`,
`HilbertBlumenthal`, `HilbertKodairaSpencer`, `HilbertQExpansion`, `InducedCharacterSupport`,
`LocalLanglandsExists`, `MinguezThetaGL`, `OpenImageCondition`, `OpenLiteratureStatements`,
`RealMultDeRhamRank`, `UnitaryDualGL` and `WeylIntegrationFormula`.

The table lists the ten published statements whose proving theorem gathers most declarations.

| Published statement | Theorem that proves it | Gathers |
|---|---|---:|
| `GlobalTheory.Published.ToroidalForFanKS` | `GlobalTheory.TorKSField.toroidalForFanKS` | 5,094 |
| `GlobalTheory.Published.SiegelToroidalIntegral` | `GlobalTheory.siegelToroidalIntegral_holds` | 3,661 |
| `GlobalTheory.Published.SiegelToroidalPolCharts` | `GlobalTheory.T.siegelToroidalCompactification_polarisedCharts` | 3,540 |
| `GlobalTheory.Published.JacquetShalikaRigidity` | `GlobalTheory.JSW.jacquetShalikaRigidity_holds` | 2,262 |
| `GlobalTheory.Published.WeilSiegelFormulaUnitary` | `UpperTheory.Lit.Sw47.weilUnitary` | 1,757 |
| `GlobalTheory.Published.WeilSiegelFormula` | `PositivityTheory.Rg.Wsf.weilSiegelFormula` | 1,718 |
| `GlobalTheory.Published.PrismaticDieudonneHodge` | `UpperTheory.Lit.prismaticDieudonneHodge` | 1,702 |
| `GlobalTheory.Published.SiegelWeilUnitarySchrodinger` | `PositivityTheory.SiegelWeilCoefficients.field` | 1,677 |
| `GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit` | `PositivityTheory.SiegelWeilCoefficients.lit` | 1,668 |
| `GlobalTheory.Published.GoodChernWeil` | `GlobalTheory.GoodMetric.goodChernWeil` | 1,443 |

The 39,190 declarations of the opening are the declarations that lie at or below at least one
of the proving theorems in the dominator tree, each counted once. The figure leaves out a
declaration that a second chain reaches without passing through the proving theorem, because
the proving theorem then does not dominate it.

## Marks on the skeleton

| Skeleton declarations | Number |
|---|---:|
| All | 590 |
| Take at least one published statement | 132 |
| Prove or derive a published statement | 25 |
| Take one, and prove or derive one | 7 |
| Carry no mark | 440 |

The seven declarations of the fourth row are counted in the second and the third row as well,
so 150 declarations carry a mark. Of the 342 heads, 64 take at least one published statement.

A skeleton declaration that takes published statements is a step that holds when those results
and its other premises hold. The five theorems are stated without premises, so the project has
to supply those results somewhere between the five theorems and that step. The script does not
locate the declarations that supply them, which may lie outside the skeleton.

`SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt`, which gathers 52,094 declarations,
takes ten published statements, among them `ResolutionCharZero`, `PrincipalisationCharZero`,
`SiegelToroidalIntegral` and `ToroidalForFanKS`. The largest number that a skeleton declaration
takes is twelve. Ten skeleton declarations take that many, and they hang in one run from
`main_theorem_published_inputs_third_alt_alt` down to `miStar2_of_allTrue_alt_alt`.

[`OUTLINE-PUBLISHED.txt`](OUTLINE-PUBLISHED.txt) has one line for each of the 38 lines of
`OUTLINE.txt`, in the same order and with the same numbers. It differs in three ways. Every
line shows a name without its namespaces, and a line that stands for a folded run of wrappers
shows the name of the head that the run ends in and keeps the number of the first wrapper.
Square brackets hold the second, third and fourth parts of the module name of the declaration
shown, written as words, so `ThetaPairLifts` reads Theta Pair Lifts. They replace the count of
folded declarations. Curly brackets hold the marks of the declarations of the line.

## The author's note

The note is [remark.pdf](https://alpo.ge/remark.pdf). It says the following about the argument.

- The argument descends from the argument of Stepanov for the Riemann Hypothesis over function
  fields, which uses a divisor with multiplicity.
- Multiplicity is hard to find over the integers, and the argument gets it from a chain of theta
  lifts between totally definite unitary groups, where each lift wins one more order of
  multiplicity.
- For a von Mangoldt sum of length X the chain has about the square root of X lifts.
- A timeline of 20 entries names further ingredients. Among them are norms of the lifts with
  divisibility by Chowla-Selberg, Weyl and the Siegel mass formula, a lower bound for the
  divisibility of the iterated lift, an Iwasawa tower, a seesaw with the name of Rallis that
  turns the period of the iterated lift into a Bessel period, the Bost slope inequality, a
  relative trace formula with Poincaré series, periods of Gan, Gross and Prasad, the explicit
  formula of Guinand and Weil, covolumes, a weakening of the Vandiver conjecture and a choice
  of the tower that uses a result of Behrend.
- The author writes that Claude compiled the timeline and that some of its entries paraphrase
  a summary of parts he has not mastered yet.

`published.py` holds 20 search patterns, one for each term of the table below. The number of
patterns has nothing to do with the number of timeline entries. A pattern is tried on every
part of a declaration's name and of its module path, and a declaration matches when one part
fits. A pattern can be wider than its row label, and the second column shows the parts that it
matched most often. The counts of that column and of the column Matches take in every
declaration of the source. The column Reached counts the matches that the five theorems reach,
and a declaration can match the patterns of two rows.

The last five columns say where the reached matches lie in the dominator tree, as shares of
the reached matches of the row. The columns stand for these declarations of the outline. A
match lies below a declaration when that declaration gathers it.

| Column | Declaration | Gathers |
|---|---|---:|
| A | `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` | 506,214 |
| B | `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`, which lies below A | 266,135 |
| C | `UpperTheory.One.vwin_of_row` | 55,754 |
| D | `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` | 51,784 |
| Else | below none of A, C and D | |

The first row of the table gives the same shares for all reached declarations. A row of
matches is spread like the whole proof when its shares are near that row, and its names are
gathered in one part when a share is far above it.

| Term of the note | Name parts that match most often | Matches | Reached | A | B | C | D | Else |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| all reached declarations | | | 760,989 | 67 % | 35 % | 7 % | 7 % | 19 % |
| theta lifts | `ThetaLifts` 7,527, `ThetaCorrespondence` 6,345 | 14,609 | 13,328 | 82 % | 38 % | 1 % | 1 % | 16 % |
| definite unitary groups | `DefiniteUnitaryClassSetFinite` 33, `BaseChangeDefiniteUnitary` 32 | 548 | 541 | 35 % | 32 % | 1 % | 10 % | 55 % |
| Chowla-Selberg | `MeanLogPeriodConjugatesEqChowlaSelberg` 5, `MeanLogPeriodChowlaSelberg` 3 | 19 | 19 | 100 % | 74 % | 0 % | 0 % | 0 % |
| Siegel mass | `UnitaryGroupMassFormula` 23,477, `SiegelMassRatios` 68 | 23,651 | 22,355 | 94 % | 74 % | 0 % | 0 % | 6 % |
| Weyl, with divisibility | `GradedWeylDivisibility` 603 | 603 | 602 | 27 % | 8 % | 0 % | 0 % | 73 % |
| divisibility of the lift | `Divisibility` 4,633, `DivisibilityProofs` 1,146 | 5,908 | 4,839 | 98 % | 18 % | 0 % | 0 % | 2 % |
| Iwasawa tower | none | 0 | 0 | | | | | |
| seesaw | `SeeSaw` 698, `HermitianAdaptedPlaneSeesaw` 33 | 1,583 | 1,458 | 95 % | 93 % | 0 % | 0 % | 4 % |
| Bessel period | `ThetaBesselIsometries` 428, `FormalDegreeBessel` 427 | 6,375 | 6,066 | 98 % | 94 % | 0 % | 0 % | 2 % |
| Rallis | `Rallis` 89, `RallisInnerProduct` 88 | 401 | 398 | 55 % | 27 % | 0 % | 2 % | 43 % |
| Bost slope inequality | `ChainSlopeWindows` 379, `DiagonalSlopes` 302 | 2,105 | 1,590 | 93 % | 10 % | 3 % | 1 % | 3 % |
| relative trace formula | `TraceFormula` 1,650 | 1,652 | 1,604 | 2 % | 0 % | 1 % | 0 % | 96 % |
| Poincaré series | `PoincareSeriesInner` 14, `PoincareSeriesUnitaryAbsolutelyConvergentModerat` 14 | 120 | 120 | 96 % | 49 % | 0 % | 0 % | 4 % |
| periods of Gan, Gross and Prasad | `ExistsGanGrossPrasadRowWeights` 17, `ExistsGanGrossPrasadColumnWeights` 14 | 68 | 59 | 88 % | 88 % | 0 % | 0 % | 12 % |
| weakening of Vandiver | none | 0 | 0 | | | | | |
| covolumes | `CovolumeBounds` 1,047, `FiniteCovolume` 873 | 4,095 | 3,581 | 57 % | 21 % | 1 % | 0 % | 43 % |
| Behrend | none | 0 | 0 | | | | | |
| explicit formula of Guinand and Weil | `ExplicitFormula` 288, `FirstKernelExplicitFormula` 146 | 499 | 493 | 100 % | 31 % | 0 % | 0 % | 0 % |
| von Mangoldt sum | `AdditiveMulEqVonMangoldtConvolution` 9, `AdditiveEqPolynomialVonMangoldtConvolutionOne` 8 | 80 | 76 | 74 % | 1 % | 0 % | 3 % | 24 % |
| Stepanov | none | 0 | 0 | | | | | |

Five things can be read from the table.

- Sixteen of the 20 terms have matches. No name and no module path of the source holds the
  words Stepanov, Vandiver, Behrend or Iwasawa tower.
- B gathers 35 % of all reached declarations. For the seesaw, the Bessel period, the periods of
  Gan, Gross and Prasad, the Siegel mass and Chowla-Selberg, between 74 % and 94 % of the
  reached matches lie below B.
- The part of A outside B gathers 31.5 % of all reached declarations. For the divisibility of
  the lift, the Bost slope inequality, the von Mangoldt sum and the explicit formula, between
  69 % and 83 % of the reached matches lie there.
- Else holds 19 % of all reached declarations. Of the reached matches of the pattern for the
  relative trace formula, 96 % lie there, and so do 73 % of the matches of
  `GradedWeylDivisibility`.
- The matches for theta lifts, Rallis and covolumes are spread more widely, and the matches
  for definite unitary groups lie mostly in Else and in B.

A separate count finds the word Iwasawa in the name or the module path of 26,784 declarations
of the source. Of these, 24,882 lie in modules whose path has the part `IwasawaDecomposition`,
which names a decomposition of a group. The other 1,902 were not examined.

The writer of this document reads the proposition `UpperTheory.Top.VWin` as the weakening of
Vandiver that the note speaks of. No name says so, and the reading rests on a resemblance
alone. The definition `UpperTheory.Top.VVle` in
[`ExistsPageN.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean)
bounds a sum over primes l and exponents e of lengths written `shaLen`, which the source takes
from `Formalism.GaloisCohomology`. The note's entry speaks of cohomology classes indexed by a
prime ℓ and an exponent e. `VWin` is built from `VVle`, and it is one of the two premises of
`every_character_of_literature_of_vWin`. The theorem `vwin_of_row` has one premise and `VWin`
as the end of its claim, and it gathers 55,754 declarations, 7.3 % of what the five theorems
reach.

## Limits

- The five namespaces are labels that the code gives. A result from the literature that the
  code states under another name is not counted. The claim of `topCovolSlim2_use_alt_alt`, for
  example, has the premises `HT.FarguesExact`, `GR.ZarhinStatement` and
  `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement`. The writer of
  this document reads those three as results from the literature, by their names, and they lie
  in none of the five namespaces.
- If each of the 361 is a result from the literature, as its namespace says, the 361 are a
  lower limit for the number of literature results that the code states. A skeleton declaration
  without a mark can still restate a known result.
- The script reads the roles from text. It compares last name parts and splits a claim at its
  last arrow outside brackets. A theorem whose claim ends in a quantifier or a conjunction is
  counted neither as proving nor as deriving, which can move a published statement into the row
  of 26 and a skeleton declaration into the row without a mark.
- A match in the table of note terms is a match of a name. It shows where the code uses a word,
  and it does not show that the mathematics behind the name is the step that the note means.
  The patterns were chosen by the writer of this document and stand in `TERMS` at the top of
  `published.py`.
- A term without a match can mean that the code lacks the ingredient. It can equally mean that
  the code names the ingredient with other words. The author describes the timeline, which
  names the Iwasawa tower, Vandiver and Behrend, as partly a paraphrase.

## Running it

```bash
python3 -I verification/skeleton/build.py        # writes the skeleton that this script reads
python3 -I verification/skeleton/published.py    # about 25 s
```

## Files

| File | Content |
|---|---|
| `published.py` | finds the published statements, their roles and the name matches |
| `published.json` | the figures in `summary`, the 361 published statements in `statements`, the marks of the 590 skeleton declarations in `skeleton`, in the order of `nodes` in `skeleton.json`, and the name matches in `terms` |
| `OUTLINE-PUBLISHED.txt` | the outline with module paths and marks |
