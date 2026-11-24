# The outline in plain words

The top line of the outline is a theorem of [`Main.lean`](../../src/Main.lean). It states that
the value `DirichletCharacter.LFunction χ s` of the Mathlib library is not zero for every
`DirichletCharacter` χ of that library and every complex number s with real part above 1/2,
except when χ is the trivial character and s is 1. The 37 lines below it state the largest
steps that the proof passes through, which are the ones that gather at least 10,000
declarations in the graph of the README. This document says for each of the 38 lines what its
Lean statement claims, in plain sentences and in ordinary notation.

The readings were written by a language model and checked by further runs of the same model.
No mathematician has checked them. Each reading has a separate paragraph for what a name only
suggests, and the check looked for meanings asserted outside that paragraph.

The model run that wrote a reading also rated its confidence. High means that it saw the
statement and what every project definition in it says. Medium means that it saw the form of
the claim with some names left unopened. Low means that it saw little more than a chain of
named conditions. One line is rated high, 24 are rated medium and 13 are rated low.

[`README.md`](README.md) defines the outline, its lines, the head and the wrappers of a line
and the verb gathers. The readings are of the source after the merge of upstream main on
2026-11-22.

## What the top of the outline says

The numbers are the line numbers of the outline, and every name in code font is a name of the
source. A reading covers the statement of the head of a line. It covers neither the proof nor
the statements of the wrappers. The sentences below about a proof, about the wrapper of line 1
and about the names of `Row` come from the source files, which the model session that wrote
this document read directly.

A premise of a line is a hypothesis that its theorem takes before its named conclusion. A
condition inside the conclusion is not counted as a premise.

- Line 1 has no premises. Its head `everyCharacter` states the proposition that the code calls
  `EveryCharacter`. For every N ≥ 1, every `DirichletCharacter` χ of level N and every complex
  number s with real part above 1/2, the value `LFunction χ s` is not zero, unless χ is the
  trivial character and s is 1. The wrapper of the line is the theorem of `Main.lean`, and its
  proposition `DirichletLNonvanishingRightOfHalf` in
  [`Statements.lean`](../../src/Statements.lean) has word for word the same definition.
- Line 2 hangs from line 1 and derives `EveryCharacter` from one premise. The statement of
  line 2 writes that premise as `Row0b` applied to the condition `IsRecT`. The code names the
  same proposition `Row`, and line 33 writes it as `Row0b recT`, where `recT` is the code's
  name for that condition. The definitions show the form of `Row`. For every CM number field
  E, every prime l, every a ≥ 1, every π of the code's type `CuspSub` that meets `IsRegAlg` and
  every χ of the type `HChar` for which the pair meets `PolarizedPair`, there exist a
  homomorphism r into the invertible a by a matrices over the field that the code calls
  `Qbar l`, an integer and a function `HT` that meet a condition `PropsB`. The statement also
  quantifies over an algebraic closure of E and an isomorphism from `Qbar l` to ℂ, which this
  summary leaves out. The names suggest Galois representations attached to automorphic
  representations, which the Lean text that the reading was made from does not show.
- Line 33 hangs from line 1 and states `Row0b recT` with no premises. The proof of the head of
  line 1 in
  [`MainConclusion.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean)
  applies the theorem of line 2 to the theorem of line 33.
- Lines 3 and 30 hang from line 2. Line 3 derives `EveryCharacter` from a bundle of three fields
  and a proposition `VWin`. Two fields of the bundle are `Row`. The other field is
  `RecTExists`, which says that for every number field and every prime of it a map exists that
  meets a condition `IsRecT`. `VWin` says that a condition `VWinAt ψ 401` holds for every
  primitive Dirichlet character ψ.
- Line 30 derives `VWin` from three named statements. Line 31 hangs from line 30 and line 32
  from line 31, and each derives `VWin` from one bundle of named statements.
- Lines 4 and 24 hang from line 3. Line 4 derives `EveryCharacter` from seven premises. Two
  premises are bundles. The text that was read shows 28 named statements of the first and 29
  of the second before it is cut. Three premises are the propositions `ThetaIntegralsAgree`,
  `LocalMatching` and `CovolumeBoundOfX`. The last two are `RecTExists` and `VWin`.
- Line 24 derives `CovolumeBoundOfX` from fifteen named propositions.
- Lines 5 and 23 hang from line 4. Line 5 concludes that a record of the type
  `HypsAlt S0.NL DefiniteSideCondition` exists. Its premises are six of the seven premises of
  line 4 and one more. Line 23 concludes the proposition `ZeroFreeAll`, which says that every
  primitive Dirichlet character ψ meets the condition `ψ.ZeroFreeAbove (1/2)`. Its premises are
  the existence of such a record, `VWin` and a statement `Green`.
- Lines 6 to 22 hang below line 5. Their statements are written in a vocabulary of the project,
  with names such as `FamP`, `LinkedAt`, `Closed` and `HypsAlt`, which the definitions shown
  to the readers do not open. The readers saw definitions up to three steps away from the
  statement, as the next section describes. A person can follow which named condition follows
  from which, and the mathematics behind the names stays closed.

Lines 1, 33, 35 and 37 have no premises. Each of the other 34 lines derives one or more named
statements from named statements. By the README, a line hangs below another when the five
theorems depend on the lower line only by way of the upper one. A line without premises can
therefore still have lines hanging below it. A lower line can also have premises that the line
above it lacks, as line 3 has `RecTExists` and `VWin`. The proof of the upper line then has to
supply them, and the readings do not show how, since they cover statements only.

## How the readings were made

1. [`dossier.py`](dossier.py) wrote a dossier for the head of each line. A dossier holds the
   Lean statement, the statements of the wrappers of the line, and definitions at three
   levels. Level one holds the definitions that the statement names, level two those that the
   definitions of level one name, and level three those that the definitions of level two name.
   A dossier stops after three levels or after 45 definitions, whichever comes first. Definitions of the first two levels are shown with
   their bodies and those of the third level without. The 38 dossiers hold 1,622 definitions
   and about one million characters.
2. A first reader wrote, from the dossier alone, what the theorem states, its premises in
   order, its conclusion, the statement in ordinary notation, the definitions it relied on, and
   its confidence. It wrote in a separate field what the names suggest beyond the text.
3. A second reader wrote its own reading from the same dossier without seeing the first.
4. A check compared both readings with the Lean text. It looked for a missing or an added
   premise, a wrong quantifier, a wrong number or exponent, a wrong conclusion, and a meaning
   asserted for a name whose body the dossier does not show.
5. A first reading with an error was corrected and checked again.

The first reader, the second reader, the check and the corrections are runs of the command
line tool Claude Code. Each run was started in a folder that held only the dossiers and, for
the check, the two readings. The briefs of the four roles are in [`briefs/`](briefs/).

The reading printed for a line is the first reading after correction. The second readings
served for the comparison and were left as they were.

The check found 16 errors in the first readings of ten lines and four errors in the second
readings of three lines. Each error was in the detail inside a premise or a conclusion. A
reading called a type a group although the dossier does not show that it is one, left out a
condition inside a premise, or gave a wrong count. No error changed the list of premises of a
line or the name of its conclusion. After correction all 38 printed readings passed the check.
Eight of the ten passed after one round, line 7 after two and line 10 after three. The last
corrections of lines 7 and 10 are the exception to the separate runs. The model session that
wrote this document made them directly and removed the detail that the check had faulted, and
the check then passed both.

A model of another maker then repeated the check. Gemini, run in the Antigravity editor, read
the same dossiers and the printed readings with the brief of the check and faulted 20 of the 38
readings with 71 findings. Each finding was compared with the words of the reading and with the
Lean text of the dossier by further runs of Claude Code. No finding showed a reading that
states what the Lean text contradicts. In 21 cases the summary of a premise left out a
quantifier, an argument or a hypothesis without saying so, and in 16 cases the wording was
inexact, with an unbound variable, a dropped argument or a claim stronger than the dossier
shows. In 17 cases the reading uses an ordinary word for an object whose body the dossier does
not show, and 23 findings did not hold, most of them because another field of the same reading
gives the detail said to be missing. The 16 lines with cases of the first two kinds were
changed in 40 places, and an entry says so when it was changed. A summary of a premise now
names what it leaves out. The 16 changed readings were then checked once more by runs of Claude
Code, each in a folder with one dossier and one reading. Twelve passed. In the other four the
check found five errors, four of them ordinary words for names without a shown body and one a
premise of the wrapper theorems of line 8 that the changed text had left out. The five were
corrected with the text of the check, and a second check of those four readings found no
error. The other cases of ordinary words stand as they were.

An entry below shows, in this order, where the head lies, what the theorem states, its
premises and its conclusion, a display of the statement in ordinary notation, the names that
the reading does not open, what the names suggest, the confidence with its reason, and what
the check found. A reading can say that definitions were left out, which refers to the limit
of 45 definitions of its dossier.

## A deeper reading of lines 6 to 22

The first readings of lines 6 to 22 stayed at the level of names. After the record `D7` was
opened in [`D7.md`](D7.md), each of these 17 lines was read once more by a run that saw the
dossier of the line, the whole Lean text of `D7` with the 282 definitions below it, and the ten
readings of [`GLOSSARY.md`](GLOSSARY.md). The briefs are `briefs/reread-reader.txt` and
`briefs/reread-check.txt`.

The 17 deeper readings open 107 names that the first readings left unopened, and the number of
names they leave unopened falls from 180 to 124. They also say more, and the check found more
to fault. It found 43 errors in 16 of the 17 readings. After those were corrected with the text
that the check supplied, a second check found 46 further errors in 15 readings, and they were
corrected in the same way. Most errors of the second round are of one kind. The reading uses a
word of mathematics, such as irreducible or unitary, for a name whose body no file shows.

Gemini then checked the deeper readings as it checked the printed ones. It found line 13
faithful and made 106 findings on the other 16 readings. Runs of Claude Code compared each
finding with the Lean text. Three findings did not hold and 103 did. None of the 103 is a
sentence that the Lean text contradicts. In 50 the reading uses a word of mathematics for a
name whose body no file shows, in 31 the wording is inexact, and in 22 a quantifier, an
argument or a hypothesis is left out without a note. The weightiest are in line 8, where the
reading stated two bounds without the hypotheses under which the Lean text places them, and
in line 18, where it named a density theorem for a statement of existence. All 103 passages
were replaced with text that the run checked against the Lean text.

The 16 changed deeper readings were then checked again, each by a run of Claude Code in a
folder with its dossier, the text of `D7`, the glossary and the reading. Fourteen passed. In
lines 12 and 22 the check found one error each, a word of mathematics for a name whose body no
file shows, and both were corrected with the text of the check. A further check of the two
corrected readings found no error. As a test of the check itself, two numbers of the deeper reading of
line 8 were changed to wrong ones in a copy, and the check found both. The check and the
readings come from one maker's models, and Gemini has not read the corrected texts. An entry of lines 6 to 22 prints the
first reading, which passed, and below it the deeper reading under its own heading. The reader
rated its confidence low for twelve of the 17 deeper readings and medium for five, where the
first reader gave low for six and medium for eleven.

## What stays unopened

A name is unopened in a reading when the first reader marked that the dossier did not let it
see in full what the definition says. `RecTExists` is an example. Its body is shown, and the
body rests on `IsRecT`, which is shown without a body.

The readings leave 194 different names unopened. The table lists the ten names that are
unopened in the largest numbers of lines.

| Name | Lines |
|---|---:|
| `RecTExists` | 10 |
| `D7` | 6 |
| `UnitaryGroupThirdPlaceHypotheses` | 5 |
| `LinkedAt` | 5 |
| `parametersOfDependence` | 5 |
| `SlotNormCondition` | 4 |
| `BoundAtTwoThreeFamilyFonAlt` | 4 |
| `KPx` | 4 |
| `BundleCondition` | 4 |
| `MIstar2` | 4 |

Each of the ten names is unopened in at least two of the lines 6 to 22. A person who wants to
see the mathematics of those lines can start by opening these ten definitions.

## Limits

- A dossier stops after three levels or after 45 definitions, and the statement splitter keeps at most
  3,000 characters of a statement and 2,000 of a body. A reading says where the text it saw was
  cut.
- A reading covers the statement of the head of a line. It does not cover the statements of
  the wrappers folded into the line.
- The first reader, the second reader and the check are the same language model, so they can
  share a blind spot that the check does not find.
- A reading says what a statement claims. It does not say why the statement holds, and it does
  not say whether the statement is the one that the mathematics needs.
- What a reading reports as a suggestion from the names is a guess.

## Files

| File | Content |
|---|---|
| `dossier.py` | writes the dossiers into `data/dossiers`, which git ignores |
| `briefs/` | the briefs of the first reader, the second reader, the check and the correction |
| `reading.json` | the 38 readings, each with the second reading and the errors that the check found |
| `reading-exact.json` | the readings of lines 39 and 40, the two lines that only the exact outline has |
| `reading.py` | writes the part of this document below this section from `reading.json` and `reading-exact.json` |

## How to read the table and the entries

In the table, the dots before a head give its depth, and a line hangs from the nearest line
above it that has one dot fewer. The column Gathers gives the number of declarations that the
line gathers, which for a line with wrappers is the number that its first wrapper gathers. A
cell that ends in three dots is cut.

<!-- lines -->

## The outline at a glance

| Line | Head | Gathers | Conclusion of the statement | Confidence |
|---:|---|---:|---|---|
| 1 | `everyCharacter` | 760,227 | For all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1), the value LFunction χ s is nonzero | high |
| 2 | · `everyCharacter_of_row` | 577,248 | EveryCharacter holds, that is, LFunction χ s ≠ 0 for all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1) | medium |
| 3 | · · `every_character_of_literature_of_vWin` | 506,214 | EveryCharacter holds, that is, LFunction χ s ≠ 0 for all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1) | medium |
| 4 | · · · `every_character_of_theta_integrals_local_matching` | 315,443 | EveryCharacter holds, that is, LFunction χ s ≠ 0 for all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1) | medium |
| 5 | · · · · `nonempty_hyps_definite_side_of_closed_bound` | 266,135 | There exists at least one record of type HypsAlt S0.NL DefiniteSideCondition | low |
| 6 | · · · · · `hypotheses_nonempty_of_unramified_exponents_alt` | 89,671 | the type HypsAlt NL DefiniteSideCondition is nonempty, that is, at least one record of that type exists | medium |
| 7 | · · · · · · `allRows_of_open0_alt` | 34,967 | AllRowsAlt KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) NN DefiniteSideCondition holds, with p = parametersOfExtension N S Γ | medium |
| 8 | · · · · · · · `at_choice_alt` | 14,543 | SelectionLpBound 𝒜 σ and SelectionOrderBound 𝒜 σ and H_hTF 𝒜 all hold | medium |
| 9 | · · · · · · · · `offDiag` | 13,933 | Closed 𝒞 holds for the property that sends Fm to the statement that for every proof hc that Fm is in 𝒞 the condition TheoremSSelected Fm 3 (sel Fm … | medium |
| 10 | · · · · · · · `servH_row_of_artin` | 10,808 | Row Q Lk (ServH ker) holds, that is, there is a family E with RowE Q Lk E such that every class 𝒜 and raw selection σ satisfying IsSel Q Lk E 𝒜 σ … | low |
| 11 | · · · · · · `member_bundles_large_unramified_exponents_alt` | 20,058 | SiegelMassRatioCM and MemberE p.s and ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) all hold, with p = parametersOfExtension … | low |
| 12 | · · · · · · · `exists_baseLattice_of_prime_alt` | 13,160 | MemberE holds for p.s, and ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) holds, which means that some slot R satisfies LargeBaseCondition … | medium |
| 13 | · · · · · · `final_alt_alt` | 15,685 | LinkedAt holds for parametersOfDependence hL cDep with the row condition (Q, L) ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 LinkN) | low |
| 14 | · · · · · · · `final_of_alt` | 14,931 | LinkedAt holds for parametersOfDependence hL cDep with the row condition (Q, L) ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 LinkN) | medium |
| 15 | · · · · · · · · `linkN_of_twGood_galoisPreconditions` | 14,338 | LinkN Fm holds, that is, there exist real C and x0 such that for all x ≥ x0, all i in Ix(x) with ShaFinOdd(D(x,i)) and all j in {1,…,m}, the … | medium |
| 16 | · · · · · `ontoX_and_lamLow_of_unitaryGroupHypotheses'` | 20,036 | SurjectiveOntoX and LambdaLowerBound₂ both hold | low |
| 17 | · · · · · · `ontoX_of_hypotheses_alt_alt` | 19,703 | SurjectiveOntoX holds | medium |
| 18 | · · · · · `open_orbit_of_unramified_exponents_alt` | 12,471 | for every real cDep, all twelve statements LinkedAt p r hold with p = parametersOfDependence hL cDep and r equal in turn to SlotPrimitivityCondition, … | low |
| 19 | · · · · · · `miStarRow_alt_alt` | 10,783 | for all N of type NormChoiceExtension hL, S of type SExt and Γ of type GeoP, both LinkedAt p (Q, L ↦ Row Q L (AtAll MI)) and LinkedAt p … | medium |
| 20 | · · · · · · · `miStarRowClosing_alt_alt` | 10,559 | RowE (IsGoodE p.s) (BundleLinkage p) MI holds, where MI is the property of a bundle b that the code writes as (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 … | medium |
| 21 | · · · · · · · · `miStar_row_alt_alt` | 10,306 | RowE holds for the same slot IsGoodE p.s and the same linkage BundleLinkage p, with the property that sends a bundle b to the condition MIstar2 of … | medium |
| 22 | · · · · · · · · · `miStar2_of_allTrue_alt_alt` | 10,050 | the condition MIstar2 of the object packageCoefficientSpace W, which is W.Q.Rl.toCx3 W.Q.F, holds when applied to W.Q.F.eV at the field zs of that … | low |
| 23 | · · · · `zero_free_all_of_green_v_win` | 12,029 | ZeroFreeAll holds, that is, every ψ of type PChar satisfies ψ.ZeroFreeAbove (1/2) | low |
| 24 | · · · `topCovolSlim2_use_alt_alt` | 52,094 | the proposition that the code calls CovolumeBoundOfX holds, which is the condition Closed applied to FamHyp and to the property that some C0 ≥ 0 … | low |
| 25 | · · · · `deep_slim_use` | 30,169 | DeepStR holds, that is, one constant C ≥ 0 exists for which MeanAll Y.U (xiR D) (ell D) C holds for all admissible D, T, j, Y, e and o with at most … | medium |
| 26 | · · · · · `deepStR_of_use` | 29,778 | DeepStR holds, that is, one constant C ≥ 0 exists for which MeanAll Y.U (xiR D) (ell D) C holds for all admissible D, T, j, Y, e and o with at most … | medium |
| 27 | · · · · · · `goodTower_volume_of_reduced` | 20,438 | both GoodTowerExistsX and VolumeTheoremX hold | medium |
| 28 | · · · · · · · `good_tower_volume_theorem` | 17,143 | both GoodTowerExistsX and VolumeTheoremX hold | medium |
| 29 | · · · · `topCovolG_alt_alt` | 12,517 | the condition CovolumeBoundOfX holds | low |
| 30 | · · `automorphic_window_of_inputs` | 55,754 | VWin holds, that is, VWinAt ψ 401 holds for every primitive Dirichlet character ψ | medium |
| 31 | · · · `v_window_of_automorphy_csd_ss_mono_odd` | 55,113 | VWin holds, that is, VWinAt ψ 401 holds for every primitive Dirichlet character ψ | low |
| 32 | · · · · `vwin_of_hypotheses_H_E_alt` | 47,836 | VWin holds, that is, VWinAt ψ 401 holds for every primitive Dirichlet character ψ | low |
| 33 | · `galoisLocalGlobalStrong_recParameter` | 51,784 | Row0b recT holds, that is, every π over a CM field with IsRegAlg and PolarizedPair has some r, wt and HT with PropsB recT π ι r wt HT | medium |
| 34 | · · `galoisRepresentations_of_thetaLift` | 48,992 | Row0b recT holds, that is, every π over a CM field with IsRegAlg and PolarizedPair has some r, wt and HT with PropsB recT π ι r wt HT | medium |
| 35 | · · · `geoOne_holds` | 43,403 | GeoOne holds, a universally quantified statement whose own hypotheses and three-part conclusion are described in the entry of line 35, with each part … | medium |
| 36 | · · · · `geometric_realization_of_weight_one` | 41,443 | GeoOne holds, which reads as follows. For all E, Ω, l, ι, odd a, d with FieldOK E l d, x in E with x² = −d, T with NonSplitSet T, primes w₀ and v' … | medium |
| 37 | · · · · · `steps_holds` | 26,301 | all seventeen fields of Steps hold, namely RepEx, ESStep, CrysStep, JumpStep, PhiStep, CutStep, TwES, TwCrys, TwJ, TwPhi, PhiOf, SatCard, JumpsOf, … | low |
| 38 | · · · · · `kodaira_spencer_of_weight_one` | 11,850 | all six fields of KSAll hold, namely StdEx, KSEx, KSNice, KSGood, KSCong and KSHodge | medium |

## The lines

### Line 1, `everyCharacter`

The head is `UpperTheory.FinalTheorems.everyCharacter`, in the module Development › Automorphic Arithmetic › Character Boxes › Main Conclusion. The line gathers 760,227 declarations and is the top of the outline. Folded into the line is the wrapper `LFunction_ne_zero_of_half_lt_re`.

The theorem asserts, with no premises, the proposition that the code calls EveryCharacter. Unfolded, it says that for every nonzero natural number N, every Dirichlet character χ of level N with complex values and every complex number s with real part greater than 1/2, if χ is not the trivial character or s is not 1, then the library value DirichletCharacter.LFunction χ s is not zero. A wrapper theorem in the module Main, named LFunction_ne_zero_of_half_lt_re, is folded into this line and asserts a proposition called DirichletLNonvanishingRightOfHalf whose body the dossier does not show.

- Conclusion. For all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1), the value LFunction χ s is nonzero.

```
∀ N ∈ ℕ with N ≠ 0, ∀ χ a Dirichlet character mod N with values in ℂ, ∀ s ∈ ℂ, 1/2 < Re(s) ⇒ (χ ≠ 1 ∨ s ≠ 1) ⇒ LFunction(χ, s) ≠ 0
```

The reading does not open the names `DirichletCharacter ℂ N`, `DirichletCharacter.LFunction` and `DirichletLNonvanishingRightOfHalf`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that LFunction is the analytically continued Dirichlet L-function, in which case the statement says no Dirichlet L-function has a zero with real part above 1/2, a form of the generalized Riemann hypothesis that includes the Riemann zeta function at N = 1, and the wrapper name suggests it restates the same claim.

The reader's confidence is high. The statement of the head and the one definition it names are shown in full, and the names of the standard library remain unfolded. The proposition DirichletLNonvanishingRightOfHalf of the wrapper also remains unfolded in the dossier. The dossier shows nothing about the proof or the axioms it relies on.

The check found no error in this reading.

### Line 2, `everyCharacter_of_row`

The head is `UpperTheory.FinalTheorems.everyCharacter_of_row`, in the module Development › Automorphic Arithmetic › Character Boxes › Main Conclusion. The line gathers 577,248 declarations and hangs from line 1, `everyCharacter`.

The theorem says that if the proposition Row0b holds for the notion Rc that sends a pair (h, rc) to the condition IsRecT h rc, then EveryCharacter holds. The premise Row0b says that for every CM number field E with algebraic closure Ω, every prime l, every ring isomorphism ι from Qbar l to ℂ, every natural number a ≥ 1, every π of type CuspSub E a and every χ of type HChar over the maximal real subfield of E, if the class of π satisfies a condition that the code calls IsRegAlg and the pair (π, χ) satisfies PolarizedPair, then there exist a group homomorphism r from the automorphism group of Ω over E to GL_a(Qbar l), an integer wt and a function HT from the ring embeddings of E into Qbar l to multisets of integers such that PropsB Rc π ι r wt HT holds. The conclusion is the nonvanishing statement of line 1.

- Premise 1. Row0b holds with the notion Rc taken to be the map (h, rc) ↦ IsRecT h rc.
- Conclusion. EveryCharacter holds, that is, LFunction χ s ≠ 0 for all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1).

```
[∀ E CM number field, ∀ Ω algebraic closure of E, ∀ l prime, ∀ ι a ring isomorphism Qbar_l ≅ ℂ, ∀ a ≥ 1, ∀ π ∈ CuspSub(E, a), ∀ χ ∈ HChar(E⁺), IsRegAlg([π]) ⇒ PolarizedPair(π, χ) ⇒ ∃ r from Aut_E(Ω) to GL_a(Qbar_l), ∃ wt ∈ ℤ, ∃ HT, PropsB(IsRecT, π, ι, r, wt, HT)] ⇒ [∀ N ≠ 0, ∀ χ mod N, ∀ s ∈ ℂ, 1/2 < Re(s) ⇒ (χ ≠ 1 ∨ s ≠ 1) ⇒ LFunction(χ, s) ≠ 0]
```

The reading does not open the names `LawsT`, `PropsB`, `CuspSub E a`, `PolarizedPair`, `HChar` and `IsRegAlg`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the premise is the existence of l-adic Galois representations attached to regular algebraic polarized cuspidal automorphic representations of GL_a over CM fields, with local-global compatibility measured against a local Langlands reciprocity map, and that the conclusion is the generalized Riemann hypothesis for Dirichlet L-functions.

The reader's confidence is medium. The outer shape of the premise and the whole conclusion are visible, but the conditions inside PropsB, CuspSub and PolarizedPair, and LawsT, a name inside the body of IsRecT, rest on names without bodies and eight definitions were left out.

The check found no error in this reading.

### Line 3, `every_character_of_literature_of_vWin`

The head is `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Every Character Of Literature Of V Win. The line gathers 506,214 declarations and hangs from line 2, `everyCharacter_of_row`.

The theorem says that if the bundle OpenLiteratureStatements holds and the proposition VWin holds, then EveryCharacter holds. The bundle has three fields, of which the first and third are both the proposition Row and the second is RecTExists, which says that for every number field E, algebraic closure Ω, valuation subring A of Ω and prime w of the integers of E with a proof h of IsPlaceOver A w, there exists a map rc satisfying IsRecT h rc. VWin says that for every primitive Dirichlet character ψ the condition VWinAt ψ 401 holds, and the display below unfolds VWinAt, with the constants 401 and 1/52, the exponent 2 and an exponent 1/J for some J ≥ 1.

- Premise 1. OpenLiteratureStatements holds, that is, Row holds (listed twice under two field names) and RecTExists holds.
- Premise 2. VWin holds, that is, VWinAt ψ 401 holds for every ψ of type PChar.
- Conclusion. EveryCharacter holds, that is, LFunction χ s ≠ 0 for all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1).

```
[Row ∧ RecTExists ∧ Row] ∧ [∀ ψ ∈ PChar, ∀ eps ∈ ℝ, 0 < eps ⇒ eps < 1/52 ⇒ ∀ e from ℝ to ℕ, (∀ x ≥ 1, PageN(eps, x, e(x))) ⇒ ∃ J ≥ 1, ∃ X0, ∀ X ≥ X0, ∀ q, d ∈ ℕ, WinPair(eps, X^(1/J), q, d) ⇒ ∃ Y, X^(1/J) ≤ Y ∧ Y^2 ≤ X ∧ ∀ x, Y ≤ x ⇒ x ≤ Y^2 ⇒ VAt(ψ, eps, 401, q, d, e(x), x)] ⇒ [∀ N ≠ 0, ∀ χ mod N, ∀ s ∈ ℂ, 1/2 < Re(s) ⇒ (χ ≠ 1 ∨ s ≠ 1) ⇒ LFunction(χ, s) ≠ 0]
```

The reading does not open the names `Row`, `RecTExists`, `PageN`, `WinPair` and `VAt`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The field names suggest that the first premise collects three results expected from the literature (a local-global compatibility result attributed to Caraiani, existence of a local Langlands reciprocity map, and Galois representations for polarized pairs) and that VWin is an analytic estimate holding on a window of scales with the constant 401, though the dossier shows that the first and third fields are literally the same proposition.

The reader's confidence is medium. The logical shape of both premises and the whole conclusion are shown, but Row0b, IsRecT, PageN, WinPair and VAt appear without bodies.

The check found no error in this reading.

### Line 4, `every_character_of_theta_integrals_local_matching`

The head is `UpperTheory.Lit.every_character_of_theta_integrals_local_matching`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Siegel Eisenstein Second Term Hypotheses. The line gathers 315,443 declarations and hangs from line 3, `every_character_of_literature_of_vWin`.

The theorem says that seven premises together imply EveryCharacter. The premises are the bundle UnitaryGroupThirdPlaceHypotheses, the bundle ThetaLocalInputs, the proposition ThetaIntegralsAgree, the proposition LocalMatching, the proposition CovolumeBoundOfX, the proposition RecTExists and the proposition VWin. The conclusion is that LFunction χ s ≠ 0 for every nonzero N, every complex Dirichlet character χ of level N and every complex s with real part above 1/2 such that χ ≠ 1 or s ≠ 1.

- Premise 1. UnitaryGroupThirdPlaceHypotheses holds, a bundle of at least 28 named propositions whose listing is cut.
- Premise 2. ThetaLocalInputs holds, a bundle of at least 29 named propositions whose listing is cut.
- Premise 3. ThetaIntegralsAgree holds, a conjunction of three statements phrased with Decay, IsMatched, OneConst, Coinv, StepBeta and StepAlpha.
- Premise 4. LocalMatching holds, that is, every IsTriple datum admits some R and Rf with IsMatched.
- Premise 5. CovolumeBoundOfX holds, a statement of the form Closed FamHyp (…) with a constant C0 ≥ 0.
- Premise 6. RecTExists holds, that is, for every number field E, algebraic closure Ω, valuation subring A, prime w and h with IsPlaceOver A w there is an rc with IsRecT h rc.
- Premise 7. VWin holds, that is, VWinAt ψ 401 holds for every ψ of type PChar.
- Conclusion. EveryCharacter holds, that is, LFunction χ s ≠ 0 for all N ≠ 0, all χ of level N and all complex s with Re(s) > 1/2 and (χ ≠ 1 or s ≠ 1).

```
UnitaryGroupThirdPlaceHypotheses ∧ ThetaLocalInputs ∧ ThetaIntegralsAgree ∧ LocalMatching ∧ CovolumeBoundOfX ∧ RecTExists ∧ VWin ⇒ [∀ N ≠ 0, ∀ χ mod N, ∀ s ∈ ℂ, 1/2 < Re(s) ⇒ (χ ≠ 1 ∨ s ≠ 1) ⇒ LFunction(χ, s) ≠ 0], where LocalMatching is [∀ number fields F, E with E an F-algebra, ∀ σ an F-algebra map E → E, ∀ B ∈ Base(F, E), ∀ a, a' ∈ ℕ, ∀ G ∈ Geo(σ, a, a'), ∀ X ∈ Chars(F, E), ∀ om, om', IsTriple(B, G, X, om, om') ⇒ ∃ R, Rf, IsMatched(B, G, X, om, om', R, Rf)] and CovolumeBoundOfX is [∃ ε1 > 0, ∀ eps, 0 < eps ≤ ε1 ⇒ ∃ K ∈ TransportedAlt, ∀ Fm ∈ FamP(eps), ∀ CH ∈ ℝ, FamHyp(Fm) ⇒ Large(Fm, K, CH) ⇒ ∃ C0 ≥ 0, EventuallyAtAllPoints(Fm, p ↦ ∀ C ≥ C0, L3((p.S false), p.N C CH))]
```

The reading does not open the names `UnitaryGroupThirdPlaceHypotheses`, `ThetaLocalInputs`, `ThetaIntegralsAgree`, `LocalMatching`, `CovolumeBoundOfX`, `FamHyp`, `RecTExists`, `VWin` and `D7`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the first two premises collect published theorems from automorphic forms and representation theory, that the next three are statements about theta integrals, local matching and a covolume bound, that RecTExists is existence of a local Langlands reciprocity map and that VWin is an analytic window estimate, all combined to yield the generalized Riemann hypothesis for Dirichlet L-functions.

The reader's confidence is medium. The list of premises and the conclusion are fully visible, but two premise bundles are cut, most of the inner conditions have no bodies and 44 definitions were left out.

The check found no error in this reading.

### Line 5, `nonempty_hyps_definite_side_of_closed_bound`

The head is `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Siegel Eisenstein Second Term Hypotheses. The line gathers 266,135 declarations and hangs from line 4, `every_character_of_theta_integrals_local_matching`.

The theorem says that seven premises together imply that the type HypsAlt S0.NL DefiniteSideCondition is nonempty, which means that at least one record of that type exists. The first six premises are UnitaryGroupThirdPlaceHypotheses, ThetaLocalInputs, ThetaIntegralsAgree, LocalMatching, CovolumeBoundOfX and RecTExists (with its proof named hL). The seventh premise says that for every real number cDep the condition LinkedAt holds for the parameters parametersOfDependence hL cDep and for the rule that sends a slot Q and linkage L to SlotNormCondition Q L N, where N is the property of a family class 𝒞 given by Closed 𝒞 (Fm ↦ BoundAtTwoThreeFamilyFonAlt Fm).

- Premise 1. UnitaryGroupThirdPlaceHypotheses holds, a bundle of named propositions whose listing is cut.
- Premise 2. ThetaLocalInputs holds, a bundle of named propositions whose listing is cut.
- Premise 3. ThetaIntegralsAgree holds.
- Premise 4. LocalMatching holds.
- Premise 5. CovolumeBoundOfX holds.
- Premise 6. RecTExists holds, with proof hL that is used in the next premise.
- Premise 7. For every real cDep, LinkedAt (parametersOfDependence hL cDep) (Q, L ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 (Fm ↦ BoundAtTwoThreeFamilyFonAlt Fm))) holds.
- Conclusion. There exists at least one record of type HypsAlt S0.NL DefiniteSideCondition.

```
UnitaryGroupThirdPlaceHypotheses ⇒ ThetaLocalInputs ⇒ ThetaIntegralsAgree ⇒ LocalMatching ⇒ CovolumeBoundOfX ⇒ ∀ hL a proof of RecTExists, [∀ cDep ∈ ℝ, LinkedAt(parametersOfDependence(hL, cDep), (Q, L) ↦ SlotNormCondition(Q, L, 𝒞 ↦ Closed(𝒞, Fm ↦ BoundAtTwoThreeFamilyFonAlt(Fm))))] ⇒ HypsAlt(NL, DefiniteSideCondition) ≠ ∅, where NL(𝒞) is Closed(𝒞, Fm ↦ LinkN(Fm)) and BoundAtTwoThreeFamilyFonAlt(Fm) is [∃ C, x0 ∈ ℝ, ∀ x ≥ x0 with Fm.x1 < x, ∀ i, HW, F, a CmpOf datum, X, C₂, SetupAlt(Fm.L x i, nch, HW, X, C₂) ⇒ BoundAtTwoThree(Fm.L x i, X.ρ, C)]
```

The reading does not open the names `HypsAlt N DR`, `S0.NL`, `DefiniteSideCondition`, `LinkedAt p r`, `SlotNormCondition Q Lk N`, `parametersOfDependence hL cDep`, `BoundAtTwoThreeFamilyFonAlt Fm`, `CovolumeBoundOfX`, `LocalMatching`, `ThetaIntegralsAgree`, `RecTExists`, `UnitaryGroupThirdPlaceHypotheses` and `ThetaLocalInputs`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that this is an intermediate step which, from published automorphic inputs, theta integral identities, a covolume bound, a local Langlands map and a uniform bound called BoundAtTwoThree along linked families, assembles a package of hypotheses for a definite unitary group side that the parent theorem then uses.

The reader's confidence is low. The order of premises and the outer form of the conclusion are visible, but HypsAlt, DefiniteSideCondition and both premise bundles are cut, the seventh premise rests on names without bodies and 104 definitions were left out.

The check found no error in this reading.

### Line 6, `hypotheses_nonempty_of_unramified_exponents_alt`

The head is `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Hypotheses Nonempty Of Unramified Exponents. The line gathers 89,671 declarations and hangs from line 5, `nonempty_hyps_definite_side_of_closed_bound`.

Assume a bundle of named hypotheses that the code calls UnitaryGroupThirdPlaceHypotheses, a condition that the code calls RowRat, and a proof hL of the statement RecTExists. Then for every real number cDep and every predicate A of the kind AtP, if A satisfies EvLgG and three conditions of the form LinkedAt hold, there exists at least one object of the record type HypsAlt built from the family condition NL and the condition DefiniteSideCondition. The first LinkedAt premise uses the parameters parametersOfDependence hL cDep, and the other two use the parameters built from extensionWithOrigin hL cDep enlarged by A.

- Premise 1. The proposition UnitaryGroupThirdPlaceHypotheses holds, which is a record of many separately named propositions.
- Premise 2. The proposition RowRat holds.
- Premise 3. hL is a proof of RecTExists, which says that for every number field E, every algebraic closure Ω of E, every valuation subring A of Ω, every height one prime w of the ring of integers of E and every proof h of a condition that the code calls IsPlaceOver A w, there exists rc with a condition that the code calls IsRecT h rc.
- Premise 4. cDep is any real number and A is any predicate of type AtP, that is, a rule that assigns a truth value to a context K, a base B, an element of Fr B.toPre and an element of TwDat B.
- Premise 5. EvLgG A holds, which unfolds to EvG applied to the map sending K to large₂ K (A K).
- Premise 6. LinkedAt holds for the parameters parametersOfDependence hL cDep and the row condition that sends a slot Q and a linkage L to SlotNormCondition Q L N₀, where N₀ sends a family class 𝒞 to Closed 𝒞 applied to the property BoundAtTwoThreeFamilyFonAlt.
- Premise 7. LinkedAt holds for the parameters parametersOfExtension (extensionWithAtProperty hL (extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry) and the row condition FunctionalCondition.
- Premise 8. LinkedAt holds for the same second set of parameters and the row condition CovolumeBoundThirdPlaceSeries.
- Conclusion. The type HypsAlt NL DefiniteSideCondition is nonempty, that is, at least one record of that type exists.

```
UnitaryGroupThirdPlaceHypotheses ⇒ RowRat ⇒ ∀ hL ∈ RecTExists, ∀ cDep ∈ ℝ, ∀ A ∈ AtP, EvLgG(A) ⇒ LinkedAt(parametersOfDependence(hL, cDep), (Q, L) ↦ SlotNormCondition(Q, L, 𝒞 ↦ Closed(𝒞, (Fm, _) ↦ BoundAtTwoThreeFamilyFonAlt(Fm)))) ⇒ LinkedAt(p, FunctionalCondition) ⇒ LinkedAt(p, CovolumeBoundThirdPlaceSeries) ⇒ Nonempty(HypsAlt(NL, DefiniteSideCondition)), where p = parametersOfExtension(extensionWithAtProperty(hL, extensionWithOrigin(hL, cDep), A), SExt.none, geoCl(anyGeometry)) and NL(𝒞) = Closed(𝒞, (Fm, _) ↦ LinkN(Fm))
```

The reading does not open the names `UnitaryGroupThirdPlaceHypotheses`, `RowRat`, `EvLgG`, `LinkedAt`, `parametersOfDependence`, `extensionWithOrigin`, `geoCl anyGeometry`, `SlotNormCondition`, `BoundAtTwoThreeFamilyFonAlt`, `FunctionalCondition`, `CovolumeBoundThirdPlaceSeries`, `HypsAlt`, `NL` and `DefiniteSideCondition`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that a list of published theorems about automorphic forms on unitary groups, together with a local Langlands reciprocity statement and three row conditions on constructed parameters, yields the full hypothesis package needed by a later stage, but the dossier does not show enough to confirm this reading.

The reader's confidence is medium. The shape of the statement and the definition of Closed are visible, but Lg1, Row, EvG, the fields of the hypothesis bundle and most of HypsAlt are cut off or not shown.

The check found no error in this reading.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 3 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 1 finding on it, and the text was changed in 1 place. A check of the changed text then found no error.

Suppose the bundle of hypotheses that the code calls UnitaryGroupThirdPlaceHypotheses holds, and suppose the condition that the code calls RowRat holds. Then the following is claimed for every proof hL of the statement RecTExists, every real number cDep and every predicate A on quadruples (context K, base B, frame f, twisting data T). If A satisfies the condition that the code calls EvLgG, if the parameter record built from hL and cDep is linked to the relation that sends a slot Q and a linkage L to SlotNormCondition Q L N, which is Row Q L applied to the map sending a family class 𝒜 to N (D3 3 𝒜), where N says of a class that it is closed for the condition BoundAtTwoThreeFamilyFonAlt, and if the parameter record built by also attaching the origin data and the property A is linked both to the test FunctionalCondition and to the test CovolumeBoundThirdPlaceSeries, then there is at least one record of the type HypsAlt NL DefiniteSideCondition. In words, under these premises a hypothesis package exists for the class property NL and the definite side condition DefiniteSideCondition.

- Premise 1. The bundle UnitaryGroupThirdPlaceHypotheses holds, which the glossary reads as the conjunction of 60 named propositions, most of them stated as published results.
- Premise 2. The condition RowRat holds, which is a condition that the code calls StepW applied to Start and to a long implication ending in the condition that the code calls Formalism.IndefR.Rat.RowTest of z.R.toCx3 z.F.
- Premise 3. hL is any proof of RecTExists, which says that for every number field E, every algebraic closure Ω of E, every valuation subring A of Ω and every finite place w of E with A lying over w, there exists a map rc with the property IsRecT.
- Premise 4. cDep is any real number.
- Premise 5. A is any predicate on quadruples (K, B, f, T) of a context, a base, a frame and twisting data.
- Premise 6. A satisfies EvLgG, meaning EvG holds of the map sending K to the statement large₂ K (A K).
- Premise 7. LinkedAt holds for the parameter record parametersOfDependence hL cDep and the relation that sends a slot Q and a linkage L to SlotNormCondition Q L N, where N says of a family class 𝒞 that Closed 𝒞 holds for BoundAtTwoThreeFamilyFonAlt.
- Premise 8. LinkedAt holds for the parameter record p′ = parametersOfExtension (extensionWithAtProperty hL (extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry) and the row test FunctionalCondition.
- Premise 9. LinkedAt holds for the same parameter record p′ and the row test CovolumeBoundThirdPlaceSeries.
- Conclusion. There exists at least one record of the type HypsAlt NL DefiniteSideCondition.

This reading opens `LinkedAt (Lg1, KPx)`, `SlotNormCondition (Row)`, `parametersOfDependence (extensionWithList)`, `BoundAtTwoThreeFamilyFonAlt`, `UnitaryGroupThirdPlaceHypotheses (all 60 fields)`, `RecTExists (IsRecT)`, `BundleCondition` and `D7`.

It does not open `EvG`, `large₂`, `LinkN` and `Row, Lg1, LargeBaseCondition, IsBuiltE, IsGoodE, BundleLinkage, EvWC, StepW, RowTest, GeoCl, OriginData, extensionWithList`.

The reader's confidence is low. The outer logical shape is fully visible, but the conclusion HypsAlt and DefiniteSideCondition are cut, and key notions such as EvG, large₂, Row, EvWC, StepW and LinkN have no body, so what the premises and the conclusion really demand cannot be seen.

### Line 7, `allRows_of_open0_alt`

The head is `GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Link R Of Is Linked. The line gathers 34,967 declarations and hangs from line 6, `hypotheses_nonempty_of_unramified_exponents_alt`.

Assume nine named propositions, six of them stated in the namespace of published theorems, one called SiegelWeilUnitaryConvergent from the namespace HeckeCharacterZeroLocus.SiegelWeilU, and two called SurjectiveOntoX and LambdaLowerBound₂. Then for every proof hL of RecTExists, every extension N, every S of type SExt, every geometry predicate Γ and every property NN of family classes, write p for the parameter record parametersOfExtension N S Γ. If p satisfies OpenParameterStatements and LinkedAt holds for p with each of the three row conditions CovolumeBoundThirdPlaceSeries, FunctionalCondition and SlotNormCondition with NN, then the record of conditions AllRowsAlt holds for KPx, the two slots IsBuiltE p.s and IsGoodE p.s, the linkage BundleLinkage p, NN and DefiniteSideCondition.

- Premise 1. GlobalArtinReciprocity holds, which says that for every number field E with algebraic closure Ω there is a monoid homomorphism art from Ideles E to Gab E Ω with a condition that the code calls IsGlobalArtin.
- Premise 2. SiegelWeilUnitaryConvergent holds, which says that for all number fields F and E with E an F-algebra, every F-algebra map σ from E to E with IsCMExt F E σ, every natural number M and every M by M matrix J over E with IsHermND σ J, a condition that the code calls SiegelWeilAt F E σ M J holds.
- Premise 3. DiscreteSeriesCover holds, which says that for all natural numbers p and q with 1 ≤ p + q and every T of type GrpData p q there is a family D of objects of type DSRep T indexed by maps lam from Ix p q to ℚ with IsParam lam, such that HasTypes holds of D lam and lam and every R of type DSRep T satisfies UnitEquiv R (D lam) for some lam.
- Premise 4. HarishChandraModules holds, which is the conjunction of HarishChandraModulesOn T for all p, q with 1 ≤ p + q and all T of type GrpData p q, and a condition that the code calls KFiniteAnalyticUJ.
- Premise 5. CuspRapidDecay holds, which says that for every datum D and suitable families θ, V, e, every complex function φ on GA D V that satisfies IsAutFun, IsSmoothInf, IsUnifModerate and IsCuspFun also satisfies IsRapidDecay.
- Premise 6. CasselmanWallach holds, a statement that, for every natural number n and every ε from Fin n to Bool, for a map σ from complex matrices to continuous linear maps of a Hilbert space H with IsURepOn (UJset ε) σ and IsIrredOn (UJset ε) σ, and for maps π and dπ from complex matrices to continuous linear maps of a complete space E with seminorms p and IsSmoothModRep ε p π dπ, every linear map T₀ from H to E with IsGKMap ε σ π dπ T₀ has a linear map T that agrees with T₀ on vectors with IsKFin, satisfies IsSmoothGMap, is unique on smooth vectors, has closed image of the smooth vectors, and, when T₀ is nonzero on some IsKFin vector, admits, for every list S of lists of matrices in lieSet ε, a continuous seminorm q with sobNorm σ S w ≤ q (T w) for every w with SmoothVec (lieSet ε) σ w.
- Premise 7. DiscreteSeriesClassification holds, a statement whose body the dossier shows and whose details this reading leaves out.
- Premise 8. SurjectiveOntoX holds, which is Closed FamHyp applied to the property that DIVinN Fm implies the existence of C0 ≥ 0 such that eventually at points p with a condition called More, a condition called ON holds for every C ≥ C0.
- Premise 9. LambdaLowerBound₂ holds, which is Closed FamHyp applied to the property that eventually at points p a condition called L6 holds for every C.
- Premise 10. hL is a proof of RecTExists, N is of type NormChoiceExtension hL, S is of type SExt, Γ is a predicate of type GeoP, and NN is a property of family classes.
- Premise 11. OpenParameterStatements p holds for p = parametersOfExtension N S Γ, which is the conjunction of twelve LinkedAt p statements with the row conditions SlotPrimitivityCondition, SlotLambdaPrimeCondition, SlotDivisorCondition, SlotDecompositionPointCondition, SlotSelectionJumpCondition, Row_tie_alt, RowLabelCondition, RowGoodnessCondition, GeometricWeakCompatibility', RowMultiplicityCondition, RowKappaCondition and RowDefectCondition.
- Premise 12. LinkedAt p CovolumeBoundThirdPlaceSeries holds.
- Premise 13. LinkedAt p FunctionalCondition holds.
- Premise 14. LinkedAt p holds with the row condition that sends a slot Q and a linkage L to SlotNormCondition Q L NN.
- Conclusion. AllRowsAlt KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) NN DefiniteSideCondition holds, with p = parametersOfExtension N S Γ.

```
GlobalArtinReciprocity ⇒ SiegelWeilUnitaryConvergent ⇒ DiscreteSeriesCover ⇒ HarishChandraModules ⇒ CuspRapidDecay ⇒ CasselmanWallach ⇒ DiscreteSeriesClassification ⇒ SurjectiveOntoX ⇒ LambdaLowerBound₂ ⇒ ∀ hL ∈ RecTExists, ∀ N ∈ NormChoiceExtension(hL), ∀ S ∈ SExt, ∀ Γ ∈ GeoP, ∀ NN ∈ (FamClass → Prop), with p = parametersOfExtension(N, S, Γ), OpenParameterStatements(p) ⇒ LinkedAt(p, CovolumeBoundThirdPlaceSeries) ⇒ LinkedAt(p, FunctionalCondition) ⇒ LinkedAt(p, (Q, L) ↦ SlotNormCondition(Q, L, NN)) ⇒ AllRowsAlt(KPx, IsBuiltE(p.s), IsGoodE(p.s), BundleLinkage(p), NN, DefiniteSideCondition)
```

The reading does not open the names `GlobalArtinReciprocity`, `SiegelWeilUnitaryConvergent`, `DiscreteSeriesCover`, `HarishChandraModules`, `CuspRapidDecay`, `CasselmanWallach`, `DiscreteSeriesClassification`, `SurjectiveOntoX`, `LambdaLowerBound₂`, `FamHyp`, `LinkedAt`, `SlotNormCondition`, `CovolumeBoundThirdPlaceSeries`, `FunctionalCondition`, `AllRowsAlt`, `KPx`, `IsBuiltE and IsGoodE`, `BundleLinkage` and `DefiniteSideCondition`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that classical results on automorphic forms and discrete series, together with an open list of row conditions at chosen parameters, deliver every row of a large table of conditions, but the dossier does not show what the rows mean.

The reader's confidence is medium. The premises and the form of the conclusion are fully visible, but Lg1, Row, the tail of AllRowsAlt and nearly all the inner conditions are not shown or are cut off.

The check found three errors in the first version of this reading. The text above is the corrected version, which passed the check after two rounds of correction.

- A says "seven of them stated as published theorems", but the Lean text puts only six of the nine premises in the namespace GlobalTheory.Published, and SiegelWeilUnitaryConvergent is named HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent.
- A says "a group homomorphism art from Ideles E to Gab E Ω", but the Lean text of GlobalArtinReciprocity writes "art : Ideles E →* Gab E Ω", which is a monoid homomorphism, and the dossier does not show that the two types are groups.
- A describes CasselmanWallach as a statement about "a linear map T₀ from a Hilbert space H to a complete space E with a condition IsGKMap" and does not say that anything is left out, but the Lean text also requires "IsURepOn (UJset ε) σ", "IsIrredOn (UJset ε) σ" and "IsSmoothModRep ε p π dπ" before the conclusion.

A second model, Gemini, checked this reading again. 3 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 2 errors in this reading and, after they were corrected, 5 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 7 findings on it, and the text was changed in 7 places. A check of the changed text then found no error.

The theorem assumes nine propositions taken as hypotheses. Six of them lie in the namespace GlobalTheory.Published and are named GlobalArtinReciprocity, DiscreteSeriesCover, HarishChandraModules, CuspRapidDecay, CasselmanWallach and DiscreteSeriesClassification, one is HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent, and two are the propositions SurjectiveOntoX and LambdaLowerBound₂, each of the form Closed FamHyp. Under these hypotheses it considers any proof hL of the proposition RecTExists, any norm choice extension N over hL, any S of type SExt, any Γ of type GeoP and any property NN of family classes, and it lets p be the parameter record parametersOfExtension N S Γ, which is the four-part record made of RX, N, S and Γ. If p satisfies every part of the record OpenParameterStatements, and LinkedAt holds at p for the three row conditions CovolumeBoundThirdPlaceSeries, FunctionalCondition and the slot norm condition for NN, then the record AllRowsAlt holds. That record is built from the base predicate KPx, the slots IsBuiltE p.s and IsGoodE p.s, the linkage BundleLinkage p, the property NN and the side condition DefiniteSideCondition. In unfolded form, AllRowsAlt says that each of a long list of row conditions (class count bound, J-invariant, instance rank, divisor, primitivity, Lp, order, torsion-free and others) is linked at p in the same sense as LinkedAt. The list is cut in the dossier, so further fields that may use NN and DefiniteSideCondition are not visible.

- Premise 1. GlobalArtinReciprocity, which says that for every number field E and every algebraic closure Ω of E there is a group homomorphism art from Ideles E to Gab E Ω that satisfies IsGlobalArtin.
- Premise 2. SiegelWeilUnitaryConvergent, which says that for all number fields F and E with E an F-algebra, every F-algebra map σ from E to E with IsCMExt F E σ, every natural number M and every M×M matrix J over E with IsHermND σ J, the condition SiegelWeilAt F E σ M J holds.
- Premise 3. DiscreteSeriesCover, which says that for all natural numbers p and q with 1 ≤ p + q and every T of type GrpData p q there is a map D from the functions lam of type Ix p q → ℚ that satisfy IsParam lam to DSRep T, so that HasTypes (D lam) lam.1 holds for every such lam and every R of type DSRep T satisfies UnitEquiv R (D lam) for some lam.
- Premise 4. HarishChandraModules, which says that HarishChandraModulesOn T holds for every p, q with p+q ≥ 1 and every T of type GrpData p q, and that KFiniteAnalyticUJ holds.
- Premise 5. CuspRapidDecay, which says that for every D of type D7 and data θ, V and e meeting IsInfFam and IsExpFam, every function φ from GA D V to ℂ that satisfies IsAutFun V φ, IsSmoothInf V e φ, IsUnifModerate θ V e φ and IsCuspFun V φ satisfies IsRapidDecay θ V φ.
- Premise 6. CasselmanWallach, a long statement about a linear map T₀ with IsGKMap from a complex Hilbert space H carrying σ with IsURepOn and IsIrredOn for UJset ε to a complete Hausdorff uniform space E with seminorms p and maps π and dπ satisfying IsSmoothModRep. It asks for a complex linear map T from H to E that agrees with T₀ on all vectors satisfying IsKFin ε σ, satisfies IsSmoothGMap ε σ p π T, agrees on all w satisfying SmoothVec (lieSet ε) σ w with any complex linear map T' from H to E meeting those two conditions, has a closed image of the set of w satisfying SmoothVec (lieSet ε) σ w, and, whenever there exists v satisfying IsKFin ε σ v with T₀ v ≠ 0, gives for every list S of lists of matrices in lieSet ε a continuous seminorm q on E satisfying sobNorm σ S w ≤ q (T w) for all w satisfying SmoothVec (lieSet ε) σ w.
- Premise 7. DiscreteSeriesClassification, which says that for every natural number n there are complex inner product spaces H ε lam and maps π ε lam from n by n complex matrices to continuous linear maps of H ε lam with two properties. First, for every ε of type Fin n → Bool and every strictly decreasing lam of type Fin n → ℝ with lam a − (n − 1)/2 an integer for all a, the space H ε lam is complete and nontrivial, π ε lam satisfies IsURepOn (UJset ε), IsIrredOn (UJset ε), IsSqIntOn ε and HasInfChar ε at lam, there is a unique submodule S with IsKTypeOf ε (π ε lam) (lam + rhoN ε − rhoC ε) S, and every μ and submodule S with IsKTypeOf ε (π ε lam) μ S has μ equal to lam + rhoN ε − rhoC ε plus a sum of the terms c a b • root a b with natural numbers c a b that are nonzero only when a < b. Second, for every ε and every complete nontrivial complex inner product space H' with a map σ satisfying IsURepOn (UJset ε), IsIrredOn (UJset ε) and IsSqIntOn ε there are a permutation s of Fin n with s a < s b whenever a < b and ε (s a) = ε (s b), a strictly decreasing mu with mu a − (n − 1)/2 an integer for all a, and a linear isometric equivalence T from H' onto H (ε ∘ s) mu with T (σ (g.submatrix s.symm s.symm) v) = π (ε ∘ s) mu g (T v) for all g in UJset (ε ∘ s) and all v.
- Premise 8. SurjectiveOntoX, which says that Closed FamHyp holds for the property sending Fm and CH to the statement that, whenever DIVinN Fm holds, there are a real C0 ≥ 0 and a real x0 such that for every x > Fm.x1 with x0 ≤ x, every i of type Fm.Ix x and every point p satisfying p.PointConditions' and More p, the condition (p.S false).ON (p.N C CH) holds for every C ≥ C0.
- Premise 9. LambdaLowerBound₂, which says that Closed FamHyp holds for the property sending Fm and CH to the statement that there is a real x0 such that for every x > Fm.x1 with x0 ≤ x, every i of type Fm.Ix x and every point p satisfying p.PointConditions', the condition (p.S true).L6 (p.N C CH) holds for every C.
- Premise 10. OpenParameterStatements p, which says that LinkedAt p r holds for each of twelve row conditions r (primitivity, lambda prime, divisor, decomposition point, selection jump, the alternative tie, label, goodness, geometric weak compatibility, multiplicity, kappa and defect).
- Premise 11. LinkedAt p CovolumeBoundThirdPlaceSeries.
- Premise 12. LinkedAt p FunctionalCondition.
- Premise 13. LinkedAt p applied to the relation that sends Q and L to SlotNormCondition Q L NN.
- Conclusion. AllRowsAlt KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) NN DefiniteSideCondition holds, where p is parametersOfExtension N S Γ.

This reading opens `D7`, `RecTExists`, `LinkedAt`, `SlotNormCondition`, `KPx` and `BundleCondition`.

It does not open `Lg1, LargeBaseCondition, EvLg`, `Row, EvWC, EvP`, `RX`, `row conditions inside AllRowsAlt and OpenParameterStatements` and `ON, L6, L3, FUN, KsExact, BundleWitness, IsGlobalArtin, SiegelWeilAt, IsRapidDecay, IsRecT`.

The reader's confidence is low. The logical shape of the statement is fully visible, but AllRowsAlt and DefiniteSideCondition are cut, and the meaning rests on many conditions with no visible body, such as Lg1, EvLg, Row, RX and most row conditions.

### Line 8, `at_choice_alt`

The head is `GlobalTheory.LocalRows.at_choice_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › At Choice. The line gathers 14,543 declarations and hangs from line 7, `allRows_of_open0_alt`. Folded into the line are the wrappers `lg1_sLp_sO_hTF` and `sLp_sO_hTF_of_siegelWeil`.

Assume the proposition SiegelWeilUnitaryConvergent. Then for every family class 𝒜 and every selection σ that assigns a BundleCondition record to each family in 𝒜, each x beyond the family's threshold x1 and each index i, three statements hold together, namely SelectionLpBound 𝒜 σ, SelectionOrderBound 𝒜 σ and H_hTF 𝒜. Two wrapper theorems folded into this line state, each under the same premise SiegelWeilUnitaryConvergent, three conditions with matching names, SlotLpCondition, SlotOrderCondition and SlotTorsionFreeCondition. One wrapper states them for every slot Q and every Lk of type LkT BundleCondition, and the other states them under the operator Lg1 for every predicate KP, every pair of slots Q and Q' and every Lk of type LkT BundleCondition. The dossier does not show the bodies of these three conditions, so it does not show that they state the same triple.

- Premise 1. hSW is a proof of SiegelWeilUnitaryConvergent, which says that for all number fields F and E with E an F-algebra, every F-algebra map σ from E to E with IsCMExt F E σ, every natural number M and every M by M matrix J over E with IsHermND σ J, the condition SiegelWeilAt F E σ M J holds.
- Premise 2. 𝒜 is any family class, that is, a predicate on families Fm of type FamP eps for every real eps.
- Premise 3. σ is any element of RawSel BundleCondition 𝒜, that is, a rule giving a BundleCondition record over (Fm.D x i, objAt Fm x hx i, Fm.Csz) for every family Fm in 𝒜, every real x with Fm.x1 < x and every index i in Fm.Ix x.
- Conclusion. SelectionLpBound 𝒜 σ and SelectionOrderBound 𝒜 σ and H_hTF 𝒜 all hold.

```
SiegelWeilUnitaryConvergent ⇒ ∀ 𝒜 ∈ FamClass, ∀ σ ∈ RawSel(BundleCondition, 𝒜), SelectionLpBound(𝒜, σ) ∧ SelectionOrderBound(𝒜, σ) ∧ H_hTF(𝒜), where SelectionLpBound(𝒜, σ) = LoopRowS(3, D3(3, 𝒜), sel_σ), SelectionOrderBound(𝒜, σ) = Closed(D3(3, 𝒜), (Fm, _) ↦ ∀ hc, TheoremSSelected(Fm, 3, sel_σ(Fm, hc))), H_hTF(𝒜) = Closed(D3(3, 𝒜), (Fm, _) ↦ TFrame(Fm, Fm.CYL + 1, 1/4, 3, 1/2, Fm.CTu, 3))
```

The reading does not open the names `SiegelWeilAt`, `FamP`, `BundleCondition`, `LoopRowS`, `TheoremSSelected`, `TFrame` and `D3`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that a convergent Siegel–Weil formula for unitary groups yields, for any selection of bundles, a row size bound, a bound on off-diagonal kernel terms and a torsion free frame condition, but only the inequality in TheoremSSelected and the inequality in TFrame are visible in the dossier.

The reader's confidence is medium. The statement, its single hypothesis and the outer layers of all three conclusions are shown with their constants, but OwnEv, D3, the hypotheses Hyp, Hyp0 and hyp and the quantities inside the bounds are not shown.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found 2 errors, which the text above corrects. A second such check found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 1 errors in this reading and, after they were corrected, 3 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 4 findings on it, and the text was changed in 4 places. A check of the changed text then found no error.

Assume the proposition that the code calls SiegelWeilUnitaryConvergent. That proposition says the following for all number fields F and E with E an algebra over F, and every automorphism σ of E that fixes F. If F is totally real, E is totally complex, E has degree 2 over F, and every complex embedding τ of E satisfies τ(σ x) = conj(τ x), then for every natural number M and every M by M matrix J over E with σ(J_ji) = J_ij for all i and j and det J ≠ 0, the two opaque conditions FinVol and SiegelDensities both hold. Under this assumption the theorem takes any family class 𝒜 and any raw selection σ, which assigns a BundleCondition record to every family Fm in 𝒜, every real x > Fm.x1 and every index i in Fm.Ix x, and it concludes three statements. The first is SelectionLpBound 𝒜 σ, which is LoopRowS with constant 3 for the class D3 3 𝒜 and the selection made of Fm.x1 and the STies data that the S fields of σ give. It says that for every function aF from lists of reals to reals, Closed holds on D3 3 𝒜 for the statement that every proof hc of D3 3 𝒜 Fm gives OwnEv at Fm of the following. For all x with Fm.x1 < x and (sel Fm hc).1 ≤ x and all words u and u′ of (Fm.D x i).what₂.Word, the opaque conditions Cnt.Hyp, with the constants Fm.CYL + 1, 1/4, 3, 1/2, Fm.CTu, 3 and aF Fm.cOut, ConcTie and AbsConv together imply the opaque conditions RowBig and RowNotScalar. The second is SelectionOrderBound 𝒜 σ, which requires Closed on D3 3 𝒜 for the statement that for every proof hc of D3 3 𝒜 Fm, TheoremSSelected holds at Fm, 3 and the same selection. TheoremSSelected says that OwnEv holds at Fm of the implication from the hypothesis AdmissibleBoundsFromSource.hyp, taken at Fm.D x i and Fm.L x i with the constants 3, C′, Cl, Fm.CYL + 1, 1/4, 3, 1/2 and Fm.CTu, to the bound ‖K0‖² ≤ (1 + 1/b⁶)·duS(u)·duS(u′)/Dstar for every x with Fm.x1 < x and s.1 ≤ x and all distinct words u ≠ u′. The third is H_hTF 𝒜, which requires Closed on D3 3 𝒜 for TFrame at Fm with the constants Fm.CYL + 1, 1/4, 3, 1/2, Fm.CTu and 3. TFrame says that OwnEv holds at Fm of the implication from the opaque hypothesis Cnt.Hyp0, taken at Fm.D x i and Fm.L x i with C′, Cl and those constants, to the inequality 1 ≤ Tr(D,w)·kaS(D)^(2·rS) for every w, where D is Fm.D x i.

- Premise 1. The global proposition SiegelWeilUnitaryConvergent holds.
- Premise 2. 𝒜 is a family class, meaning a predicate on families Fm of type FamP eps for every real eps.
- Premise 3. σ is a raw selection that gives, for every eps, every Fm with 𝒜 Fm, every real x with Fm.x1 < x and every i in Fm.Ix x, a record of type BundleCondition (Fm.D x i) (objAt Fm x hx i) Fm.Csz.
- Conclusion. SelectionLpBound 𝒜 σ and SelectionOrderBound 𝒜 σ and H_hTF 𝒜 all hold.

This reading opens `D7`, `Ranks (D.R, including m)`, `SData (D.s, including Del with Del > 0)`, `Des` and `WithChN`.

It does not open `FinVol`, `SiegelDensities`, `FamCore`, `OwnEv`, `Large`, `TransportedAlt`, `Cnt.Hyp, Cnt.Hyp0, AdmissibleBoundsFromSource.hyp`, `ConcTie, AbsConv, RowBig, RowNotScalar, epsL, ddC` and `Tr, kaS, duS, K0, tO`.

The reader's confidence is medium. The logical shape, the quantifiers, the constants 3, 1/4, 1/2 and CYL+1, and the definitions Closed, D3, LoopRowS, TheoremSSelected and TFrame are all visible, but the central operator OwnEv, the hypotheses Cnt.Hyp and AdmissibleBoundsFromSource.hyp, FinVol, SiegelDensities and most quantities inside the bounds have no visible bodies.

### Line 9, `offDiag`

The head is `GlobalTheory.CarrierGap.offDiag`, in the module Development › Abelian Variety Theory › Proofs › Flag Measures › Off K0 Closed. The line gathers 13,933 declarations and hangs from line 8, `at_choice_alt`.

Assume three global conditions that the code calls SWXS, RowNGP and RowsFinDim. Then for every class 𝒞 of parameter families and every selector sel on 𝒞, if every selected datum Fm.D x i is LocTied, and the conditions RanksRow 3 𝒞 and LoopRowS 3 𝒞 sel hold, then the off-diagonal bound TheoremSSelected Fm 3 (sel Fm hc) holds in the Closed sense on 𝒞. Unfolded, the bound says that for all large x, every index i and every pair of distinct words u ≠ u', the squared norm of the quantity K0 attached to (u, u') is at most (1 + 1/b^6) times duS(u)·duS(u')/Dstar, under a standing hypothesis with constants 3, C', Cl, Fm.CYL + 1, 1/4, 3, 1/2 and Fm.CTu.

- Premise 1. SWXS holds, which says that for every datum D and every HidaSetting X of D two conditions that the code calls SWa1 and StabilizerFirstChernCompatibility hold for the fields, the map cm.sig, rank n and matrix J of X.
- Premise 2. RowNGP holds, which says that for all reals Cg, cb, Cw, cT, CT, C0 with 0 < cb and 0 < cT there are C4 ≥ 0 and thresholds C'₀, Cl₀ such that for all C' ≥ C'₀ and Cl ≥ Cl₀ and all data satisfying Ties, Hyp0, Stand, ConcTie and AbsConv, a condition that the code calls RowNG holds with the numbers epsNG D large₂ C4 and ddC X Y u u'.
- Premise 3. RowsFinDim holds, which says that under listed hypotheses on an instance I, a Haar measure, a fundamental domain, a right regular action R, a locally constant function e supported in I.Kset, and unitary irreducible families σ with unit vectors w, the range of the composite operator Re∘T is a finite-dimensional complex vector space. This summary leaves out the hypotheses that introduce Re and T, which are I.IsRConvF μf fund R e Re and IsOpInt (muInf I) (fun g => R (g, 1)) (phInf I σ w dv) T, the condition IsFdeg on the numbers dv and the integrability of phLoc.
- Premise 4. 𝒞 is any property of parameter families FamP eps and sel is any function that gives a selection SSelF Fm for each family Fm in 𝒞.
- Premise 5. For every eps, every family Fm with a proof hc of 𝒞 Fm, every x with Fm.x1 < x and (sel Fm hc).1 ≤ x and every index i in Fm.Ix x, the datum Fm.D x i is LocTied, meaning that at every nonzero prime p of the ring of integers of its field host.F there exists a LocIso between the two local objects D.s.atP p and locC D p, where D stands for Fm.D x i.
- Premise 6. RanksRow 3 𝒞 holds, which is Closed 𝒞 applied to the condition RanksF Fm 3 (Fm.CYL + 1) (1/4) 3 (1/2) Fm.CTu.
- Premise 7. LoopRowS 3 𝒞 sel holds, which says that for every function aF from lists of reals to reals, in the Closed sense on 𝒞 and eventually in x, the hypotheses Hyp with constants C', Cl, Fm.CYL + 1, 1/4, 3, 1/2, Fm.CTu, 3 and aF(Fm.cOut), together with ConcTie and AbsConv, imply both RowBig and RowNotScalar with the numbers epsL(Fm.D x i) and ddC. This summary leaves out the binders hc, hx, h0, u and u' and the object (sel Fm hc).2 x hx h0 i, and the constants C' and Cl stand for sC' Fm and sCl Fm.
- Conclusion. Closed 𝒞 holds for the property that sends Fm to the statement that for every proof hc that Fm is in 𝒞 the condition TheoremSSelected Fm 3 (sel Fm hc) holds.

```
SWXS ⇒ RowNGP ⇒ RowsFinDim ⇒ ∀ 𝒞 ∀ sel ∈ SSel 𝒞, [∀ eps ∀ Fm ∈ FamP eps ∀ hc ∈ 𝒞 Fm ∀ x (Fm.x1 < x ∧ (sel Fm hc).1 ≤ x) ∀ i ∈ Fm.Ix x, LocTied(Fm.D x i)] ⇒ RanksRow 3 𝒞 ⇒ LoopRowS 3 𝒞 sel ⇒ Closed 𝒞 (Fm ↦ ∀ hc, TheoremSSelected Fm 3 (sel Fm hc)), where Closed 𝒞 P means ∃ ε1 > 0 ∀ eps (0 < eps ≤ ε1) ∃ K ∈ TransportedAlt ∀ Fm ∈ FamP eps ∀ CH ∈ ℝ, 𝒞 Fm ⇒ Fm.Large K CH ⇒ P Fm CH, and TheoremSSelected Fm 3 s means ∃ x0 ∀ x ≥ x0 ∀ i ∈ Fm.Ix x, hyp(Fm.D x i, Fm.L x i, 3, sC' Fm, sCl Fm, Fm.CYL+1, 1/4, 3, 1/2, Fm.CTu) ⇒ ∀ (Fm.x1 < x) (s.1 ≤ x) ∀ u ≠ u', ‖((s.2 x i).Y.tO u u').K0‖² ≤ (1 + ((Fm.L x i).sc.b⁶)⁻¹)·(duS u · duS u' / Dstar)
```

The reading does not open the names `FamP`, `hyp`, `RanksRow`, `LoopRowS`, `RowNGP`, `SWXS`, `ConcTie` and `D7`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest a bound on the off-diagonal entries of a kernel or Gram matrix indexed by words, derived from a Siegel–Weil type input (SWXS), a row non-degeneracy input and a finite-dimensionality statement for a space of automorphic forms, but the dossier does not show this.

The reader's confidence is medium. The logical shape, the constants and the final inequality are fully visible, but RowNG, RowBig, RowNotScalar, FamilyRanksHypothesis, Fm.Large, STies, StandingHypotheses and the object K0 are names without visible bodies and the records FamP and D7 are cut.

The check found no error in this reading.

A second model, Gemini, checked this reading again. 4 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found one error, which the text above corrects. A second such check found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 4 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 5 findings on it, and the text was changed in 5 places. A check of the changed text then found no error.

The theorem assumes three global statements, called SWXS, RowNGP and RowsFinDim. It then takes any class 𝒞 of parameter families and any selector sel for that class, and it adds three more assumptions. The first is that every datum Fm.D x i of every family in 𝒞 satisfies LocTied whenever x exceeds the family's base point x1 and is at least the selected threshold. The second is the rank condition RanksRow with constant 3. The third is the row condition LoopRowS with constant 3 and the selector sel. Under these assumptions the property Closed holds for 𝒞. This means there is ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is a constant package K for which every family Fm in 𝒞 that is large with respect to K and any CH satisfies TheoremSSelected Fm 3 (sel Fm hc). TheoremSSelected says that for all large enough x and every index i, whenever AdmissibleBoundsFromSource.hyp holds for Fm.D x i and Fm.L x i with the constants 3, sC' Fm, sCl Fm, Fm.CYL + 1, 1/4, 3, 1/2 and Fm.CTu, and whenever Fm.x1 < x and s.1 ≤ x hold, then for any two distinct words u ≠ u' the squared norm of the quantity K0 of (s.2 x hx h0 i).Y.tO u u' is at most (1 + 1/b^6) · duS(u) · duS(u') / Dstar.

- Premise 1. SWXS holds, meaning that for every D of type D7 and every Hida setting X over D, the two opaque conditions SWa1 and StabilizerFirstChernCompatibility hold for the field, CM and Hermitian data of X.
- Premise 2. RowNGP holds, meaning that for all real constants Cg, cb, Cw, cT, CT, C0 with cb > 0 and cT > 0 there is C4 ≥ 0 and thresholds C'₀ and Cl₀ such that for all C' ≥ C'₀ and Cl ≥ Cl₀ and every D, size datum large₂, Hida setting X, full datum Y and words u, u', the conditions Ties D, Hyp0, Stand D u u', ConcTie X Y and AbsConv of Y.tO u u' together imply RowNG of Y.tO u u' with tolerance epsNG D large₂ C4 = 2^(−(k − 2·rS − 5)) · exp(C4 · mR(D)^5 · f · log b), where k − 2·rS − 5 is a subtraction of natural numbers that is cut off at zero, so the first factor is 1 whenever k < 2·rS + 5 and with the number ddC X Y u u' = duC(u) · duC(u') / DstC.
- Premise 3. RowsFinDim holds, meaning that for every record I of type AutInst, every σ-finite Haar measure μf on I.Gf, every subset fund of I.GA with I.IsFundDom (I.muA μf) fund, every map R on I.GA with I.IsRightReg μf fund R, every locally constant complex function e on I.Gf that vanishes outside I.Kset with an operator Re satisfying I.IsRConvF μf fund R e Re, and every family over the infinite places v of I.F of complex Hilbert spaces H v, maps σ v satisfying IsURepOn and IsIrredOn on UJset (I.ε v), reals dv v satisfying IsFdeg for muG (I.ε v), unit vectors w v and integrable functions phLoc (σ v) (w v) (dv v), every continuous linear operator T on I.L2 μf fund that satisfies IsOpInt with the measure muInf I, the action g ↦ R (g, 1) and the function phInf I σ w dv has a finite-dimensional complex space HH I μf fund Re T.
- Premise 4. A class 𝒞 of parameter families is given (a class is a property of families FamP eps for each real eps).
- Premise 5. A selector sel for 𝒞 is given, which gives every family Fm in 𝒞 a pair made of a threshold x0 and, for each x > x1 with x ≥ x0 and each index i, an object of the opaque type STies for D x i.
- Premise 6. For every eps, every family Fm in 𝒞, every x with x1 < x and (sel Fm hc).1 ≤ x and every index i, the datum D x i satisfies LocTied, meaning that for every nonzero prime p of the ring of integers of the field host.F there exists a LocIso between the local datum (D.s.atP p) and the local datum locC D p that Examples₂.locAtC builds.
- Premise 7. RanksRow 3 𝒞 holds, meaning that Closed holds for 𝒞 with the property RanksF Fm 3 (Fm.CYL + 1) (1/4) 3 (1/2) Fm.CTu, which unfolds to the opaque FamilyRanksHypothesis.
- Premise 8. LoopRowS 3 𝒞 sel holds, meaning that for every function aF from real lists to reals, Closed holds for 𝒞 with the property that for every hc, eventually in x, for all indices and all words u, u', the hypothesis Hyp with C0 = 3 and A = aF(Fm.cOut), together with ConcTie and AbsConv for the selected data, implies both RowBig and RowNotScalar of Y.tO u u' with tolerance epsL = exp(−(1/3) · k · f · log k) and number ddC.
- Conclusion. Closed holds for 𝒞 with the property that every family Fm in 𝒞, for every proof hc of membership, satisfies TheoremSSelected Fm 3 (sel Fm hc), which says that there is x0 such that for every x ≥ x0 and every index i, whenever AdmissibleBoundsFromSource.hyp holds for Fm.D x i and Fm.L x i with the constants 3, sC' Fm, sCl Fm, Fm.CYL + 1, 1/4, 3, 1/2 and Fm.CTu, and Fm.x1 < x and (sel Fm hc).1 ≤ x hold, the bound ‖K0(u,u')‖² ≤ (1 + 1/b^6) · duS(u) · duS(u') / Dstar holds for all distinct words u ≠ u'.

This reading opens `D7`, `Formalism.MainNotions.S.Draft.SData (the field D.s and its atP)`, `Formalism.MainNotions.S.Loc.LocAt`, `Formalism.MainNotions.S.Loc.resChar` and `Formalism.BasicNotions.Rows.Data (Word, Dstar)`.

It does not open `Large`, `STies`, `SWa1`, `StabilizerFirstChernCompatibility`, `FamilyRanksHypothesis`, `StandingHypotheses / StandingNumericalData`, `tO, K0, AbsConv, RowNG, RowBig, RowNotScalar`, `duS, duC, DstC, sC', sCl, cOut, CYL` and `IsFundDom, IsRightReg, IsRConvF, Kset, IsCRepOn, coefOn, mInf, TFrameAt`.

The reader's confidence is medium. The quantifier structure, the explicit constants and the bodies of Closed, TheoremSSelected, LoopRowS, RanksRow, LocTied and LocAt are all visible, but the key quantities and conditions K0, tO, RowBig, RowNG, Large, STies, StandingHypotheses and FamilyRanksHypothesis have no body in the files.

### Line 10, `servH_row_of_artin`

The head is `GlobalTheory.Svd.servH_row_of_artin`, in the module Development › Abelian Variety Theory › Proofs › Satake Parameters › Bundle Both Parts Of Standard Kernel Of Global Artin Reci. The line gathers 10,808 declarations and hangs from line 7, `allRows_of_open0_alt`. Folded into the line are the wrappers `hServ_of_linkR`, `row_hServ_of_link_alt`, `reciprocity_kernel_of_artin`, `servH_row_linkR_alt` and `bundle_bothParts_of_standardKernel_of_globalArtinReciprocity`.

Assume the proposition that the code calls GlobalArtinReciprocity, which says that for every number field E with an algebraic closure Ω there is a monoid homomorphism art from Ideles E to Gab E Ω satisfying a condition that the code calls IsGlobalArtin. Then for every boundary type Bd, slot Q, linkage Lk and every function ker that assigns a KerEntTied record to each boundary element, if Q always implies the slot positionOf HasPart and if RowE Q Lk holds for the family that asks StdTie D O (ker D O c b), then Row Q Lk (ServH ker) holds. The dossier also folds five wrapper theorems into this line, and this reading does not describe them.

- Premise 1. GlobalArtinReciprocity holds, that is, for every number field E and algebraic closure Ω of E there exists a monoid homomorphism art from Ideles E to Gab E Ω with IsGlobalArtin art.
- Premise 2. Bd is any function that gives a type for each datum D, object O of D and real c, Q is any slot, Lk is any linkage for Bd, and ker gives a KerEntTied O.ex for each D, O, c and element of Bd D O c.
- Premise 3. For all K, X, f, T and c, the statement Q K X f T c implies positionOf HasPart K X f T c.
- Premise 4. RowE Q Lk E holds for the family E that sends any parameter and D, O, c, b to the statement StdTie D O (ker D O c b).
- Conclusion. Row Q Lk (ServH ker) holds, that is, there is a family E with RowE Q Lk E such that every class 𝒜 and raw selection σ satisfying IsSel Q Lk E 𝒜 σ also satisfies ServH ker 𝒜 σ.

```
GlobalArtinReciprocity ⇒ ∀ Bd ∀ Q ∀ Lk ∀ ker, [∀ K X f T c, Q K X f T c ⇒ positionOf HasPart K X f T c] ⇒ RowE Q Lk ((_, D, O, c, b) ↦ StdTie D O (ker D O c b)) ⇒ Row Q Lk (ServH ker), where Row Q Lk H means ∃ E, RowE Q Lk E ∧ ∀ 𝒜 ∀ σ, IsSel Q Lk E 𝒜 σ ⇒ H 𝒜 σ, and RowE Q Lk E means EvP ((κ, K) ↦ ∀ β ∈ BPt K, β.Is Q ⇒ ∀ c ∈ ℝ ∀ b ∈ Bd β.D β.O c, Lk K β c b ⇒ E κ β.D β.O c b), and ServH ker 𝒜 σ means Closed 𝒜 ((Fm, _) ↦ RowTwU Fm) ∧ AtAll ((D, O, c, b) ↦ Pdv.At O.ex (ker D O c b).ent) 𝒜 σ
```

The reading does not open the names `GlobalArtinReciprocity`, `HasPart`, `RowE`, `ServH`, `StdTie`, `Closed, EvP, IsSel, AtAll, RowTwU, Pdv.At, BPt, Par` and `D7`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that global Artin reciprocity is used to pass from a kernel that is tied to a standard construction at each bundle point to a service hypothesis for that kernel along a whole row of the construction, but the dossier does not show this.

The reader's confidence is low. The quantifier structure and the bodies of Row, RowE, ServH, StdTie and positionOf are visible, but EvP, IsSel, AtAll, Closed, RowTwU, Pdv.At, StdAt, Part and IsGlobalArtin have no visible bodies and 49 definitions were left out.

The check found one error in the first version of this reading. The text above is the corrected version, which passed the check after three rounds of correction.

- A says that of the five wrapper theorems there are "four that specialise it to particular Bd, Q and Lk built from parameters p", but only reciprocity_kernel_of_artin and servH_row_linkR_alt fix Bd, Q and Lk, whereas hServ_of_linkR and row_hServ_of_link_alt quantify over every "Lk : LkT BundleCondition" under a linkage premise and conclude "SlotServiceCondition (IsGoodE p.s) Lk", a name whose body the dossier does not show.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 1 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 7 findings on it, and the text was changed in 7 places. A check of the changed text then found no error.

Assume the proposition that the code calls GlobalArtinReciprocity. By its visible body, this proposition says that for every number field E and every algebraic closure Ω of E there is a monoid homomorphism art from a type the code calls Ideles E into a type the code calls Gab E Ω, and that art satisfies a condition the code calls IsGlobalArtin. Now take any family Bd of types indexed by a D7 record D, an object O over D and a real number c, any slot predicate Q, any link predicate Lk, and any rule ker that turns each element b of Bd D O c into a kernel record of type KerEntTied over O.ex. Suppose two things. First, every point accepted by Q has the position property positionOf HasPart. Second, the condition RowE holds for Q and Lk with the map sending κ, D, O, c and b to StdTie D O (ker D O c b). Then the row condition Row holds for Q, Lk and the service property ServH ker.

- Premise 1. The proposition the code calls GlobalArtinReciprocity holds. For every number field E with an algebraic closure Ω there is a monoid homomorphism art from Ideles E to Gab E Ω such that IsGlobalArtin art holds.
- Premise 2. Bd is any family that gives a type for each D7 record D, object O of type Obj D and real number c. It is an implicit argument.
- Premise 3. Q is any slot predicate of type V4.Slot. Such a predicate takes a context K, stages X, a frame f, twist data T and a core c, and returns a proposition.
- Premise 4. Lk is any predicate of type LkT Bd. It takes a context K, an element β of type BPt K, a real number c and an element of Bd β.D β.O c, and returns a proposition. Here Lk is a bound variable and not the definition Formalism.L2.Forms.Lk.
- Premise 5. ker is any function that sends each D, O, c and each b in Bd D O c to a record of type KerEntTied O.ex.
- Premise 6. For all K, X, f, T and c, if Q K X f T c holds then positionOf HasPart K X f T c holds. This means there exist w, Z and c′ such that Part w Z c′.O is nonempty and the dependent triple formed from X.C, the later data (X.W, X.V, X.S, X.N, X.G) and c is equal to the triple (w.C, Z, c′).
- Premise 7. RowE Q Lk holds for the map that sends κ, D, O, c and b to StdTie D O (ker D O c b). This means the predicate EvP holds of the property of κ and K that says that for every β of type BPt K with β.Is Q, every real c and every b in Bd β.D β.O c with Lk K β c b, the triple (β.D, β.O, ker β.D β.O c b) is standard. Being standard means it equals a triple (I.rec7 l Z, O′, t′) built from some base B, PreX X, TC structure I, laws l with Law0 l, later data Z, object O′ and kernel record t′ that satisfy StdAt I l l0 Z O′ t′.
- Conclusion. Row Q Lk (ServH ker) holds. So there is a map E from Par to BdP Bd such that RowE Q Lk E holds and every family class 𝒜 and every raw selection σ with IsSel Q Lk E 𝒜 σ satisfy ServH ker 𝒜 σ. ServH ker 𝒜 σ means that Closed holds of 𝒜 and the map sending Fm and an ignored second argument to GlobalTheory.TwU.RowTwU Fm, and that AtAll holds of the predicate sending D, O, c and b to GlobalTheory.Pdv.At O.ex (ker D O c b).ent together with 𝒜 and σ.

This reading opens `D7`.

It does not open `IsGlobalArtin`, `Ideles`, `Gab`, `Part`, `EvP`, `IsSel`, `Par, BdP, Ctx, BPt, FamClass, RawSel`, `BPt.Is`, `Closed, RowTwU, AtAll, Pdv.At`, `StdAt, TC, TC.Later, I.rec7, I.Laws, I.Law0, Mem.Base, PreX` and `Core, Stages, Fr, TwDat, ColW, Cols, CP`.

The reader's confidence is medium. The logical shape and the visible bodies of Row, RowE, positionOf, HasPart, StdTie, ServH and D7 are clear, but EvP, IsSel, Closed, AtAll, Pdv.At, StdAt, Part, IsGlobalArtin and several base types have no bodies in the files, so the actual content of premises and conclusion is only partly visible.

### Line 11, `member_bundles_large_unramified_exponents_alt`

The head is `GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Member Bundles Large Unramified Exponents. The line gathers 20,058 declarations and hangs from line 6, `hypotheses_nonempty_of_unramified_exponents_alt`. Folded into the line is the wrapper `large_unramified_exponent_bundles_exist_alt`.

Assume a bundle of named propositions that the code calls UnitaryGroupThirdPlaceHypotheses and a condition that the code calls S0.RowRat. Then for every proof hL of RecTExists, every real cDep and every property A of type AtP with EvLgG A, three things hold together. They are the mass ratio identity SiegelMassRatioCM, the condition MemberE p.s, and the condition ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p), where p is the parameter record ⟨RX, N, SExt.none, geoCl anyGeometry⟩ and N is the extension built from hL, cDep and A.

- Premise 1. UnitaryGroupThirdPlaceHypotheses holds, which is a record of at least 28 named propositions such as ClozelCohomological, GlobalArtinReciprocity, JacquetShalika and WeilSiegelFormulaUnitary, with the list cut off in the dossier.
- Premise 2. S0.RowRat holds, which is a condition StepW Start applied to a statement whose final conclusion is RowTest (z.R.toCx3 z.F), meaning that finitely many linear functionals jointly separate the space EE and take values in the range of the map Bs.v0.embedding on the vectors Θ t (jR t x).
- Premise 3. hL is a proof of RecTExists, which says that for every number field E, algebraic closure Ω, valuation subring A of Ω, nonzero prime w of the integers of E and proof h of IsPlaceOver A w there exists rc with IsRecT h rc.
- Premise 4. cDep is any real number and A is any property of a context, a base B, a frame of B and a twisting datum of B.
- Premise 5. EvLgG A holds, which is a condition that the code calls EvG applied to the map sending K to large₂ K (A K).
- Conclusion. SiegelMassRatioCM and MemberE p.s and ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) all hold, with p = parametersOfExtension (extensionWithAtProperty hL (extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry).

```
UnitaryGroupThirdPlaceHypotheses ⇒ RowRat ⇒ ∀ hL ∈ RecTExists ∀ cDep ∈ ℝ ∀ A ∈ AtP, EvLgG A ⇒ SiegelMassRatioCM ∧ MemberE p.s ∧ ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p), with p = ⟨RX, extensionWithAtProperty hL (extensionWithOrigin hL cDep) A, SExt.none, geoCl anyGeometry⟩, where SiegelMassRatioCM means ∀ number fields K with star, IsCMUnram K ⇒ ∀ M ≥ 3, mass(stdForm K M, stdLat K M) / mass(stdForm K (M−1), stdLat K (M−1)) = [((M−1)! · (vInv K / π)^M)^(fDeg K) / √((2 · vInv K)^(fDeg K))] · lValEta K M, and MemberE 𝒮 means BaseCond KPx ∧ FirstG KPx (IsBuiltE 𝒮) ∧ ExportF KPx (IsBuiltE 𝒮) ∧ SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮), and ExBL KP Q Q' Lk means ∃ R ∈ Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk
```

The reading does not open the names `UnitaryGroupThirdPlaceHypotheses`, `RowRat`, `RecTExists`, `EvLgG`, `massRatioRightSide`, `extensionWithOrigin`, `anyGeometry and geoCl`, `MemberE`, `IsBuiltE and IsGoodE`, `KPx`, `LargeBaseCondition`, `ExB` and `BundleLinkage`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that from a list of published theorems about automorphic forms and Galois representations one obtains the Siegel mass ratio for standard hermitian lattices over unramified CM fields, a membership statement, and the eventual existence of bundles linked to every good point, but the dossier does not show this beyond the mass ratio formula.

The reader's confidence is low. The mass ratio conjunct and the logical shape are visible, but BaseCond, FirstG, ExportF, SecondG, EvP, EvLg, EvG, positionOf, BuiltE, GoodE, linkOf, the field s of the parameter record and most of the hypothesis bundle have no visible bodies, and 55 definitions were left out.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 2 errors in this reading and, after they were corrected, 0 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 5 findings on it, and the text was changed in 5 places. A check of the changed text then found no error.

Suppose the sixty-field proposition structure UnitaryGroupThirdPlaceHypotheses holds and the condition RowRat holds. Then for every proof hL of the proposition RecTExists, every real number cDep and every predicate A on quadruples (context K, base record B, frame f, twisting data T) that satisfies the condition EvLgG, three things hold together. First, for every CM-type number field K that is unramified in the sense of IsCMUnram and every natural number M ≥ 3, the mass of the standard Hermitian lattice of rank M divided by the mass of the one of rank M − 1 equals a fixed explicit expression called massRatioRightSide K M. Second, the condition MemberE holds for the slot data p.s, where p is the parameter record built from hL, cDep and A in the way described below. Third, there is a slot R such that LargeBaseCondition KPx (IsBuiltE p.s) R holds, which is the condition that the code calls EvLg applied to the property that whenever KPx B f holds, every stage tuple and core satisfying IsBuiltE p.s also satisfies R, and such that ExB (sAnd (IsGoodE p.s) R) (BundleLinkage p) holds, which is the condition that the code calls EvP applied to the property of an ignored argument and a context K that every β of type BPt K with β.Is (sAnd (IsGoodE p.s) R) has, at every real number c, a BundleCondition record that is linked in the sense of BundleLinkage p.

- Premise 1. The record UnitaryGroupThirdPlaceHypotheses holds, which means that each of its sixty proposition fields holds, most of them placed in the namespace Published.
- Premise 2. The condition RowRat holds, which is StepW Start applied to the property of K, B, f, T and w saying that for all Z, hX, Wt and z, under GrpTrue Z.N f, GrpAt (w.st Z) w.I, DV.KapDef (w.D Z), z.R.toRealDat.ExAt, InGeo z.geo, CoreP z, GIs2 K w Z.G, the identity Wt = z.W1 (F0K K.s (w.D Z)) and the condition that B.places.resChar v belongs to T.pl for all v in Wt, the row test RowTest holds for z.R.toCx3 z.F.
- Premise 3. hL is any proof of RecTExists, the claim that for every number field E, algebraic closure Ω, valuation subring A of Ω and prime w of the ring of integers of E lying under A there is a map rc that satisfies IsRecT.
- Premise 4. cDep is any real number.
- Premise 5. A is any predicate on context, base record, frame and twisting data.
- Premise 6. A satisfies EvLgG, which by definition is EvG applied to the family K ↦ large₂ K (A K).
- Conclusion. SiegelMassRatioCM holds, MemberE holds for p.s, and ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) holds, with p = parametersOfExtension (extensionWithAtProperty hL (extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry).

This reading opens `D7`, `BundleCondition`, `UnitaryGroupThirdPlaceHypotheses (fields past the cut)`, `IsRecT`, `PrePin` and `FieldDat`.

It does not open `Step`, `EvG`, `large₂`, `GeoCl`, `Parameters / .s / RX`, `BaseCond, FirstG, ExportF, SecondG`, `positionOf, BuiltE, GoodE`, `KsExact`, `EvLg / EvP` and `linkOf, BundleWitness`.

The reader's confidence is low. The logical shape and the mass-ratio conjunct can be seen in full, but MemberE, the eventuality operators EvG, EvLg and EvP, the slots positionOf, BuiltE and GoodE, Step, Parameters with its field s, and BundleWitness all have no visible body, so most of what is claimed stays opaque.

### Line 12, `exists_baseLattice_of_prime_alt`

The head is `GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Exists Base Lattice Of Prime. The line gathers 13,160 declarations and hangs from line 11, `member_bundles_large_unramified_exponents_alt`.

Assume three named bundles of hypotheses and the condition ExistsUnlocalizedSaturatedState, then a proof hL of the statement RecTExists, then a fourth bundle that depends on hL, then any real number cDep. Let p be the parameter record built from the extension that the code calls extensionWithOrigin hL cDep, the trivial choice SExt.none and the geometry condition geoCl anyGeometry. If p satisfies the condition MultiplicityCondition, then the slot system p.s satisfies the four-part condition MemberE, and there is a slot R such that LargeBaseCondition holds from the slot IsBuiltE p.s to R and the condition ExB holds for the conjunction of IsGoodE p.s with R, relative to the linkage BundleLinkage p.

- Premise 1. The bundle of 21 assumed statements that the code calls HypAAlt holds.
- Premise 2. The bundle of 25 assumed statements that the code calls EllipticHypothesis holds.
- Premise 3. The bundle of 5 assumed statements that the code calls MultiplicityCoverHypotheses holds.
- Premise 4. The condition that the code calls ExistsUnlocalizedSaturatedState holds.
- Premise 5. hL is a proof of RecTExists, which says that for every number field E, algebraic closure Ω of E, valuation subring A of Ω, nonzero prime w of the ring of integers of E and proof h of IsPlaceOver A w there is an object rc with IsRecT h rc.
- Premise 6. The bundle of 6 assumed statements that the code calls LocalLanglandsHypothesis hL holds.
- Premise 7. cDep is any real number.
- Premise 8. MultiplicityCondition holds for the record p = parametersOfExtension (extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry).
- Conclusion. MemberE holds for p.s, and ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) holds, which means that some slot R satisfies LargeBaseCondition KPx (IsBuiltE p.s) R together with ExB (sAnd (IsGoodE p.s) R) (BundleLinkage p).

```
HypAAlt ⇒ EllipticHypothesis ⇒ MultiplicityCoverHypotheses ⇒ ExistsUnlocalizedSaturatedState ⇒ ∀ hL proving RecTExists, LocalLanglandsHypothesis(hL) ⇒ ∀ cDep ∈ ℝ, with p = parametersOfExtension(extensionWithOrigin(hL, cDep), SExt.none, geoCl(anyGeometry)), MultiplicityCondition(p) ⇒ [ MemberE(p.s) ∧ ∃ R slot, LargeBaseCondition(KPx, IsBuiltE(p.s), R) ∧ ExB(IsGoodE(p.s) ∧ R, BundleLinkage(p)) ], where MemberE(S) = BaseCond(KPx) ∧ FirstG(KPx, IsBuiltE S) ∧ ExportF(KPx, IsBuiltE S) ∧ SecondG(KPx, IsBuiltE S, IsGoodE S) and ExB(Q, Lk) = EvP(K ↦ ∀ β ∈ BPt(K), β.Is(Q) ⇒ ∀ c ∈ ℝ, ∃ b ∈ BundleCondition(β.D, β.O, c), Lk(K, β, c, b))
```

The reading does not open the names `HypAAlt`, `EllipticHypothesis`, `MultiplicityCoverHypotheses`, `ExistsUnlocalizedSaturatedState`, `RecTExists`, `LocalLanglandsHypothesis`, `extensionWithOrigin`, `geoCl anyGeometry`, `p.s`, `MultiplicityCondition`, `MemberE`, `KPx`, `IsBuiltE and IsGoodE`, `LargeBaseCondition`, `ExB`, `BundleLinkage`, `BundleCondition` and `EvP, EvLg, Step`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names EvP and EvLg suggest that the properties hold eventually or for all large contexts, and the hypothesis names suggest published results in Galois cohomology, class field theory, automorphic forms and discrete series, while the head name speaks of a base lattice and a prime although no lattice or prime appears in the statement.

The reader's confidence is medium. The logical shape and the first layers of unfolding are visible, but the operators EvP, EvLg, Step, the projection p.s, the four parts of MemberE and nearly all hypothesis components are opaque, and 91 definitions were left out of the dossier.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 6 errors in this reading and, after they were corrected, 2 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 8 findings on it, and the text was changed in 8 places. A check of the changed text then found one error, which the text below corrects. A check of the corrected text found no error.

Assume four propositions, namely the bundle of hypotheses HypAAlt, the bundle EllipticHypothesis, the bundle MultiplicityCoverHypotheses and the proposition ExistsUnlocalizedSaturatedState. Then for every proof hL of the proposition RecTExists for which LocalLanglandsHypothesis hL holds, and for every real number cDep, the theorem looks at the single parameter record p built by parametersOfExtension from extensionWithOrigin hL cDep of type NormChoiceExtension hL, the constant PUnit-valued family SExt.none of type SExt and the predicate geoCl anyGeometry of type GeoP. If MultiplicityCondition holds for p, then two things follow together. The first is the condition MemberE on p.s, which has the unopened type Slots. The second is ExBL, which says that some slot R exists such that the condition LargeBaseCondition KPx (IsBuiltE p.s) R holds and the condition ExB holds for the slot "IsGoodE p.s and R" with the linkage BundleLinkage p, so that, in the sense the code calls EvP applied to a predicate of an ignored argument and a context K, for every β of type BPt K with β.Is of that slot and every real c there are a BundleCondition record b over β.D, β.O and c, a q of the unopened type WPt p.s K and a BundleCondition record b' with BundleWitness q b' nonempty, such that the dependent triple (β.D, β.O, b) equals (q.w.D q.Z, q.O, b').

- Premise 1. HypAAlt holds, which is a record of twenty-one fields a1 to a23 with only a4 and a15 absent, namely eighteen named propositions such as RayField, CasselmanWallach and GlobalArtinReciprocity and three explicit quantified statements a19, a20 and a21 involving unopened names such as IsHCParam, IsDS, UJset, GrpData, Ix, IsParam, DSRep and HasParam.
- Premise 2. EllipticHypothesis holds, which is a record of twenty-five propositions e1 to e25, the last saying that for every object D of the record type D7, every prime l and every K of the type FinExt l, the condition bkAll holds of (D.loc l).PD K, where FinExt l is the type of intermediate fields K of Om l over ℚ_[l] that are finite dimensional over ℚ_[l], PD is the field of LocPrime l that gives for each K of type FinExt l a PeriodData record, and only bkAll is not opened.
- Premise 3. MultiplicityCoverHypotheses holds, which is a record of DiscreteSeriesCover, PublishedThetaConditionTheorems, HeckeLPartialContinuation and two StepW conditions multL and multW that conclude GlobalTheory.CuspMult.MultEq applied to z.R.toRealDat, with multW also concluding Formalism.IndefR.Rat.RowTest applied to z.R.toCx3 z.F.
- Premise 4. ExistsUnlocalizedSaturatedState holds, which is the unopened condition Step applied to KPx, the constantly true predicate and the property of K, B, f and T which says that for every w of the unopened type ColW B f T satisfying Start (Pinned, Supp and Coh) there exist a record P of type Pre2 K w and a record x of type St P with SatU P, with the type x.o.N.nd.Loc empty and with x.o.η j v equal to 0 for all j and v.
- Premise 5. hL is any proof of RecTExists, which says that for every number field E with algebraic closure Ω, every valuation subring A of Ω and every nonzero prime w of the integers of E under A, a map rc satisfying IsRecT exists.
- Premise 6. LocalLanglandsHypothesis hL holds, which is a record of six propositions pr, ser, arch, par, pt and parMem.
- Premise 7. cDep is any real number.
- Premise 8. MultiplicityCondition holds for the parameter record p = parametersOfExtension (extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry), which says that, in the sense that the code calls EvP applied to a predicate on an ignored argument and K, GlobalTheory.CuspMult.MultEq holds for q.x.what₂.r.z.R.toRealDat for every q of the unopened type WPt p.s K.
- Conclusion. MemberE p.s holds and ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (BundleLinkage p) holds for that same parameter record p.

This reading opens `D7`, `D.loc (LocTheory)`, `RecTExists (IsRecT, LawsT, IsLocalArtin per glossary)`, `KPx (FieldDat, PrePin per glossary)` and `BundleCondition (RecTAlt, STiesRAlt, RowSideFamily, SquareIntegrableColumns, RealTBAlt per glossary)`.

It does not open `Step`, `geoCl`, `p.s`, `EvP`, `MultEq`, `BaseCond, FirstG, ExportF, SecondG` and `EvLg`.

The reader's confidence is low. The order of quantifiers and the logical shape are fully visible, but the conditions that carry the content, such as EvP, EvLg, Step, MultEq, BaseCond, FirstG, ExportF, SecondG, positionOf, GeoCl and the slot data p.s, have no visible body in the three files.

### Line 13, `final_alt_alt`

The head is `UpperTheory.GalC.final_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › C Final. The line gathers 15,685 declarations and hangs from line 6, `hypotheses_nonempty_of_unramified_exponents_alt`.

The theorem proves the proposition that the code calls mainTheorem. That proposition says that, under eight named hypotheses, for every proof hL of RecTExists and every real number cDep, if LinkedAt holds for the parameters parametersOfDependence hL cDep with the row condition built from BoundAtTwoThreeFamilyFonAlt, then LinkedAt holds for the same parameters with the row condition built from LinkN. Both row conditions have the form SlotNormCondition Q L applied to the test that sends a family class 𝒞 to Closed 𝒞 of the respective family property.

- Premise 1. The bundle of 7 assumed statements that the code calls Hypotheses₂ holds.
- Premise 2. The bundle of 14 assumed statements that the code calls PublishedInputsThirdLayerAlt holds.
- Premise 3. The bundle of 12 assumed statements that the code calls GeometricGaloisRepCompatibility holds.
- Premise 4. The bundle of 6 assumed statements that the code calls SerN holds.
- Premise 5. The statement DepthZeroSupport holds, which passes the existence of a nonzero vector fixed by KOne from a representation π over a nonarchimedean local field to every member σ_a of a family related to π by IsCuspSupport. This summary leaves out the binders n, s and d and the arguments of KOne, which are k (Fin n) for π and k (Fin (d a)) for σ_a.
- Premise 6. LocalFiniteness holds, which asserts LocalFinitenessAt A rho v for every number field F, algebraic closure Ω, prime l, exponent r, finite discrete module M over the integers modulo l^r, valuation subring A of Ω, representation rho of Dec A on M and height-one prime v of the integers of F.
- Premise 7. LocalTateDuality holds, which asserts LocalTateDualityAt A rho v over the same range of data.
- Premise 8. LocalEulerChar holds, which asserts LocalEulerCharAt A rho v over the same range of data.
- Premise 9. hL is a proof of RecTExists and cDep is any real number.
- Premise 10. LinkedAt holds for parametersOfDependence hL cDep with the row condition (Q, L) ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 BoundAtTwoThreeFamilyFonAlt).
- Conclusion. LinkedAt holds for parametersOfDependence hL cDep with the row condition (Q, L) ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 LinkN).

```
Hypotheses₂ ⇒ PublishedInputsThirdLayerAlt ⇒ GeometricGaloisRepCompatibility ⇒ SerN ⇒ DepthZeroSupport ⇒ LocalFiniteness ⇒ LocalTateDuality ⇒ LocalEulerChar ⇒ ∀ hL proving RecTExists, ∀ cDep ∈ ℝ, with p = parametersOfDependence(hL, cDep), LinkedAt(p, (Q, L) ↦ SlotNormCondition(Q, L, 𝒞 ↦ Closed(𝒞, (Fm, CH) ↦ BoundAtTwoThreeFamilyFonAlt(Fm)))) ⇒ LinkedAt(p, (Q, L) ↦ SlotNormCondition(Q, L, 𝒞 ↦ Closed(𝒞, (Fm, CH) ↦ LinkN(Fm)))), where LinkedAt(p, r) = Lg1(KPx, IsBuiltE(p.s), IsGoodE(p.s), S ↦ r(S, BundleLinkage(p))), SlotNormCondition(Q, L, N) = Row(Q, L, 𝒜 ↦ N(D3(3, 𝒜))), Closed(𝒞, P) = ∃ ε1 > 0, ∀ eps with 0 < eps ≤ ε1, ∃ K ∈ TransportedAlt, ∀ Fm ∈ FamP(eps), ∀ CH ∈ ℝ, 𝒞(Fm) ⇒ Fm.Large(K, CH) ⇒ P(Fm, CH), and LinkN(Fm) = ∃ C, x0 ∈ ℝ, ∀ x ≥ x0, ∀ i ∈ Fm.Ix(x), ShaFinOdd(Fm.D x i) ⇒ ∀ j ∈ lifts(Fm.D x i), LinkN_at(Fm.L x i, j, C)
```

The reading does not open the names `Hypotheses₂`, `PublishedInputsThirdLayerAlt`, `GeometricGaloisRepCompatibility`, `SerN`, `DepthZeroSupport`, `LocalFiniteness, LocalTateDuality, LocalEulerChar`, `RecTExists`, `parametersOfDependence`, `LinkedAt`, `SlotNormCondition`, `BoundAtTwoThreeFamilyFonAlt`, `LinkN` and `FamP, FamClass, TransportedAlt`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the theorem turns a bound at the primes two and three for families of arithmetic data into a final bound called LinkN, conditional on published results in p-adic Hodge theory, Galois cohomology and automorphic forms, with ShaFinOdd suggesting finiteness of a Tate–Shafarevich group at odd primes.

The reader's confidence is low. The implication and its eight hypotheses are visible, but this dossier shows Lg1, Row, D3, LinkN_at, ShaFinOdd, FamP and all hypothesis components without bodies, and 49 definitions were left out.

The check found no error in this reading.

The check found one error in the second reading, which the text above does not use.

A second model, Gemini, checked this reading again. 3 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 1 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then found no error in it.

The theorem says that the proposition the code calls mainTheorem holds, and that proposition is one long implication. It assumes four bundles of named statements, called Hypotheses₂, PublishedInputsThirdLayerAlt, GeometricGaloisRepCompatibility and SerN. It also assumes the depth-zero support statement DepthZeroSupport and three statements called LocalFiniteness, LocalTateDuality and LocalEulerChar, each of which says that a per-place condition with no visible body holds for every finite ZMod(l^r)-representation of Dec A at every finite place of every number field. Under these assumptions, it says that for every proof hL of the statement RecTExists and every real number cDep, take the parameter record p = parametersOfDependence hL cDep. If LinkedAt holds for p with the row test built from Closed and BoundAtTwoThreeFamilyFonAlt, then LinkedAt also holds for p with the same row test built from Closed and LinkN. In other words, the theorem transfers a linkage statement from the bound condition BoundAtTwoThreeFamilyFonAlt to the condition LinkN, at the same parameters and in the same row and slot setting, and it does not claim that either linkage holds outright.

- Premise 1. Hypotheses₂ holds, which is the conjunction of seven statements that the code calls FontaineBcris, GlobalArtinReciprocity, BlochKatoLocal, LocalTateDualityK, LocalEulerCharK, LocalFinitenessK and BhattScholzeIntegral.
- Premise 2. PublishedInputsThirdLayerAlt holds, which is the conjunction of fourteen named statements, among them ThetaLocalInputsAlt, CuspRapidDecay, HarishChandraFinite, GreenCuspidal, Green, ZelevinskyPolynomialRing, RayClassFieldSt, RayField, RayCharacterArtin, BaseChangeDefiniteUnitaryGroup, GenericUnitaryDualGL, StandardCosocleGL, Cheb and HoweUnram.
- Premise 3. GeometricGaloisRepCompatibility holds, which is the conjunction of twelve named statements, among them WeilRepresentationUnitaryPair, DiscreteSeriesExists, DiscreteSeriesClassification, FlathFactorisation, WeilSiegelFormulaUnitary, DoublingMethodLocalZetaIntegrals, HeckeLPartialContinuation and HtCard.
- Premise 4. SerN holds, which is the conjunction of six named statements called SeriesRat, SerInt, HeckeInt, HeckeTransform, HeckeReadTie and RatioConj.
- Premise 5. DepthZeroSupport holds. For every nonarchimedean local field k, every n, every π of the type Irr k n and every family σ of objects of the types Irr k (d a), if IsCuspSupport links π to the σ a and π has a nonzero vector fixed by KOne k (Fin n), then every σ a has a nonzero vector fixed by KOne k (Fin (d a)).
- Premise 6. LocalFiniteness holds, meaning that LocalFinitenessAt A rho v is true for every number field F with algebraic closure Ω, every prime l, every r, every finite discrete ZMod(l^r)-module M, every valuation subring A of Ω, every representation rho of Dec A on M and every finite place v of F.
- Premise 7. LocalTateDuality holds, meaning that LocalTateDualityAt A rho v is true for all of the same data.
- Premise 8. LocalEulerChar holds, meaning that LocalEulerCharAt A rho v is true for all of the same data.
- Premise 9. hL is any proof of RecTExists, and cDep is any real number.
- Premise 10. LinkedAt holds at the parameters parametersOfDependence hL cDep for the relation that sends a slot Q and a linkage L to SlotNormCondition Q L applied to the class property 𝒞 ↦ Closed 𝒞 BoundAtTwoThreeFamilyFonAlt.
- Conclusion. LinkedAt holds at the same parameters for the relation that sends Q and L to SlotNormCondition Q L applied to the class property 𝒞 ↦ Closed 𝒞 LinkN.

This reading opens `D7`, `BundleCondition`, `KPx`, `Lg1`, `Row`, `D3`, `Parameters` and `FamClass`.

It does not open `FamP`, `FamClass`, `TransportedAlt`, `ShaFinOdd`, `lifts`, `LinkN_at`, `SetupAlt, BoundAtTwoThree`, `D3`, `Row, Lg1, IsBuiltE, IsGoodE, BundleLinkage, V4.Slot, LkT, Parameters`, `IsCuspSupport, Irr, KOne, fixed, LocalFinitenessAt, LocalTateDualityAt, LocalEulerCharAt, Dec, IsRecT` and `named published statements`.

The reader's confidence is low. The logical shape is fully visible, but the conditions that carry the mathematical content are opaque names, including LinkN_at, ShaFinOdd, lifts, SetupAlt, BoundAtTwoThree, FamP, D3, Row and the dozens of published statements in the hypotheses.

### Line 14, `final_of_alt`

The head is `UpperTheory.GalC.final_of_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Link N Fam. The line gathers 14,931 declarations and hangs from line 13, `final_alt_alt`.

Assume five named hypotheses, a proof hL of RecTExists, a real number cDep, and that MemberAtLayerPoint hL holds for the property that sends its arguments, among them w, Z and nch, to GaloisPreconditions (w.D Z) nch. If LinkedAt holds for the parameters parametersOfDependence hL cDep with the row condition built from BoundAtTwoThreeFamilyFonAlt, then LinkedAt holds for the same parameters with the row condition built from LinkN. Unfolded, the conclusion says that there are a slot R and an assignment E such that, with p for parametersOfDependence hL cDep, LargeBaseCondition KPx (IsBuiltE p.s) R and RowE hold and every family class 𝒜 with a selection σ that satisfies IsSel has Closed (D3 3 𝒜) LinkN.

- Premise 1. hP, the bundle of 7 assumed statements that the code calls Hypotheses₂, holds.
- Premise 2. hG, the statement CutGivesAlt, holds, which says that for every D of type D7 and every nch of type NChoice D with GaloisPreconditions D nch and Tie4 D there is c in CutD D with c.Good, NormChoiceFacts (cut D c) (nchTr c nch) and Tie4 (cut D c).
- Premise 3. prN, the bundle of 14 assumed statements that the code calls PublishedInputsThirdLayerAlt, holds.
- Premise 4. hX, the bundle of 12 assumed statements that the code calls GeometricGaloisRepCompatibility, holds.
- Premise 5. dzs, the statement DepthZeroSupport, holds.
- Premise 6. hL is a proof of RecTExists.
- Premise 7. cDep is any real number.
- Premise 8. hF, the statement MemberAtLayerPoint hL applied to the property that sends its arguments to GaloisPreconditions (w.D Z) nch, holds.
- Premise 9. hAt, the statement LinkedAt for parametersOfDependence hL cDep with the row condition (Q, L) ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 BoundAtTwoThreeFamilyFonAlt), holds.
- Conclusion. LinkedAt holds for parametersOfDependence hL cDep with the row condition (Q, L) ↦ SlotNormCondition Q L (𝒞 ↦ Closed 𝒞 LinkN).

```
Hypotheses₂ ∧ CutGivesAlt ∧ PublishedInputsThirdLayerAlt ∧ GeometricGaloisRepCompatibility ∧ DepthZeroSupport ⇒ ∀ hL proving RecTExists, ∀ cDep ∈ ℝ, with p = parametersOfDependence(hL, cDep) and Lk = BundleLinkage(p), MemberAtLayerPoint(hL, (…, w, Z, …, nch, …) ↦ GaloisPreconditions(w.D Z, nch)) ⇒ LinkedAt(p, (Q, L) ↦ SlotNormCondition(Q, L, 𝒞 ↦ Closed(𝒞, BoundAtTwoThreeFamilyFonAlt))) ⇒ LinkedAt(p, (Q, L) ↦ SlotNormCondition(Q, L, 𝒞 ↦ Closed(𝒞, LinkN))), where the conclusion unfolds to ∃ R slot, LargeBaseCondition(KPx, IsBuiltE(p.s), R) ∧ ∃ E, RowE(sAnd(IsGoodE(p.s), R), Lk, E) ∧ ∀ 𝒜 ∀ σ, IsSel(sAnd(IsGoodE(p.s), R), Lk, E, 𝒜, σ) ⇒ Closed(D3(3, 𝒜), LinkN), with LinkN(Fm) = ∃ C, x0 ∈ ℝ, ∀ x ≥ x0, ∀ i ∈ Fm.Ix(x), ShaFinOdd(Fm.D x i) ⇒ ∀ j ∈ {1, …, (Fm.D x i).R.m}, LinkN_at(Fm.L x i, j, C), and LinkN_at(L, j, C) = [Summable(vvTerm D) ⇒ etaSum(L, j) ≤ L.dZ0(j) · (C · (D.R.f · D.R.m · L.sc.b · (L.sc.L)² + (log L.sc.x)² · L.Nc) + Σ_l vvTerm(D, l))]
```

The reading does not open the names `Hypotheses₂`, `CutGivesAlt`, `GaloisPreconditions`, `PublishedInputsThirdLayerAlt`, `GeometricGaloisRepCompatibility`, `DepthZeroSupport`, `RecTExists`, `MemberAtLayerPoint`, `parametersOfDependence`, `Lg1`, `Row`, `D3`, `FamP`, `BoundAtTwoThreeFamilyFonAlt`, `LinkN_at`, `ShaFinOdd` and `KPx, IsBuiltE, IsGoodE, BundleLinkage`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the theorem derives the final inequality LinkN, a bound on a sum called etaSum for families whose Tate–Shafarevich lengths are finite, from a bound at the primes two and three, given a cutting construction and Galois-theoretic preconditions, and the name ShaFinOdd suggests odd primes although the shown body quantifies over all primes.

The reader's confidence is medium. The dossier unfolds LinkedAt, Lg1, Row, Closed, LinkN and LinkN_at far enough to see the logical form and the final inequality, but LargeBaseCondition, RowE, IsSel, EvLgG, etaSum, vvTerm and the hypothesis components stay opaque and 66 definitions were left out.

The check found no error in this reading.

A second model, Gemini, checked this reading again. 3 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found one error, which the text above corrects. A second such check found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 2 errors in this reading and, after they were corrected, 3 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 6 findings on it, and the text was changed in 5 places. A check of the changed text then found no error.

Assume the bundle of stated results that the code calls Hypotheses₂, the statement CutGivesAlt, the two bundles PublishedInputsThirdLayerAlt and GeometricGaloisRepCompatibility, the single statement DepthZeroSupport, a proof hL of the statement RecTExists, a real number cDep, and the condition hF that MemberAtLayerPoint hL holds for the predicate that sends the layer data to GaloisPreconditions (w.D Z) nch. Assume also that the property LinkedAt holds for the parameter record built from hL and cDep, where the test is SlotNormCondition applied to the closure property Closed of the family bound BoundAtTwoThreeFamilyFonAlt. Under these premises the theorem concludes that the same LinkedAt statement holds with the same parameter record and the same SlotNormCondition test, but with BoundAtTwoThreeFamilyFonAlt replaced inside Closed by the family bound LinkN. Here Closed for a class 𝒞 and a property P means that there is a number ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is a record K of type TransportedAlt, made of one real number and three functions from lists of reals to reals, such that for every family Fm of type FamP eps and every real CH with 𝒞 Fm and Fm.Large K CH the property P holds of Fm and CH. LinkN for a family Fm means that there are real C and x0 such that, for every x ≥ x0 and every index i of the family at x for which the datum Fm.D x i satisfies ShaFinOdd, and for every j in {1, …, (Fm.D x i).R.m}, the condition LinkN_at (Fm.L x i) j C holds, which is an inequality required whenever the series vvTerm of the datum is summable.

- Premise 1. hP, a proof of the bundle Hypotheses₂, which collects seven stated results that the code calls FontaineBcris, GlobalArtinReciprocity, BlochKatoLocal, LocalTateDualityK, LocalEulerCharK, LocalFinitenessK and BhattScholzeIntegral.
- Premise 2. hG, a proof of CutGivesAlt, which says that for every D7 datum D and every nch of type NChoice D satisfying GaloisPreconditions D nch and Tie4 D there is an element c of type CutD D such that c.Good, NormChoiceFacts (cut D c) (nchTr c nch) and Tie4 (cut D c) all hold.
- Premise 3. prN, a proof of the bundle PublishedInputsThirdLayerAlt, which collects fourteen stated results such as CuspRapidDecay, HarishChandraFinite, Green, RayField, HoweUnram and ThetaLocalInputsAlt.
- Premise 4. hX, a proof of the bundle GeometricGaloisRepCompatibility, which collects twelve stated results such as WeilRepresentationUnitaryPair, FlathFactorisation and HtCard.
- Premise 5. dzs, a proof of DepthZeroSupport, which says that for every nonarchimedean local field k, every natural number n, every π of type Irr k n, every natural number s, every function d from Fin s to the natural numbers and every family σ assigning to each a an element of Irr k (d a), if IsCuspSupport π.π d (fun a => (σ a).π) holds and there exists v in fixed π.π (KOne k (Fin n)) with v ≠ 0, then for every a there exists v in fixed (σ a).π (KOne k (Fin (d a))) with v ≠ 0.
- Premise 6. hL, a proof of RecTExists, which says that for every number field E, algebraic closure Ω, valuation subring A of Ω and finite place w of E with A lying over w, there is a map rc satisfying the condition IsRecT.
- Premise 7. A real number cDep.
- Premise 8. hF, the statement MemberAtLayerPoint for hL, which says that EvLgG holds of the predicate that sends K, B, f and T to the statement that KPx B f implies that, for all further data w, Z, Wt, p0, t, nch, n, xd and c, whenever defaultExtension hL K B f T w Z Wt p0 t nch n xd c and RXs t are nonempty and an element of type ColPin w is given, the condition GaloisPreconditions (w.D Z) nch holds.
- Premise 9. hAt, the statement that LinkedAt holds for parametersOfDependence hL cDep with the test that sends a slot Q and a linkage L to SlotNormCondition Q L applied to Closed of the property BoundAtTwoThreeFamilyFonAlt.
- Conclusion. LinkedAt holds for parametersOfDependence hL cDep with the test that sends a slot Q and a linkage L to SlotNormCondition Q L applied to Closed of the property LinkN.

This reading opens `D7`, `Ranks`, `LinkedAt`, `parametersOfDependence`, `SlotNormCondition`, `BoundAtTwoThreeFamilyFonAlt`, `KPx`, `BundleCondition` and `RecTExists`.

It does not open `Large`, `etaSum, vvTerm, dZ0, shaLen`, `Tie4, NormChoiceFacts, cut, CutD, NChoice` and `EvLgG, LargeBaseCondition, Row, RowE, IsSel`.

The reader's confidence is medium. The logical shape is fully visible, since the conclusion repeats premise hAt with BoundAtTwoThreeFamilyFonAlt replaced by LinkN and both are unfolded, but many inner conditions such as Large, etaSum, vvTerm, EvLg and the bodies of the bundled published results have no visible text.

### Line 15, `linkN_of_twGood_galoisPreconditions`

The head is `UpperTheory.GalC.linkN_of_twGood_galoisPreconditions`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Link N Fam. The line gathers 14,338 declarations and hangs from line 14, `final_of_alt`. Folded into the line are the wrappers `linkedAt_linkN_of_boundAtTwoThree` and `linkN_of_boundAtTwoThree_slot`.

Assume the bundle of seven statements that the code calls Hypotheses₂ and the statement that the code calls CutGivesAlt. Let eps be a real number and Fm a family of type FamP eps that satisfies TwGood, such that for every real x above the family threshold x1 and every index i the datum D(x,i), with the choice nch stored in the family's extra data, satisfies GaloisPreconditions and Tie4. Then Fm satisfies LinkN, which means there are real numbers C and x0 such that, for every x ≥ x0, every index i with ShaFinOdd(D(x,i)) and every integer j from 1 to m, summability of vvTerm implies that etaSum(j) is at most dZ0(j) times (C·(f·m·b·L² + (log X)²·Nc) plus the sum of vvTerm), where X is the field sc.x of L(x,i), which the family ties to x only when x1 < x.

- Premise 1. The conjunction that the code calls Hypotheses₂ holds, with its seven fields FontaineBcris, GlobalArtinReciprocity, BlochKatoLocal, LocalTateDualityK, LocalEulerCharK, LocalFinitenessK and BhattScholzeIntegral.
- Premise 2. The condition that the code calls CutGivesAlt holds, which says that every datum D with a choice nch satisfying GaloisPreconditions and Tie4 has a cut c with c.Good, NormChoiceFacts for the cut datum and transported choice, and Tie4 for the cut datum.
- Premise 3. eps is a real number and Fm is a family of type FamP eps.
- Premise 4. Fm satisfies the condition that the code calls TwGood.
- Premise 5. For every real x with x1 < x and every index i in Ix(x), both GaloisPreconditions(D(x,i), nch(x,i)) and Tie4(D(x,i)) hold, where nch(x,i) is the nch field of the family's extra data ex at x and i.
- Conclusion. LinkN Fm holds, that is, there exist real C and x0 such that for all x ≥ x0, all i in Ix(x) with ShaFinOdd(D(x,i)) and all j in {1,…,m}, the condition LinkN_at(L(x,i), j, C) holds.

```
Hypotheses₂ ∧ CutGivesAlt ⇒ ∀ eps ∈ ℝ, ∀ Fm ∈ FamP(eps), [TwGood(Fm) ∧ (∀ x ∈ ℝ, x1 < x ⇒ ∀ i ∈ Ix(x), GaloisPreconditions(D(x,i), ex(x,i).nch) ∧ Tie4(D(x,i)))] ⇒ ∃ C, x0 ∈ ℝ, ∀ x ≥ x0, ∀ i ∈ Ix(x), ShaFinOdd(D(x,i)) ⇒ ∀ j ∈ {1,…,D.R.m}, [Summable(vvTerm D) ⇒ etaSum(L,j) ≤ dZ0(j)·(C·(f·m·sc.b·sc.L² + (log sc.x)²·Nc) + Σ_l vvTerm(D,l))], where D = D(x,i), L = L(x,i), f = D.R.f, m = D.R.m
```

The reading does not open the names `TwGood`, `GaloisPreconditions` and `Tie4`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that Galois-representation preconditions and a twist-goodness condition on a family give a bound, uniform in the family, on a sum called eta in terms of a size dZ0, under finiteness of a Tate–Shafarevich-type length, and that the Hypotheses₂ fields stand for published theorems of p-adic Hodge theory and class field theory taken as assumptions.

The reader's confidence is medium. The logical shape, the quantifiers and the final inequality are fully visible, but GaloisPreconditions, Tie4, TwGoodAt, etaSum, vvTerm and shaLen have no visible bodies and several records are cut off.

The check found one error in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- A writes the bound with "(log x)²" in the same sentence that quantifies over "every x ≥ x0", while the Lean text has Real.log L.sc.x ^ 2 with L = Fm.L x i, and the dossier ties L.sc.x to x only when Fm.x1 < x, which x ≥ x0 does not give.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 5 errors in this reading and, after they were corrected, 0 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 6 findings on it, and the text was changed in 6 places. A check of the changed text then found no error.

Assume the bundle of propositions that the code calls Hypotheses₂, which is a list of seven propositions with names such as LocalTateDualityK, LocalEulerCharK, LocalFinitenessK and GlobalArtinReciprocity, and assume the proposition CutGivesAlt. Take any real number eps and any family Fm of type FamP eps, which assigns to every real x and every index i in a type Ix x a D7 record D x i together with size data and much further data and conditions. Suppose that Fm satisfies the condition TwGood, and that for every real x with x1 < x and every index i the record D x i satisfies the condition GaloisPreconditions for the choice record nch stored in the field ex of Fm, and also satisfies the condition Tie4. Then Fm satisfies LinkN, which says that there are real constants C and x0 such that for every real x ≥ x0, every index i in Ix x for which the condition ShaFinOdd holds for D x i, and every whole number j from 1 to the natural number (D x i).R.m, a certain bound on a quantity etaSum holds whenever a certain series is summable.

- Premise 1. The bundle Hypotheses₂ of seven propositions holds.
- Premise 2. The proposition CutGivesAlt holds, which says that for every D7 record D and every nch of type NChoice D such that GaloisPreconditions D nch and Tie4 D hold, there exists c of type CutD D with c.Good such that NormChoiceFacts holds for cut D c and nchTr c nch and Tie4 holds for cut D c.
- Premise 3. eps is a real number and Fm is a family of type FamP eps.
- Premise 4. The family Fm satisfies TwGood, which is TwGoodE applied to Fm and twE Fm.
- Premise 5. For every real x with Fm.x1 < x and every index i in Fm.Ix x, the record Fm.D x i satisfies GaloisPreconditions with the choice record (Fm.ex x hx i).nch and also satisfies Tie4.
- Conclusion. The family Fm satisfies LinkN, so there are real constants C and x0 such that for x ≥ x0, every index i where ShaFinOdd holds for D x i, and every j with 1 ≤ j ≤ (D x i).R.m, the bound LinkN_at (Fm.L x i) j C holds.

This reading opens `D7`, `Ranks`, `Frame`, `shaLen` and `Rows.Data`.

It does not open `etaSum`, `vvTerm`, `dZ0` and `SizeData₂`.

The reader's confidence is medium. The logical shape of the statement and the definitions of LinkN, TwGood, CutGivesAlt and Hypotheses₂ are fully visible, but etaSum, vvTerm, dZ0, SizeData₂, the many fields of GaloisPreconditions and Tie4, and parts of FamP are cut or have no visible body.

### Line 16, `ontoX_and_lamLow_of_unitaryGroupHypotheses'`

The head is `GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses'`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Surjective And Low Weight Of Unramified Exponents. The line gathers 20,036 declarations and hangs from line 5, `nonempty_hyps_definite_side_of_closed_bound`.

If the bundle of statements that the code calls UnitaryGroupThirdPlaceHypotheses holds, then both the statement called SurjectiveOntoX and the statement called LambdaLowerBound₂ hold. Each of these two says that there is ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is a K such that every family Fm of type FamP eps and every real CH with FamHyp(Fm) and Fm.Large(K, CH) satisfy a property of the pair (Fm, CH). In both properties the word eventually means from some x0 on, at all points p of the family that satisfy PointConditions'. For SurjectiveOntoX the property is that DIVinN(Fm) gives some C0 ≥ 0 such that, eventually, More(p) implies (p.S false).ON (p.N C CH) for all C ≥ C0, and for LambdaLowerBound₂ the property is that, eventually, (p.S true).L6 (p.N C CH) holds for all real C.

- Premise 1. The conjunction that the code calls UnitaryGroupThirdPlaceHypotheses holds, a record of propositions of which the dossier shows twenty-eight fields before the text is cut.
- Conclusion. SurjectiveOntoX and LambdaLowerBound₂ both hold.

```
UnitaryGroupThirdPlaceHypotheses ⇒ SurjectiveOntoX ∧ LambdaLowerBound₂, where SurjectiveOntoX = Closed(FamHyp, (Fm,CH) ↦ [DIVinN(Fm) ⇒ ∃ C0 ≥ 0, Ev(Fm, p ↦ (More(p) ⇒ ∀ C ≥ C0, ON(p.S(false), p.N(C,CH))))]), LambdaLowerBound₂ = Closed(FamHyp, (Fm,CH) ↦ Ev(Fm, p ↦ ∀ C, L6(p.S(true), p.N(C,CH)))), Closed(𝒞,P) = ∃ ε1 > 0, ∀ eps, 0 < eps ≤ ε1 ⇒ ∃ K, ∀ Fm ∈ FamP(eps), ∀ CH ∈ ℝ, 𝒞(Fm) ∧ Large(Fm,K,CH) ⇒ P(Fm,CH), and Ev(Fm,Q) = ∃ x0, ∀ x > x1 with x ≥ x0, ∀ i ∈ Ix(x), ∀ p ∈ Pt(Fm,x,i), PointConditions'(p) ⇒ Q(p)
```

The reading does not open the names `DIVinN`, `More`, `ON and L6`, `Large` and `Pt`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that a list of published results on automorphic forms on unitary groups, theta correspondence, Siegel–Weil formulas, local representation theory and Galois representations is taken as an assumption, and that the conclusions are a surjectivity statement onto something called X and a lower bound for a quantity called lambda, for all sufficiently large members of suitable families.

The reader's confidence is low. The outer quantifier structure of both conclusions is visible, but the hypothesis record is cut off and the core conditions ON, L6, More, Large, DIVinN_at and Pt are not shown.

The check found one error in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- A says the property "holds at all points p of the family from some x0 on", while the Lean text of EventuallyAtPoints requires it only for points p with p.PointConditions', and the field "says" does not state that this condition is left out.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 2 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 1 finding on it, and the text was changed in 1 place. A check of the changed text then found no error.

The theorem says that if the large bundle of hypotheses called UnitaryGroupThirdPlaceHypotheses holds, then two statements both hold. The first statement, SurjectiveOntoX, says the following. There is a threshold ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is a K of the type called TransportedAlt for which every family Fm of the type called FamP eps, and every real number CH, that satisfies the family conditions FamHyp and the condition Fm.Large K CH has a further property. If Fm satisfies the condition DIVinN, then there is a real C0 ≥ 0 and a real x0 such that for every x ≥ x0 with x > Fm.x1, every index i in Fm.Ix x and every point p over (x, i) that meets the condition called PointConditions' and the condition More, the object p.S false satisfies the relation called ON with p.N C CH for every C ≥ C0. The second statement, LambdaLowerBound₂, has the same outer frame of ε1, eps, K, Fm and CH with FamHyp and Large, but no DIVinN premise and no More premise, and it concludes that eventually, at every point p meeting PointConditions', the object p.S true satisfies the relation called L6 with p.N C CH for every real C.

- Premise 1. The proposition UnitaryGroupThirdPlaceHypotheses holds, which is a conjunction of named propositions (clozelCohomological, greenCuspidal, heckeLAdicCharacter, chebotarevDegreeOne and many more, about 60 in all according to the glossary, and the dossier's list is cut).
- Conclusion. SurjectiveOntoX and LambdaLowerBound₂ both hold.

This reading opens `D7` and `UnitaryGroupThirdPlaceHypotheses`.

It does not open `FamP`, `TransportedAlt`, `Large`, `Pt`, `PointConditions'`, `S`, `N`, `ON`, `L6`, `DIVinN_at`, `SingleIndexPlacesAreTwisted, CoreTies, RecTies` and `PageFix, PageWin, ChosenWall, ChosenE, TwGood and the other FamHyp parts`.

The reader's confidence is low. The logical frame of quantifiers and implications is fully visible, but the actual conclusions ON and L6, the objects p.S and p.N, the point and family types and most hypothesis parts have no visible bodies, and the hypothesis bundle's field list is cut in the dossier.

### Line 17, `ontoX_of_hypotheses_alt_alt`

The head is `GlobalTheory.BigOn.ontoX_of_hypotheses_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Onto X Of Prints. The line gathers 19,703 declarations and hangs from line 16, `ontoX_and_lamLow_of_unitaryGroupHypotheses'`.

If twelve named statements hold, namely GreenCuspidal, ClozelCohomological, HeckeLAdicCharacter, ChebotarevDegreeOne, CuspUAlt, BaseChangeDefiniteUnitaryGroup, BhattScholzeCrystallineLattices, HeckeLAdicCharacterAbove, CuspRapidDecay, RecTExists, DiscreteSeriesCover and CasselmanWallach, then the statement called SurjectiveOntoX holds. SurjectiveOntoX says there is ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is a K such that, for every family Fm of type FamP eps and real CH with FamHyp(Fm) and Fm.Large(K, CH), the condition DIVinN(Fm) gives a C0 ≥ 0 and an x0 beyond which every point p with PointConditions' and More(p) satisfies (p.S false).ON (p.N C CH) for all C ≥ C0.

- Premise 1. The condition that the code calls GreenCuspidal holds, defined as GlobalTheory.GLq.Green with no visible body.
- Premise 2. ClozelCohomological holds, which says that for every totally complex number field E, every a ≥ 1 and every π of type CuspSub E a, the condition IsRegAlg implies the condition IsCohomological.
- Premise 3. HeckeLAdicCharacter holds, which says that for a number field E with algebraic closure Ω there is a map art from Ideles E to Gab E Ω with IsGlobalArtin such that, for every prime l, every isomorphism ι from Qbar l to ℂ and every map n from the ring homomorphisms E → ℂ to ℤ, every χ of type HChar E with IsAlgPos χ n has a unique continuous character r into the units of Qbar l with IsLAdicOf art ι χ n r.
- Premise 4. ChebotarevDegreeOne holds, which says that for a finite Galois extension L of a number field F inside an algebraic closure, an automorphism g of L over F and a finite set S of primes, there is a prime v outside S of inertia degree 1 over ℤ with a valuation subring B of Ω that satisfies IsPlaceOver B v and whose subgroup Ine B lies inside the fixing subgroup of L and a σ with IsFrob B (normV v) σ whose restriction to L is g.
- Premise 5. CuspUAlt holds, which says that for a CM field E with algebraic closure Ω, a prime l, an isomorphism ι from Qbar l to ℂ, a ≥ 1, π of type CuspSub E a and χ of type HChar on the maximal real subfield of E, with IsRegAlg for π and IsPolarized π χ, there exist a homomorphism r from G E Ω to GL_a(Qbar l), an integer wt and a multiset-valued HT with IsGalUAlt π χ ι r wt HT.
- Premise 6. BaseChangeDefiniteUnitaryGroup holds, which unfolds to DefiniteN, saying that for a CM field E unramified at every finite prime over its maximal real subfield, every n ≥ 1 and every π with IsAutRepU there exist c, sizes N_i summing to n, and data V, σ, m with IsBaseChangeU.
- Premise 7. BhattScholzeCrystallineLattices holds, a two-part statement under the assumption IsAinf K P₀ e, giving, for every P and AI with IsStd P AI, existence of an object E of type FCrys with a map j satisfying Realises for each lattice in a representation with IsCrys, and, without the IsStd assumption, unique existence of a morphism u of FCrys objects compatible with any equivariant linear map f between modules T and T' over ℤ_[l] that satisfy Realises. This summary leaves out the binders l, K, P₀ and e of the assumption IsAinf K P₀ e.
- Premise 8. The condition that the code calls HeckeLAdicCharacterAbove holds, defined as GlobalTheory.TripleGal.CharAbove with no visible body.
- Premise 9. CuspRapidDecay holds, which says that for a datum D, a family θ with IsInfFam θ, a V with a map e satisfying IsExpFam θ V e, and a function φ on GA D V with IsAutFun, IsSmoothInf, IsUnifModerate and IsCuspFun, the condition IsRapidDecay holds.
- Premise 10. RecTExists holds, which says that for every number field E, algebraic closure Ω, valuation subring A of Ω and prime w of E with IsPlaceOver A w there exists rc with IsRecT h rc.
- Premise 11. DiscreteSeriesCover holds, which says that for all naturals p, q with p + q ≥ 1 and every T of type GrpData p q there is a map D from parameters lam with IsParam to DSRep T such that each D(lam) has HasTypes and every R in DSRep T is UnitEquiv to some D(lam).
- Premise 12. CasselmanWallach holds, which says that for an irreducible representation σ with IsURepOn on a complete complex inner product space H and a representation π with IsSmoothModRep on a complete Hausdorff space E, every linear map T₀ with IsGKMap has a linear map T that agrees with T₀ on the vectors with IsKFin, has IsSmoothGMap, is unique on smooth vectors, has closed image of the smooth vectors, and, when T₀ is nonzero on some vector with IsKFin, bounds each sobNorm of a smooth vector w by a continuous seminorm of T(w). This summary leaves out the binders n, ε and dπ and, in the last clause, the quantifier over lists S of lists of matrices in lieSet ε.
- Conclusion. SurjectiveOntoX holds.

```
GreenCuspidal ⇒ ClozelCohomological ⇒ HeckeLAdicCharacter ⇒ ChebotarevDegreeOne ⇒ CuspUAlt ⇒ BaseChangeDefiniteUnitaryGroup ⇒ BhattScholzeCrystallineLattices ⇒ HeckeLAdicCharacterAbove ⇒ CuspRapidDecay ⇒ RecTExists ⇒ DiscreteSeriesCover ⇒ CasselmanWallach ⇒ SurjectiveOntoX, where SurjectiveOntoX = ∃ ε1 > 0, ∀ eps, 0 < eps ≤ ε1 ⇒ ∃ K, ∀ Fm ∈ FamP(eps), ∀ CH ∈ ℝ, FamHyp(Fm) ∧ Large(Fm,K,CH) ⇒ [DIVinN(Fm) ⇒ ∃ C0 ≥ 0, ∃ x0, ∀ x > x1 with x ≥ x0, ∀ i ∈ Ix(x), ∀ p ∈ Pt(Fm,x,i), PointConditions'(p) ⇒ More(p) ⇒ ∀ C ≥ C0, ON(p.S(false), p.N(C,CH))]
```

The reading does not open the names `DIVinN`, `More`, `ON`, `GreenCuspidal` and `HeckeLAdicCharacterAbove`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that twelve published theorems (Green on cuspidal characters of finite general linear groups, Clozel, Hecke characters and their l-adic realisations, Chebotarev, Galois representations for polarized cuspidal representations, base change from definite unitary groups, Bhatt–Scholze on crystalline lattices, rapid decay of cusp forms, local Langlands reciprocity, discrete series classification and Casselman–Wallach globalisation) are taken as assumptions to derive a surjectivity statement onto an object called X.

The reader's confidence is medium. The twelve premises and the outer quantifier structure of the conclusion are visible, but the innermost conditions ON, More, Large, DIVinN_at, Pt and several premise predicates have no visible bodies.

The check found two errors in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- A glosses CuspRapidDecay as holding "for a datum D and a function φ on GA D V with IsAutFun, IsSmoothInf, IsUnifModerate and IsCuspFun", while the Lean text also requires IsInfFam θ and IsExpFam θ V e, and A does not say that these are left out.
- A glosses BhattScholzeCrystallineLattices as giving E and j "for each lattice in a representation with IsCrys", while the Lean text also requires IsAinf K P₀ e for both parts and IsStd P AI for the first part, and A does not say that these are left out.

A second model, Gemini, checked this reading again. 7 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found one error, which the text above corrects. A second such check found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 3 errors in this reading and, after they were corrected, 6 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 8 findings on it, and the text was changed in 7 places. A check of the changed text then found no error.

The theorem is a chain of twelve implications. If twelve propositions all hold, then the proposition that the code calls SurjectiveOntoX holds. Each of the twelve is a closed statement that the code files under the label Published or under UpperTheory, such as a Chebotarev statement with degree-one primes, a statement named after Clozel that for every π of type CuspSub E a the condition IsRegAlg of CG.mk π implies the condition GKCoh.IsCohomological π, a Bhatt–Scholze statement on crystalline lattices, a Casselman–Wallach statement, and an existence statement for maps rc satisfying the condition IsRecT. The conclusion SurjectiveOntoX says the following. There is a threshold ε₁ > 0 such that, for every eps with 0 < eps ≤ ε₁, there is an object K of the type the code calls TransportedAlt with this property. For every family Fm of the type FamP eps and every real number CH, if Fm satisfies the bundle of conditions FamHyp and the condition Fm.Large K CH, and Fm also satisfies the condition DIVinN, then there is a real C₀ ≥ 0 and a cutoff x₀ such that, for every x with proof hx of Fm.x1 < x and x ≥ x₀, every index i of type Fm.Ix x and every p of type Pt Fm x hx i, if p satisfies PointConditions' and the condition More, then for every C ≥ C₀ the relation ON holds between p.S false and p.N C CH. The meaning of the final relation ON, and of the objects it relates, is not visible in the files.

- Premise 1. The proposition GreenCuspidal, which is defined as an opaque condition the code calls GlobalTheory.GLq.Green.
- Premise 2. The proposition ClozelCohomological, which says that for every totally complex number field E, every a ≥ 1 and every π of the type CuspSub E a, if CG.mk π satisfies the condition IsRegAlg then π satisfies the condition GKCoh.IsCohomological.
- Premise 3. The proposition HeckeLAdicCharacter, which says that for every number field E with algebraic closure Ω there is a group homomorphism art from Ideles E to Gab E Ω satisfying IsGlobalArtin, such that for every prime l, every ring isomorphism ι from Qbar l to ℂ, every χ of type HChar E and every function n from the ring homomorphisms E → ℂ to ℤ with IsAlgPos χ n, there is exactly one continuous homomorphism r from G E Ω to the units of Qbar l with IsLAdicOf art ι χ n r.
- Premise 4. The proposition ChebotarevDegreeOne, which says that for every finite Galois subextension L of an algebraic closure of a number field F, every g in Gal(L/F) and every finite set S of finite places, there is a place v outside S with inertia degree 1 over ℤ, a valuation subring B over v whose inertia group (Ine) fixes L, and a Frobenius σ at B (IsFrob) whose restriction to L is g.
- Premise 5. The proposition CuspUAlt, which says that for every number field E with IsCMField E, every algebraic closure Ω of E, every prime l, every ring isomorphism ι from Qbar l to ℂ, every natural number a ≥ 1, every π of type CuspSub E a and every χ of type HChar (maximalRealSubfield E), if (CG.mk π).IsRegAlg and IsPolarized π χ hold, then there exist a homomorphism r from G E Ω to GL (Fin a) (Qbar l), an integer wt and a function HT from the ring homomorphisms E → Qbar l to multisets of integers with IsGalUAlt π χ ι r wt HT.
- Premise 6. The proposition BaseChangeDefiniteUnitaryGroup, defined as DefiniteN, which says that for every number field E with IsCMField E such that every finite place of E is unramified over the maximal real subfield, every natural number n ≥ 1 and every complex subspace π of the functions from UA E n to ℂ with IsAutRepU π, there exist a natural number c, sizes N i with a proof h that they sum to n, complex subspaces V i of Sm E (N i), a family σ that gives for each i and each finite place w an element of SmIrr (GL (Fin (N i)) (w.adicCompletion E)), and a family m that gives for each i and each ring homomorphism E → ℂ a multiset of complex numbers, with IsBaseChangeU π h V σ m.
- Premise 7. The proposition BhattScholzeCrystallineLattices, which for every prime l, finite extension K of ℚ_l and A_inf-object P₀ with IsAinf says that for every P of type LocPrime l with some AI satisfying IsStd P AI, every finite extension LL and every lattice T with IsCrys (P.PD K) T.ρ comes from some F-crystal E through a realising map j (Realises), and that for any ℤ_l-modules T and T' with maps ρ and ρ' and F-crystals E and E' realised through j and j', every ℤ_l-linear map f from T to T' that commutes with ρ and ρ' comes from exactly one morphism u of F-crystals.
- Premise 8. The proposition HeckeLAdicCharacterAbove, defined as an opaque condition the code calls GlobalTheory.TripleGal.CharAbove.
- Premise 9. The proposition CuspRapidDecay, which says that for every D of the record type D7 and every admissible θ, V and e (IsInfFam, IsExpFam), every function φ from GA D V to ℂ that satisfies IsAutFun V φ, IsSmoothInf V e φ, IsUnifModerate θ V e φ and IsCuspFun V φ satisfies IsRapidDecay θ V φ.
- Premise 10. The proposition RecTExists, which says that for every number field E, algebraic closure Ω, valuation subring A of Ω and finite place w with A over w, there is a map rc with IsRecT h rc.
- Premise 11. The proposition DiscreteSeriesCover, which says that for all natural numbers p and q with 1 ≤ p + q and every T of type GrpData p q there is a map D from functions lam from Ix p q to ℚ satisfying IsParam lam to DSRep T such that every D lam satisfies HasTypes (D lam) lam.1 and for every R of type DSRep T there is some lam satisfying UnitEquiv R (D lam).
- Premise 12. The proposition CasselmanWallach, which says that for every natural number n, every ε of type Fin n → Bool, every σ on a complex Hilbert space H with IsURepOn (UJset ε) σ and IsIrredOn (UJset ε) σ, and every complete Hausdorff uniform complex vector space E with seminorms p and maps π and dπ satisfying IsSmoothModRep ε p π dπ, every complex linear map T₀ from H to E with IsGKMap ε σ π dπ T₀ has a complex linear map T from H to E that agrees with T₀ on the vectors satisfying IsKFin ε σ, satisfies IsSmoothGMap ε σ p π T, is unique on the vectors satisfying SmoothVec (lieSet ε) σ among the maps with these two properties, has closed image of the set of vectors satisfying SmoothVec (lieSet ε) σ, and, when T₀ is nonzero on some vector with IsKFin ε σ, has for every list S of lists of n by n complex matrices whose members all belong to lieSet ε a continuous seminorm q on E such that sobNorm σ S w ≤ q (T w) for every w satisfying SmoothVec (lieSet ε) σ.
- Conclusion. SurjectiveOntoX holds, that is, for all small enough eps there is a K such that every family Fm satisfying FamHyp, Large K CH and DIVinN has a constant C₀ ≥ 0 and a cutoff x₀ beyond which every point p satisfying PointConditions' and More satisfies (p.S false).ON (p.N C CH) for all C ≥ C₀.

This reading opens `D7`, `Host`, `Rows.Data` and `IsRecT`.

It does not open `ON`, `FamP, Pt, TransportedAlt, Large, PointConditions', S, N`, `DIVinN_at, SingleIndexPlacesAreTwisted, CoreTies, RecTies`, `GreenCuspidal`, `HeckeLAdicCharacterAbove` and `CuspSub, IsRegAlg, IsCohomological, IsPolarized, IsGalUAlt, IsGlobalArtin, IsLAdicOf, IsAlgPos, IsFrob, Ine, IsRapidDecay, IsCuspFun, DSRep, UnitEquiv, IsParam, IsBaseChangeU, IsAutRepU, Realises, FCrys`.

The reader's confidence is low. The quantifier structure of the conclusion and of most premises is visible, but the final relation ON, the objects S and N, the family type FamP, the point type Pt and most component conditions have no body in the three files, so what is actually claimed cannot be pinned down.

### Line 18, `open_orbit_of_unramified_exponents_alt`

The head is `GlobalTheory.Fc.S0.Open0ProofU.open_orbit_of_unramified_exponents_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Open Orbit Of Unramified Exponents. The line gathers 12,471 declarations and hangs from line 5, `nonempty_hyps_definite_side_of_closed_bound`. Folded into the line is the wrapper `open0_of_unitary_group_hypotheses`.

Assume a bundle of hypotheses that the code calls UnitaryGroupThirdPlaceHypotheses, which is a conjunction of at least 28 named statements. Then for every proof hL of a statement that the code calls RecTExists and for every real number cDep, a condition that the code calls OpenParameterStatements holds for the parameter object parametersOfDependence hL cDep. That condition is a conjunction of twelve statements, each of the form LinkedAt p r, where p is that parameter object and r runs through twelve named row conditions.

- Premise 1. The bundle UnitaryGroupThirdPlaceHypotheses holds, which is a conjunction of at least 28 named statements whose list is cut off in the dossier.
- Premise 2. hL is a proof of RecTExists, which says that for every number field E, algebraic closure Ω of E, valuation subring A of Ω, height one prime w of the ring of integers of E and proof h of a condition that the code calls IsPlaceOver A w, there exists an object rc that satisfies a condition that the code calls IsRecT h rc.
- Conclusion. For every real cDep, all twelve statements LinkedAt p r hold with p = parametersOfDependence hL cDep and r equal in turn to SlotPrimitivityCondition, SlotLambdaPrimeCondition, SlotDivisorCondition, SlotDecompositionPointCondition, SlotSelectionJumpCondition, Row_tie_alt, RowLabelCondition, RowGoodnessCondition, GeometricWeakCompatibility', RowMultiplicityCondition, RowKappaCondition and RowDefectCondition.

```
UnitaryGroupThirdPlaceHypotheses ⇒ ∀ hL proving RecTExists, ∀ cDep ∈ ℝ, with p = parametersOfDependence(hL, cDep) = parametersOfExtension(extensionWithList(hL, cDep), SExt.none, geoCl(anyGeometry)), ⋀_{r ∈ {SlotPrimitivity, SlotLambdaPrime, SlotDivisor, SlotDecompositionPoint, SlotSelectionJump, Row_tie_alt, RowLabel, RowGoodness, GeometricWeakCompatibility', RowMultiplicity, RowKappa, RowDefect}} LinkedAt(p, r), where LinkedAt(p, r) = Lg1(KPx, IsBuiltE(p.s), IsGoodE(p.s), S ↦ r(S, BundleLinkage(p)))
```

The reading does not open the names `UnitaryGroupThirdPlaceHypotheses`, `RecTExists`, `LinkedAt`, `parametersOfDependence`, `Parameters`, `Slot conditions (Primitivity, LambdaPrime, Divisor, DecompositionPoint, SelectionJump, Row_tie_alt)`, `RowLabelCondition`, `RowGoodnessCondition, RowKappaCondition, RowMultiplicityCondition, RowDefectCondition`, `GeometricWeakCompatibility'` and `BundleCondition`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that a list of published theorems about automorphic forms, Galois representations and unitary groups is assumed, together with the existence of a local Langlands type reciprocity map, and that the conclusion is a package of twelve row conditions for a construction that depends on one real constant, but the dossier does not show this.

The reader's confidence is low. The outer shape is fully visible, but the hypothesis bundle is cut off, eleven definitions are left out, and the conclusion rests on Lg1, Row, AtAll, BundleLinkage and p.s, none of which has a body in this dossier.

The check found no error in this reading.

The check found one error in the second reading, which the text above does not use.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 2 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 1 finding on it, and the text was changed in 1 place. A check of the changed text then found no error.

The theorem says that if the hypothesis bundle the code calls UnitaryGroupThirdPlaceHypotheses holds, then a conclusion follows for every proof hL of the proposition RecTExists and for every real number cDep. RecTExists says that for every number field E, every algebraic closure Ω of E, every valuation subring A of Ω and every nonzero prime w of the ring of integers of E that A lies over, there is a map rc that satisfies a condition the code calls IsRecT. The hypothesis bundle is the joint assertion of a long list of named statements, most of them in the namespace Published, such as BernsteinUnitaryProductIrreducible, ChebotarevDegreeOne, which gives for every finite set S of primes a prime outside S of inertia degree 1 with a Frobenius condition IsFrob, and GlobalArtinReciprocity. The conclusion is that the parameter record parametersOfDependence hL cDep satisfies OpenParameterStatements. This means that twelve row or slot conditions each hold in the sense the code calls LinkedAt for that record.

- Premise 1. The hypothesis bundle UnitaryGroupThirdPlaceHypotheses holds, which is the joint truth of all its named fields, among them ClozelCohomological, GreenCuspidal, HeckeLAdicCharacter, ChebotarevDegreeOne, BernsteinUnitaryProductIrreducible, GlobalArtinReciprocity, HarishChandraFinite and more (the dossier's listing is cut, and the glossary counts 60 fields).
- Premise 2. hL is any proof of RecTExists, the statement that a map rc with IsRecT h rc exists for every number field, algebraic closure, valuation subring and prime that the subring lies over.
- Premise 3. cDep is any real number.
- Conclusion. The record parametersOfDependence hL cDep satisfies OpenParameterStatements, which means that each of twelve conditions is LinkedAt that record, namely the primitivity, lambda prime, divisor, decomposition point and selection jump slot conditions, the tie, label, goodness, geometric weak compatibility, multiplicity, kappa and defect row conditions.

This reading opens `RecTExists`, `D7`, `UnitaryGroupThirdPlaceHypotheses`, `LinkedAt`, `parametersOfDependence`, `KPx`, `BundleCondition` and `Row`.

It does not open `IsRecT`, `AtAll, Ind.EvW, Ind.EvWC`, `Lg1 inner parts (EvLg, IsBuiltE, IsGoodE, BundleLinkage, p.s)` and `Published fields with unopened bodies (GreenCuspidal, HeckeLAdicCharacterAbove, BaseChangeDefiniteUnitaryGroup, DoublingMethodLocalZetaIntegrals, GeometricLemmaFiltration, JacquetShalika, CuspUAlt, CarUAlt, GreenR, and others)`.

The reader's confidence is low. The logical shape is fully visible, but the content of the conclusion rests on Row, AtAll, EvW, EvLg, Built, GoodO and many bundle conditions with no body, and the listing of the hypothesis bundle is cut.

### Line 19, `miStarRow_alt_alt`

The head is `GlobalTheory.miStarRow_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Main Theorem Published Inputs Third. The line gathers 10,783 declarations and hangs from line 18, `open_orbit_of_unramified_exponents_alt`. Folded into the line is the wrapper `main_theorem_published_inputs_third_alt_alt`.

Assume fourteen named statements, thirteen of them from a namespace called Published or Hk3 and one called HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent. Then for every proof hL of RecTExists and every N, S and Γ, two statements hold for the parameter record p = ⟨RX, N, S, Γ⟩. Both say that there is a slot R with LargeBaseCondition KPx (IsBuiltE p.s) R such that a Row statement holds at the slot sAnd (IsGoodE p.s) R with the linkage BundleLinkage p, the first with the property AtAll MI and the second with the property Ind.EvW MI, where MI is one fixed condition on a bundle b that the code calls MIstar2.

- Premise 1. A condition that the code calls Published.HarishChandraFinite.
- Premise 2. A condition that the code calls Published.CuspRapidDecay.
- Premise 3. A condition that the code calls Published.DiscreteSeriesCover.
- Premise 4. A condition that the code calls Published.HarishChandraModules.
- Premise 5. A condition that the code calls Published.CasselmanWallach.
- Premise 6. A condition that the code calls Hk3.HoweUnram.
- Premise 7. A condition that the code calls Published.WeilRepresentationUnitaryPair.
- Premise 8. A condition that the code calls Published.WeilSiegelFormulaUnitary.
- Premise 9. A condition that the code calls Published.SiegelWeilUnitaryConvergent.
- Premise 10. A condition that the code calls Published.DoublingMethodLocalZetaIntegrals, which is an abbreviation of ResidueKilled.DM.
- Premise 11. A condition that the code calls Published.UnramifiedDoublingGL.
- Premise 12. A condition that the code calls Published.DiscreteSeriesClassification.
- Premise 13. A condition that the code calls Published.StrongApproxSU.
- Premise 14. A second and different condition that the code calls HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent.
- Premise 15. hL is a proof of RecTExists.
- Conclusion. For all N of type NormChoiceExtension hL, S of type SExt and Γ of type GeoP, both LinkedAt p (Q, L ↦ Row Q L (AtAll MI)) and LinkedAt p RowMultiplicityCondition hold, where p = parametersOfExtension N S Γ.

```
H1 ⇒ H2 ⇒ … ⇒ H14 ⇒ ∀ hL proving RecTExists, ∀ N, ∀ S, ∀ Γ, with p = ⟨RX, N, S, Γ⟩ and MI(b) = MIstar2(toCx3(b.B.Q.Rl, b.B.Q.F), eV(b.B.Q.F, toCx3(b.B.Q.Rl, b.B.Q.F).zs), b.B.Q.sEE), [∃ R, LargeBaseCondition(KPx, IsBuiltE(p.s), R) ∧ Row(sAnd(IsGoodE(p.s), R), BundleLinkage(p), AtAll(MI))] ∧ [∃ R', LargeBaseCondition(KPx, IsBuiltE(p.s), R') ∧ Row(sAnd(IsGoodE(p.s), R'), BundleLinkage(p), EvW(MI))], where Row(Q, Lk, H) ⇔ ∃ E, RowE(Q, Lk, E) ∧ ∀ 𝒜, ∀ σ, IsSel(Q, Lk, E, 𝒜, σ) ⇒ H(𝒜, σ), and AtAll(MI)(𝒜, σ) ⇔ ∀ eps, ∀ Fm ∈ FamP(eps), ∀ hc proving 𝒜(Fm), ∀ x ∈ ℝ with Fm.x1 < x, ∀ i ∈ Fm.Ix(x), MI(σ(Fm, hc, x, i))
```

The reading does not open the names `RowMultiplicityCondition`, `MIstar2`, `KPx`, `IsBuiltE, IsGoodE, BundleLinkage, p.s`, `BundleCondition`, `RecTExists`, `NormChoiceExtension, SExt, GeoP`, `Published.HarishChandraFinite`, `Published.CuspRapidDecay`, `Published.DiscreteSeriesCover`, `Published.HarishChandraModules`, `Published.CasselmanWallach`, `Hk3.HoweUnram`, `Published.WeilRepresentationUnitaryPair`, `Published.WeilSiegelFormulaUnitary`, `Published.SiegelWeilUnitaryConvergent`, `Published.DoublingMethodLocalZetaIntegrals`, `Published.UnramifiedDoublingGL`, `Published.DiscreteSeriesClassification`, `Published.StrongApproxSU` and `HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the theorem derives, from published results on automorphic forms, the Weil representation, the Siegel–Weil formula and discrete series, a multiplicity statement (MI star) for every selected bundle in a row of a larger construction, in both an everywhere form and an eventual form, but the dossier does not show this.

The reader's confidence is medium. The logical skeleton through LinkedAt, Lg1, Row and AtAll is visible, but the central property MIstar2 and the names RowE, IsSel, Ind.EvW, LargeBaseCondition and sAnd have no bodies, and 129 definitions are left out.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 0 errors in this reading and, after they were corrected, 2 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 16 findings on it, and the text was changed in 15 places. A check of the changed text then found no error.

Assume fourteen propositions that the code names after published results, from HarishChandraFinite through the second proposition called SiegelWeilUnitaryConvergent, which lives in the HeckeCharacterZeroLocus namespace. Then for every proof hL of the statement RecTExists, every norm-choice extension N over hL, every S of type SExt and every geometric predicate Γ of type GeoP, two claims hold for the parameter record p = parametersOfExtension N S Γ, which is the four-part record made of RX, N, S and Γ. The first claim is LinkedAt p r, where r takes a slot Q and a linkage L to the proposition Row Q L (AtAll R). Here R is the test that, for a bundle b, holds when the condition MIstar2 holds for the complex datum b.B.Q.Rl.toCx3 b.B.Q.F, with arguments b.B.Q.F.eV applied to that datum's zs and b.B.Q.sEE. The second claim is LinkedAt p RowMultiplicityCondition, which is the same row statement with the test wrapped by an operator the code calls Ind.EvW in place of AtAll. Unfolded, each claim says that there is a slot R0 such that a condition the code calls LargeBaseCondition holds for KPx, IsBuiltE p.s and R0, and such that the row statement holds at the slot that is the pointwise conjunction of IsGoodE p.s with R0, paired with the linkage BundleLinkage p.

- Premise 1. The proposition HarishChandraFinite, which says that the complex span of the set that the code calls forms θ V U ε fr ρ c is finite-dimensional, for every D7 record D, every family θ with IsInfFam θ, every V of type HSp D, every open subgroup U of GA D V, every pair ε and fr with IsFrameFam V ε fr, every family of finite-dimensional complex spaces W τ with representations ρ τ of Formalism.REAL.KG (ε τ) that satisfy IsContRep, and every c from D.what₂.Tau and ℕ to ℂ.
- Premise 2. The proposition CuspRapidDecay, which says that for every D7 record D, every family θ with IsInfFam θ, every V of type HSp D and every map e from LieInf V to GA D V with IsExpFam θ V e, every complex function φ on GA D V with IsAutFun V φ, IsSmoothInf V e φ, IsUnifModerate θ V e φ and IsCuspFun V φ satisfies a condition the code calls IsRapidDecay θ V φ.
- Premise 3. The proposition DiscreteSeriesCover, which says that for all natural numbers p and q with p + q ≥ 1 and every T of type GrpData p q there is a family D of objects of type DSRep T, indexed by the maps lam from Ix p q to ℚ with IsParam lam, such that HasTypes (D lam) lam.1 holds for every lam and every R of type DSRep T satisfies UnitEquiv R (D lam) for some lam.
- Premise 4. The proposition HarishChandraModules, which is HarishChandraModulesOn T for all natural numbers p and q with p + q ≥ 1 and all T of type GrpData p q, together with KFiniteAnalyticUJ.
- Premise 5. The proposition CasselmanWallach, which says that for every natural number n and every ε from Fin n to Bool, every map σ from complex n by n matrices to continuous linear maps of a complex Hilbert space H with IsURepOn (UJset ε) σ and IsIrredOn (UJset ε) σ, every complete Hausdorff complex space E with seminorms p and maps π and dπ with IsSmoothModRep ε p π dπ, and every linear map T₀ from H to E with IsGKMap ε σ π dπ T₀, there is a linear map T from H to E that agrees with T₀ on the vectors with IsKFin ε σ, satisfies IsSmoothGMap ε σ p π T, agrees on the vectors with SmoothVec (lieSet ε) σ with every other such map, sends the set of those vectors to a closed set, and, when T₀ is nonzero on some vector with IsKFin, admits for every list S of lists of matrices in lieSet ε a continuous seminorm q with sobNorm σ S w ≤ q (T w) for every w with SmoothVec (lieSet ε) σ w.
- Premise 6. The proposition HoweUnram, which says that for a complete valued field L of characteristic zero and data ϖ, σ, q, δ, n, n', JS, JT and ψ, a complex module M, a map ρ and a homomorphism ω from the product of Formalism.UG.UJ σ JS and Formalism.UG.UJ σ JT to the endomorphisms of M with LocPair ϖ σ q δ JS JT ψ ρ ω, and for every nonzero s in M with LocVac ρ s whose images ρ x s span M, every w fixed by ω (g, 1) for all g in Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) lies in the complex span of the vectors ω (1, h) s, and every w fixed by ω (1, h) for all h in Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) lies in the complex span of the vectors ω (g, 1) s.
- Premise 7. The proposition WeilRepresentationUnitaryPair, which says that for every D7 record D, every additive character ψ of AF D.host.F with IsStdChar D ψ (-1), all S and T of type HSp D and all characters χS and χT from the units of AE D to the circle with IsHeckeChar D χS, IsHeckeChar D χT, ResEta D χS S.rank and ResEta D χT T.rank, there is a homomorphism ω from GA D S × GA D T to the complex linear endomorphisms of the functions from WO S T to ℂ with IsWeilDatumO ψ S T χS χT ω.
- Premise 8. The proposition WeilSiegelFormulaUnitary, which says two things for a D7 record D, A and B of type HSp D and a Haar measure m on GA D B with 1 ≤ A.rank and either wittIdx B = 0 or A.rank + wittIdx B < B.rank. First, for every d and every basis ε of D.host.E over D.host.F there is a seminorm ν with IsContSeminorm ν such that absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) for every φ. Second, for every ψ, χ and ω with IsWeilDatumO ψ (dblSp A) B 1 χ ω and every f with IsThetaFunO ψ (dblSp A) B f, the function descend (GQ B) (fun h => thetaKO ω g h f) is integrable against autMeasure B m for every g, and, when 2 · A.rank < B.rank, for every ν and 𝓖 with IsCovolOne (ratL B A) ν 𝓖 the condition LeftInv (siegelQ A) (swSection A B ν 𝓖 ω f) holds and for every g the condition CosetConv holds and cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g equals the average of that function against autMeasure B m.
- Premise 9. The proposition GlobalTheory.Published.SiegelWeilUnitaryConvergent, which says that for a D7 record D, an additive character ψ and A and B of type HSp D with A.rank < B.rank, B.rank ≤ 2 · A.rank and A.rank + wittIdx B < B.rank, and for further data χB, ω, a, θ, sS, sB, μ, 𝓨, ν and f under the hypotheses IsWeilDatumO, IsMaj, HasIwasawa, IsInfFam, IsCartanInv for sS and for sB, a commutation condition on sS, IsCovolOne, that ν is a Haar measure, and IsFockVec, the function AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ω g h f) is integrable against autMeasure B ν for every g and Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B) (thetaMean ω ν f) holds.
- Premise 10. The proposition DoublingMethodLocalZetaIntegrals, which is by definition the proposition the code calls ResidueKilled.DM.
- Premise 11. The proposition UnramifiedDoublingGL, which says that for a field k of characteristic zero with IsNonarchimedeanLocalField k, a natural number n, a Haar measure μ on GL (Fin n) k with μ (KO k (Fin n)) = 1, a representation π of GL (Fin n) k on a complex module V and α from Fin n to ℂˣ with HasSatake π α, and a function ω from GL (Fin n) k to ℂ with IsZonal π (KO k (Fin n)) ω, there is a real s₀ such that for every complex s with s₀ < Re s the function g ↦ sphSection k (Fin n) s (io k (Fin n) (g, 1)) · ω g is integrable against μ and its integral equals lFactor (resCard k) α (s + 1/2) · lFactor (resCard k) α⁻¹ (s + 1/2) · invNormFactor (resCard k) n s.
- Premise 12. The proposition DiscreteSeriesClassification, which says that for every natural number n there are complex inner product spaces H ε lam with maps π ε lam from complex n by n matrices to continuous linear maps of H ε lam such that two things hold. First, whenever lam is strictly decreasing and every lam a − (n − 1)/2 is an integer, H ε lam is complete and nontrivial, π ε lam satisfies IsURepOn (UJset ε), IsIrredOn (UJset ε), IsSqIntOn ε and HasInfChar ε for lam, exactly one submodule S satisfies IsKTypeOf ε (π ε lam) (lam + rhoN ε − rhoC ε) S, and every μ that has a submodule with IsKTypeOf equals lam + rhoN ε − rhoC ε plus a sum of natural multiples c a b of root a b in which c a b is nonzero only for a < b. Second, every complete nontrivial complex inner product space H' with a map σ that satisfies IsURepOn (UJset ε), IsIrredOn (UJset ε) and IsSqIntOn ε has a permutation s with s a < s b whenever a < b and ε (s a) = ε (s b), a strictly decreasing mu of the same form, and a linear isometric equivalence T from H' to H (ε ∘ s) mu with T (σ (g.submatrix s.symm s.symm) v) = π (ε ∘ s) mu g (T v) for every g in UJset (ε ∘ s) and every v.
- Premise 13. The proposition StrongApproxSU, which says that for number fields F and E with E an algebra over F and an F-algebra map σ of E with IsCMExt F E σ, every M ≥ 2 and every M by M matrix J over E with IsHermND σ J, every finite set S₁ of infinite places of F, every finite set S₂ of height one primes of the ring of integers of F and every ε of type AF F with IsPlacesIdem S₁ S₂ ε such that SUSupp σ J ε is not compact, every g in SUAdelic σ J lies in the closure of the set of products γ · h in HA (AF F) σ J with γ in SURat σ J and h in SUSupp σ J ε.
- Premise 14. The proposition HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent, which says that a condition the code calls SiegelWeilAt F E σ M J holds for all number fields F and E with E an algebra over F, every F-algebra map σ of E with IsCMExt F E σ, every natural number M and every M by M matrix J over E with IsHermND σ J.
- Conclusion. For all hL, N, S and Γ, the parameter record parametersOfExtension N S Γ is linked both to the row statement that every selected bundle satisfies MIstar2 at every index beyond the threshold and to RowMultiplicityCondition.

This reading opens `D7`, `LinkedAt`, `MIstar2`, `KPx`, `BundleCondition` and `RecTExists`.

It does not open `LargeBaseCondition`, `RowE`, `IsSel`, `Ind.EvW`, `RX`, `toCx3, eV, zs, sEE` and `MIDat, MIUnit2, MIid, AuNZ`.

The reader's confidence is low. The logical shape is visible through LinkedAt, Row and AtAll, but the core conditions MIstar2 internals, RowE, IsSel, EvW, LargeBaseCondition and RX have no visible body, so the mathematical content of the conclusion cannot be seen.

### Line 20, `miStarRowClosing_alt_alt`

The head is `GlobalTheory.miStarRowClosing_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Main Theorem Published Inputs Variant. The line gathers 10,559 declarations and hangs from line 19, `miStarRow_alt_alt`. Folded into the line is the wrapper `main_theorem_published_inputs_variant_alt_alt`.

Assume thirteen named statements from the namespaces Published and Hk3, and assume a statement RowDiag about the pair of conditions IsScaleWithBoundedGamma D L C' and RankMu D u for all u. Then for every proof hL of RecTExists and every parameter record p, if for every context K and every point q of type WPt p.s K the type RXs q.x.what₂ is nonempty, then RowE holds for the slot IsGoodE p.s, the linkage BundleLinkage p and the property MI. Unfolded, RowE says that a condition EvP holds of the statement, about a pair κ and K that EvP binds, that for every point β of type BPt K with β.Is (IsGoodE p.s), every real c and every bundle b linked to β by BundleLinkage p, the condition that the code calls MIstar2 holds for b.

- Premise 1. A condition that the code calls Published.HarishChandraFinite.
- Premise 2. A condition that the code calls Published.CuspRapidDecay.
- Premise 3. A condition that the code calls Published.DiscreteSeriesCover.
- Premise 4. A condition that the code calls Published.HarishChandraModules.
- Premise 5. A condition that the code calls Published.CasselmanWallach.
- Premise 6. A condition that the code calls Hk3.HoweUnram.
- Premise 7. A condition that the code calls Published.WeilRepresentationUnitaryPair.
- Premise 8. A condition that the code calls Published.WeilSiegelFormulaUnitary.
- Premise 9. A condition that the code calls Published.SiegelWeilUnitaryConvergent.
- Premise 10. A condition that the code calls Published.DoublingMethodLocalZetaIntegrals, which is an abbreviation of ResidueKilled.DM.
- Premise 11. A condition that the code calls Published.UnramifiedDoublingGL.
- Premise 12. A condition that the code calls Published.DiscreteSeriesClassification.
- Premise 13. A condition that the code calls Published.StrongApproxSU.
- Premise 14. RowDiag of the condition E(D, L, C') that says IsScaleWithBoundedGamma D L C' holds and RankMu D u holds for every u.
- Premise 15. hL is a proof of RecTExists.
- Premise 16. For the given p, for every context K and every q of type WPt p.s K, the type RXs q.x.what₂ has at least one element.
- Conclusion. RowE (IsGoodE p.s) (BundleLinkage p) MI holds, where MI is the property of a bundle b that the code writes as (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE.

```
H1 ⇒ … ⇒ H13 ⇒ RowDiag(E) ⇒ ∀ hL proving RecTExists, ∀ p ∈ Parameters(hL), (∀ K, ∀ q ∈ WPt(p.s, K), RXs(q.x.what₂) ≠ ∅) ⇒ EvP(κ, K ↦ ∀ β ∈ BPt(K), β.Is(IsGoodE(p.s)) ⇒ ∀ c ∈ ℝ, ∀ b ∈ BundleCondition(β.D, β.O, c), BundleLinkage(p)(K, β, c, b) ⇒ MI(b)), where E(D, L, C') ⇔ [∃ ℓ ∈ SizeData₂(D), ℓ.sc.L = L ∧ 8·ℓ.CGam ≤ C' ∧ 1 ≤ ℓ.CGam] ∧ ∀ u, d0(D, u) = duStar_u · (T_u^k − 1)^f, RowDiag(E) ⇔ ∀ Cg, cb, Cu, cT, CT ∈ ℝ, 0 < cb ⇒ 0 < cT ⇒ ∃ C, C'₀, Cl₀ ∈ ℝ, 1 ≤ C ∧ ∀ C' ≥ C'₀, ∀ Cl ≥ Cl₀, ∀ D, L, u, TrueE(D) ⇒ E(D, L, C') ⇒ HD(D, L, C', Cl, Cg, cb, Cu, cT, CT) ⇒ TwoTerm(D, u, 4(exp(C·mfL(D, L)) + 1), 4·exp(−kfk(D)/2) + 2·exp(−kfk(D))), and EvP(P) ⇔ ParEv(κ ↦ κ.Pos ⇒ ∃ x0 ∈ ℝ, ∀ K, κ.Of(K) ⇒ x0 ≤ K.s.x ⇒ P(κ, K))
```

The reading does not open the names `EvP`, `MIstar2`, `SDiag`, `TrueE, HD`, `BundleWitness`, `IsGoodE`, `Parameters`, `WPt`, `RXs`, `Ctx`, `BPt`, `RecTExists` and `The thirteen Published and Hk3 hypotheses`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that this is the closing step for a multiplicity (MI star) row, which shows that for all large enough scales every good point with a linked bundle has the multiplicity property, given published analytic inputs, a diagonal two-term estimate and the existence of certain row data at every weighted point, but the dossier does not show this.

The reader's confidence is medium. The premises RowDiag, IsScaleWithBoundedGamma and RankMu and the shape of RowE and EvP are visible, but MIstar2, ParEv, TwoTerm, HD, the projections β.Is and p.s and 140 left out definitions keep the core content opaque.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 1 errors in this reading and, after they were corrected, 1 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 10 findings on it, and the text was changed in 10 places. A check of the changed text then found no error.

The theorem says that if fourteen given statements all hold, then a certain conclusion holds for every proof hL of the statement the code calls RecTExists and for every parameter record p built over hL. The first thirteen are statements from the GlobalTheory.Published and GlobalTheory.Hk3 namespaces, such as HarishChandraFinite, CasselmanWallach, WeilSiegelFormulaUnitary and StrongApproxSU. The fourteenth is RowDiag applied to a predicate E. Here E D L C' holds when D has size data whose scale has L as its field L and whose constant CGam satisfies 1 ≤ CGam and 8·CGam ≤ C', and when for every word u the complex dimension of the space D.s.Cu u equals duStar·(T^k − 1)^f. For each such hL and p there is one more premise, namely that for every context K and every point q of type WPt p.s K the record type RXs q.x.what₂ has an element. The conclusion is RowE for the slot IsGoodE p.s and the linkage BundleLinkage p, with a target predicate that requires MIstar2 to hold for the data read off each linked bundle b.

- Premise 1. HarishChandraFinite holds. For every D in D7, every family θ with IsInfFam θ, every V in HSp D, every open subgroup U of GA D V, all families ε and fr with IsFrameFam V ε fr, every family of finite-dimensional representations ρ with IsContRep for each of them and every c, the complex span of the set the code calls forms θ V U ε fr ρ c is finite-dimensional.
- Premise 2. CuspRapidDecay holds. For every D in D7, every family θ with IsInfFam θ, every V in HSp D and every family e with IsExpFam θ V e, every function φ from GA D V to the complex numbers that satisfies IsAutFun V φ, IsSmoothInf V e φ, IsUnifModerate θ V e φ and IsCuspFun V φ satisfies the condition the code calls IsRapidDecay θ V φ.
- Premise 3. DiscreteSeriesCover holds. For all natural numbers p and q with 1 ≤ p + q and every T of type GrpData p q there is a family D from the subtype of functions lam of type Ix p q → ℚ satisfying IsParam lam to DSRep T, such that each D lam satisfies HasTypes (D lam) lam.1 and every R of type DSRep T satisfies UnitEquiv R (D lam) for some lam.
- Premise 4. HarishChandraModules holds. HarishChandraModulesOn T holds for all p and q with 1 ≤ p + q and every T, and KFiniteAnalyticUJ holds.
- Premise 5. CasselmanWallach holds. For every natural number n, every ε of type Fin n → Bool, every complex Hilbert space H with a map σ of type Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) satisfying IsURepOn (UJset ε) σ and IsIrredOn (UJset ε) σ, every complete Hausdorff complex vector space E with a uniform additive group structure, a sequence p of seminorms on E and maps π and dπ of type Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E) satisfying IsSmoothModRep ε p π dπ, and every complex linear map T₀ from H to E satisfying IsGKMap ε σ π dπ T₀, there exists a complex linear map T from H to E agreeing with T₀ on every v with IsKFin ε σ v, satisfying IsSmoothGMap ε σ p π T, agreeing on every w with SmoothVec (lieSet ε) σ w with every other such map T', with the image under T of the set of w satisfying SmoothVec (lieSet ε) σ w closed, and such that if T₀ v ≠ 0 for some v with IsKFin ε σ v then for every list S of lists of matrices in lieSet ε there exists a continuous seminorm q on E satisfying sobNorm σ S w ≤ q (T w) for every w with SmoothVec (lieSet ε) σ w.
- Premise 6. HoweUnram holds. For every tuple satisfying LocPair ϖ σ q δ JS JT ψ ρ ω and every nonzero s of type M satisfying LocVac ρ s whose translates ρ x s span M over ℂ, every vector w in M satisfying ω (g, 1) w = w for every g in UJ σ JS whose coercion to GL (Fin n) L lies in GLint (Fin n) (intL L) belongs to the complex span of the translates ω (1, h) s over h in UJ σ JT, and symmetrically every vector w in M satisfying ω (1, h) w = w for every h in UJ σ JT whose coercion to GL (Fin n') L lies in GLint (Fin n') (intL L) belongs to the complex span of the translates ω (g, 1) s over g in UJ σ JS.
- Premise 7. WeilRepresentationUnitaryPair holds. For every D of type D7, every additive character ψ from AF D.host.F to ℂ, all S and T of type HSp D, and all group homomorphisms χS and χT from (AE D)ˣ to Circle satisfying IsStdChar D ψ (-1), IsHeckeChar D χS, IsHeckeChar D χT, ResEta D χS S.rank and ResEta D χT T.rank, there exists a homomorphism ω from GA D S × GA D T to Module.End ℂ (WO S T → ℂ) satisfying IsWeilDatumO ψ S T χS χT ω.
- Premise 8. WeilSiegelFormulaUnitary holds. For every D of type D7, all A and B of type HSp D, and every Haar measure m on GA D B with 1 ≤ A.rank and either wittIdx B = 0 or A.rank + wittIdx B < B.rank, every d and basis ε of D.host.E over D.host.F admits a seminorm ν satisfying IsContSeminorm ν with absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) for all φ, and for every ψ, χ and ω satisfying IsWeilDatumO ψ (dblSp A) B 1 χ ω and every f satisfying IsThetaFunO ψ (dblSp A) B f the function descend (GQ B) (fun h => thetaKO ω g h f) is integrable against autMeasure B m for every g and, when 2 * A.rank < B.rank, for all ν and 𝓖 satisfying IsCovolOne (ratL B A) ν 𝓖 both LeftInv (siegelQ A) (swSection A B ν 𝓖 ω f) holds and for every g both CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g holds and cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g equals the average of descend (GQ B) (fun h => thetaKO ω g h f) with respect to autMeasure B m.
- Premise 9. SiegelWeilUnitaryConvergent holds. For every D of type D7, every ψ of type AddChar (AF D.host.F) ℂ, and all A and B of type HSp D satisfying A.rank < B.rank, B.rank ≤ 2 * A.rank and A.rank + wittIdx B < B.rank, given χB and ω satisfying IsWeilDatumO ψ (dblSp A) B 1 χB ω, an element a of GL (Fin A.rank) (AE D) satisfying IsMaj A a and HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a), θ, sS and sB satisfying IsInfFam θ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ) and IsCartanInv (gramAt D B τ) (sB τ) for all τ and compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) for every k in Khat A a and every τ, μ and 𝓨 satisfying IsCovolOne (ratL B A) μ 𝓨, a Haar measure ν on GA D B, and f satisfying IsFockVec ψ θ (dblSp A) B sS sB f, the function AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ω g h f) is integrable against autMeasure B ν for every g and Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B) (thetaMean ω ν f) holds.
- Premise 10. A condition that the code calls DoublingMethodLocalZetaIntegrals holds, defined as ResidueKilled.DM.
- Premise 11. UnramifiedDoublingGL holds. For every nonarchimedean local field k of characteristic 0, every natural number n, every Haar measure μ on GL (Fin n) k with μ (KO k (Fin n)) = 1, every complex representation π of GL (Fin n) k on a complex vector space V with α of type Fin n → ℂˣ satisfying HasSatake π α, and every function ω from GL (Fin n) k to ℂ satisfying IsZonal π (KO k (Fin n)) ω, there exists a real number s₀ such that for every complex number s with s₀ < s.re the function taking g to sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g is integrable against μ and its integral against μ equals lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) n s.
- Premise 12. DiscreteSeriesClassification holds. For every natural number n there exist families of normed complex inner product spaces H ε lam and maps π ε lam from n by n complex matrices to bounded linear operators on H ε lam, indexed by ε of type Fin n → Bool and lam of type Fin n → ℝ, such that whenever lam is strictly decreasing and lam a - ((n as a real) - 1) / 2 is an integer for every a, the space H ε lam is complete and nontrivial with IsURepOn (UJset ε) (π ε lam), IsIrredOn (UJset ε) (π ε lam), IsSqIntOn ε (π ε lam) and HasInfChar ε (fun a => (lam a as a complex number)) (π ε lam), admits a unique complex submodule S satisfying IsKTypeOf ε (π ε lam) (lam + rhoN ε - rhoC ε) S, and satisfies μ equal to (lam + rhoN ε - rhoC ε) plus the sum over a and b of the real-cast scalar multiple of root a b by c a b for some natural-valued c with c a b ≠ 0 implying a < b whenever IsKTypeOf ε (π ε lam) μ S holds, and conversely for every ε of type Fin n → Bool and every complete nontrivial normed complex inner product space H' with map σ satisfying IsURepOn (UJset ε) σ, IsIrredOn (UJset ε) σ and IsSqIntOn ε σ there exist a permutation s of Fin n and mu of type Fin n → ℝ, with mu strictly decreasing, mu a - ((n as a real) - 1) / 2 an integer for every a, and s a < s b whenever a < b and ε (s a) = ε (s b), together with a complex linear isometric equivalence T between H' and H (ε ∘ s) mu satisfying T (σ (g.submatrix s.symm s.symm) v) = π (ε ∘ s) mu g (T v) for all g in UJset (ε ∘ s) and all v.
- Premise 13. StrongApproxSU holds. For all number fields F and E with E an F-algebra and every F-algebra homomorphism σ from E to E satisfying IsCMExt F E σ, every natural number M with 2 ≤ M, every M by M matrix J over E satisfying IsHermND σ J, every finite set S₁ of infinite places of F, every finite set S₂ of nonzero prime ideals of the ring of integers of F, and every ε of type AF F satisfying IsPlacesIdem S₁ S₂ ε such that SUSupp σ J ε is not compact, every g in SUAdelic σ J lies in the closure of the set of products γ * h in HA (AF F) σ J with γ in SURat σ J and h in SUSupp σ J ε.
- Premise 14. RowDiag holds for the predicate E D L C' given by IsScaleWithBoundedGamma D L C' together with RankMu D u for every word u.
- Premise 15. For every context K and every q in WPt p.s K the type RXs q.x.what₂ is nonempty.
- Conclusion. RowE (IsGoodE p.s) (BundleLinkage p) holds with the target predicate sending each bundle b to the statement MIstar2 for the record b.B.Q.Rl.toCx3 b.B.Q.F, the map b.B.Q.F.eV evaluated at the zs of that record, and the map b.B.Q.sEE.

This reading opens `D7`, `MIstar2`, `SData (field Cu)`, `ColumnsAtT (fields T and duStar)`, `Member`, `Ranks (field k)` and `Frame`.

It does not open `IsGoodE`, `ParEv`, `Pos, Of, Is`, `TrueE, HD, TwoTerm, mfL, kfk`, `MIDat, MIUnit2, MIid, AuNZ, toCx3, eV, zs`, `p.s`, `R.f, Scale, CGam`, `DoublingMethodLocalZetaIntegrals` and `Published bodies' inner names`.

The reader's confidence is low. The shape of the statement and many definitions are visible, but the conclusion depends on unopened conditions such as ParEv, Pos, Of, Is, positionOf, GoodE, MIDat, MIUnit2, MIid, AuNZ, TwoTerm, TrueE and HD, so its real content cannot be seen.

### Line 21, `miStar_row_alt_alt`

The head is `GlobalTheory.Fam.miStar_row_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Main Theorem Published Results Final. The line gathers 10,306 declarations and hangs from line 20, `miStarRowClosing_alt_alt`. Folded into the line is the wrapper `main_theorem_published_results_final_alt_alt`.

The theorem assumes thirteen named statements that the code files under published theorems, together with a quantitative statement that the code calls RowDiag, and a statement that the code calls RecTExists. Under these, for every parameter package p, if a certain structure RXs is inhabited at every point q of every context K, then one eventual row statement implies another. The assumed row statement says that every linked bundle b at a good point satisfies BundlePointConditions, and the concluded row statement says that every such bundle satisfies a condition that the code calls MIstar2.

- Premise 1. The proposition HarishChandraFinite holds.
- Premise 2. The proposition CuspRapidDecay holds.
- Premise 3. The proposition DiscreteSeriesCover holds.
- Premise 4. The proposition HarishChandraModules holds.
- Premise 5. The proposition CasselmanWallach holds.
- Premise 6. The proposition HoweUnram holds.
- Premise 7. The proposition WeilRepresentationUnitaryPair holds.
- Premise 8. The proposition WeilSiegelFormulaUnitary holds.
- Premise 9. The proposition SiegelWeilUnitaryConvergent holds.
- Premise 10. The proposition DoublingMethodLocalZetaIntegrals holds, which is an abbreviation for an opaque condition ResidueKilled.DM.
- Premise 11. The proposition UnramifiedDoublingGL holds.
- Premise 12. The proposition DiscreteSeriesClassification holds.
- Premise 13. The proposition StrongApproxSU holds.
- Premise 14. RowDiag holds for the condition E(D, L, C') that says IsScaleWithBoundedGamma D L C' holds and RankMu D u holds for every word u.
- Premise 15. hL is a proof of RecTExists, and p is any element of Parameters hL.
- Premise 16. For every context K and every point q of WPt p.s K, the type RXs (q.x.what₂) has at least one element.
- Premise 17. RowE holds for the slot IsGoodE p.s, the linkage BundleLinkage p, and the property that sends a bundle b to BundlePointConditions b.
- Conclusion. RowE holds for the same slot IsGoodE p.s and the same linkage BundleLinkage p, with the property that sends a bundle b to the condition MIstar2 of the object b.B.Q.Rl.toCx3 b.B.Q.F, applied to b.B.Q.F.eV at the field zs of that object and to b.B.Q.sEE.

```
HarishChandraFinite ⇒ CuspRapidDecay ⇒ DiscreteSeriesCover ⇒ HarishChandraModules ⇒ CasselmanWallach ⇒ HoweUnram ⇒ WeilRepresentationUnitaryPair ⇒ WeilSiegelFormulaUnitary ⇒ SiegelWeilUnitaryConvergent ⇒ DoublingMethodLocalZetaIntegrals ⇒ UnramifiedDoublingGL ⇒ DiscreteSeriesClassification ⇒ StrongApproxSU ⇒ RowDiag((D, L, C') ↦ IsScaleWithBoundedGamma(D, L, C') ∧ ∀u RankMu(D, u)) ⇒ ∀ hL ∈ RecTExists, ∀ p ∈ Parameters(hL), [∀ K ∈ Ctx, ∀ q ∈ WPt(p.s, K), RXs(q.x.what₂) ≠ ∅] ⇒ RowE(IsGoodE(p.s), BundleLinkage(p), b ↦ BundlePointConditions(b)) ⇒ RowE(IsGoodE(p.s), BundleLinkage(p), b ↦ MIstar2(C_b, eV_b(zs(C_b)), sEE_b)), where C_b = b.B.Q.Rl.toCx3(b.B.Q.F), eV_b = b.B.Q.F.eV, sEE_b = b.B.Q.sEE, and RowE(Q, Lk, E) = EvP((κ, K) ↦ ∀ β ∈ BPt(K), β.Is(Q) ⇒ ∀ c ∈ ℝ, ∀ b ∈ Bd(β.D, β.O, c), Lk(K, β, c, b) ⇒ E(κ, β.D, β.O, c, b))
```

The reading does not open the names `MIstar2`, `IsGoodE` and `DoublingMethodLocalZetaIntegrals`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the thirteen hypotheses stand for known results in the representation theory of unitary groups and theta correspondence (Harish-Chandra finiteness, Casselman and Wallach, Howe duality, the Weil representation, Siegel and Weil formulas, the doubling method, discrete series classification, strong approximation), and that MIstar2 is some multiplicity or isometry statement for a theta lift, but the text does not show this.

The reader's confidence is medium. The logical shape, RowE, EvP, Row and the thirteen hypotheses are visible, but the conclusion MIstar2, the projection p.s, ParEv and most fields of BundlePointConditions are opaque and 149 definitions were left out.

The check found no error in this reading.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 5 errors in this reading and, after they were corrected, 9 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 8 findings on it, and the text was changed in 8 places. A check of the changed text then found no error.

The theorem is a long implication with no free variables. It assumes twelve propositions that the project names after published results, together with HoweUnram and a scale-and-rank hypothesis built with RowDiag. Under these assumptions it says the following for every proof hL of RecTExists and every parameter record p over hL. If the record type RXs q.x.what₂ is nonempty for every context K and every point q in WPt p.s K, and if the ten-field bundle condition BundlePointConditions holds on the linked good points in the eventual sense that RowE expresses, then the condition MIstar2 holds on those same points in the same eventual sense. MIstar2 is applied to the complex data b.B.Q.Rl.toCx3 b.B.Q.F, the map b.B.Q.F.eV evaluated at the zs component of that data, and the map b.B.Q.sEE.

- Premise 1. The proposition HarishChandraFinite, which says that the complex span of forms θ V U ε fr ρ c is finite-dimensional over ℂ for every D7 record D, every family θ with IsInfFam θ, every V of type HSp D, every open subgroup U of GA D V, every pair ε and fr with IsFrameFam V ε fr, every family of finite-dimensional complex spaces W τ with representations ρ τ of Formalism.REAL.KG (ε τ) that satisfy IsContRep, and every c from D.what₂.Tau and ℕ to ℂ.
- Premise 2. The proposition CuspRapidDecay, which says that every φ satisfying IsAutFun, IsSmoothInf, IsUnifModerate and IsCuspFun, for θ with IsInfFam and e with IsExpFam, satisfies a condition that the code calls IsRapidDecay.
- Premise 3. The proposition DiscreteSeriesCover, which says that for all natural numbers p and q with 1 ≤ p + q and every T of type GrpData p q there is a family D of DSRep objects indexed by parameters, each with the types of its parameter, such that every DSRep object is UnitEquiv to some member of the family.
- Premise 4. The proposition HarishChandraModules, which is HarishChandraModulesOn T for all p, q with 1 ≤ p + q and all T, joined by 'and' to a condition that the code calls KFiniteAnalyticUJ.
- Premise 5. The proposition CasselmanWallach, which says that for every natural number n, every ε of type Fin n → Bool, every σ on a complete complex inner product space H with IsURepOn and IsIrredOn for UJset ε, every complete Hausdorff complex vector space E that is a uniform additive group, with seminorms p and maps π and dπ satisfying IsSmoothModRep ε p π dπ, and every linear map T₀ from H to E with IsGKMap ε σ π dπ T₀, there is a linear map T from H to E that agrees with T₀ on the vectors with IsKFin ε σ and satisfies IsSmoothGMap ε σ p π T, agrees on the vectors with SmoothVec (lieSet ε) σ with every other such map, sends the set of the vectors with SmoothVec (lieSet ε) σ to a closed set, and, when T₀ is nonzero on some vector with IsKFin ε σ, gives for every list S of lists of matrices that all lie in lieSet ε a continuous seminorm q on E with sobNorm σ S w ≤ q (T w) for every w with SmoothVec (lieSet ε) σ w.
- Premise 6. The proposition HoweUnram, which says that for every complete field L of characteristic 0 with a valuation in WithZero (Multiplicative ℤ) and all data satisfying LocPair, every nonzero s with LocVac ρ s whose orbit under ρ spans M satisfies two statements, namely that each w fixed by ω (g, 1) for all g in UJ σ JS whose image lies in GLint (intL L) lies in the span of the vectors ω (1, h) s, and the same with the two factors exchanged.
- Premise 7. The proposition WeilRepresentationUnitaryPair, which says that for every D7 record, every ψ with IsStdChar D ψ (−1), all S and T in HSp D and all χS and χT with IsHeckeChar and the ResEta conditions there exists ω satisfying IsWeilDatumO.
- Premise 8. The proposition WeilSiegelFormulaUnitary, which says that for every D7 record D, all A and B in HSp D and every Haar measure m on GA D B with 1 ≤ A.rank and either wittIdx B = 0 or A.rank + wittIdx B < B.rank, first, for every natural number d and every basis ε of D.host.E over D.host.F indexed by Fin d there is a seminorm ν with IsContSeminorm ν such that absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) for every φ in WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), and second, for all ψ, χ and ω with IsWeilDatumO ψ (dblSp A) B 1 χ ω and every f with IsThetaFunO ψ (dblSp A) B f, the function descend (GQ B) (fun h => thetaKO ω g h f) is integrable for autMeasure B m for every g, and when 2 · A.rank < B.rank, for all ν and 𝓖 with IsCovolOne (ratL B A) ν 𝓖, LeftInv (siegelQ A) (swSection A B ν 𝓖 ω f) holds and for every g both CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g holds and cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g equals the average over autMeasure B m of descend (GQ B) (fun h => thetaKO ω g h f).
- Premise 9. The proposition SiegelWeilUnitaryConvergent, which says that for every D7 record D, every ψ of type AddChar (AF D.host.F) ℂ, all A and B in HSp D with A.rank < B.rank ≤ 2 · A.rank and A.rank + wittIdx B < B.rank, all χB and ω with IsWeilDatumO ψ (dblSp A) B 1 χB ω, every a in GL (Fin A.rank) (AE D) with IsMaj A a and HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a), all θ, sS and sB with IsInfFam θ, with IsCartanInv (gramAt D (dblSp A) τ) (sS τ) and IsCartanInv (gramAt D B τ) (sB τ) for every τ, and with compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) for every k in Khat A a and every τ, all μ and 𝓨 with IsCovolOne (ratL B A) μ 𝓨, every Haar measure ν on GA D B and every f with IsFockVec ψ θ (dblSp A) B sS sB f, the function AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ω g h f) is integrable for autMeasure B ν for every g and Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B) (thetaMean ω ν f) holds, where no file shows a body of thetaKO, Eis.EisValueAt, flat, swSec, sZero or thetaMean.
- Premise 10. The proposition DoublingMethodLocalZetaIntegrals, which is by definition a condition that the code calls ResidueKilled.DM.
- Premise 11. The proposition UnramifiedDoublingGL, which says that for a nonarchimedean local field k of characteristic 0, a natural number n, a Haar measure μ on GL (Fin n) k with μ (KO k (Fin n)) = 1, a representation π of GL (Fin n) k on a complex vector space V and α of type Fin n → ℂˣ with HasSatake π α, and a function ω from GL (Fin n) k to ℂ with IsZonal π (KO k (Fin n)) ω, there is a real s₀ such that for every complex s with s₀ < Re s the function that sends g to sphSection k (Fin n) s (io k (Fin n) (g, 1)) · ω g is integrable for μ and its integral over μ equals lFactor (resCard k) α (s + 1/2) · lFactor (resCard k) α⁻¹ (s + 1/2) · invNormFactor (resCard k) n s.
- Premise 12. The proposition DiscreteSeriesClassification, which says that for every natural number n there is a family of complex inner product spaces H ε lam with maps π ε lam such that, first, for every ε of type Fin n → Bool and every strictly decreasing lam of type Fin n → ℝ with lam a − (n − 1)/2 an integer for every a, the space H ε lam is complete and nontrivial, π ε lam satisfies IsURepOn (UJset ε), IsIrredOn (UJset ε) and IsSqIntOn ε, HasInfChar ε holds of lam read as complex numbers and of π ε lam, exactly one submodule S satisfies IsKTypeOf ε (π ε lam) (lam + rhoN ε − rhoC ε) S, and every μ and S with IsKTypeOf ε (π ε lam) μ S have μ = (lam + rhoN ε − rhoC ε) + ∑ a, ∑ b, c a b • root a b for some natural numbers c a b that are zero unless a < b, and second, for every ε of type Fin n → Bool and every complete nontrivial complex inner product space H′ with a map σ satisfying IsURepOn (UJset ε), IsIrredOn (UJset ε) and IsSqIntOn ε there are a permutation s of Fin n with s a < s b whenever a < b and ε (s a) = ε (s b), a strictly decreasing mu with mu a − (n − 1)/2 an integer for every a, and a linear isometric equivalence T from H′ to H (ε ∘ s) mu with T (σ (g.submatrix s.symm s.symm) v) = π (ε ∘ s) mu g (T v) for every g in UJset (ε ∘ s) and every v.
- Premise 13. The proposition StrongApproxSU, which says that for number fields F and E with IsCMExt F E σ, M ≥ 2, a matrix J with IsHermND σ J and data with IsPlacesIdem for which SUSupp σ J ε is not compact, every g in SUAdelic σ J lies in the closure of the products γ·h with γ in SURat σ J and h in SUSupp σ J ε.
- Premise 14. The proposition RowDiag applied to the condition 'IsScaleWithBoundedGamma D L C′ and RankMu D u for every word u', which says that for all reals Cg, cb, Cu, cT, CT with 0 < cb and 0 < cT there exist C ≥ 1, C′₀ and Cl₀ such that for all C′ ≥ C′₀, Cl ≥ Cl₀, every D7 record D, every real L and every word u, the assumptions TrueE D, the stated condition and HD D L C′ Cl Cg cb Cu cT CT give TwoTerm D u (4(exp(C·mfL D L) + 1)) (4·exp(−kfk D / 2) + 2·exp(−kfk D)).
- Premise 15. For every proof hL of RecTExists and every p in Parameters hL, the hypothesis that RXs q.x.what₂ is nonempty for every context K and every point q in WPt p.s K.
- Premise 16. The hypothesis RowE (IsGoodE p.s) (BundleLinkage p) with predicate BundlePointConditions b.
- Conclusion. RowE (IsGoodE p.s) (BundleLinkage p) holds with the predicate that sends a bundle b to MIstar2 of the complex data b.B.Q.Rl.toCx3 b.B.Q.F with the maps b.B.Q.F.eV ((b.B.Q.Rl.toCx3 b.B.Q.F).zs) and b.B.Q.sEE, which means that ParEv holds of the statement that, when κ.Pos holds, there is a real x₀ such that for every context K with κ.Of K and x₀ ≤ K.s.x every good point β with a real number c and a linked bundle b satisfies MIstar2.

This reading opens `D7`, `D7.s (SData)`, `SData.Cu`, `D7.mem (Member)`, `ColumnsAtT.duStar`, `ColumnsAtT.T`, `Ranks.k`, `Ranks.m`, `MIstar2`, `GoodE`, `linkOf and BundleWitness inside BundleLinkage`, `IsRecT` and `BundleCondition`.

It does not open `TwoTerm`, `TrueE`, `HD`, `mfL`, `kfk`, `ParEv`, `BundleWitness` and `DoublingMethodLocalZetaIntegrals`.

The reader's confidence is low. The implication structure and many outer definitions are visible, but the eventual quantifier ParEv, the inner parts of MIstar2, TwoTerm, HD, TrueE and many names inside the published hypotheses have no body in the files.

### Line 22, `miStar2_of_allTrue_alt_alt`

The head is `GlobalTheory.Fam.miStar2_of_allTrue_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Main Theorem From Published Results Alt Alt Alt Alt. The line gathers 10,050 declarations and hangs from line 21, `miStar_row_alt_alt`. Folded into the line are the wrappers `main_theorem_from_published_results_alt_alt_alt_alt_alt`, `miAt_of_truePack_alt_alt` and `main_theorem_from_published_results_alt_alt_alt_alt`.

The theorem assumes thirteen named statements that the code files under published theorems. Under these, for every base B, every choice of X, I, l and Z, which make up the datum I.rec7 l Z, of L, hT, Gi, Gl, Yd and ex, which are typed over that datum, and of Kc and cX, which do not depend on it, and every package W of type RealPackAlt ex, three further conditions on W, B and the datum imply a condition that the code calls MIstar2 for the object W.Q.Rl.toCx3 W.Q.F.

- Premise 1. The proposition HarishChandraFinite holds.
- Premise 2. The proposition CuspRapidDecay holds.
- Premise 3. The proposition DiscreteSeriesCover holds.
- Premise 4. The proposition HarishChandraModules holds.
- Premise 5. The proposition CasselmanWallach holds.
- Premise 6. The proposition HoweUnram holds.
- Premise 7. The proposition WeilRepresentationUnitaryPair holds.
- Premise 8. The proposition WeilSiegelFormulaUnitary holds.
- Premise 9. The proposition SiegelWeilUnitaryConvergent holds.
- Premise 10. The proposition DoublingMethodLocalZetaIntegrals holds, which is an abbreviation for an opaque condition ResidueKilled.DM.
- Premise 11. The proposition UnramifiedDoublingGL holds.
- Premise 12. The proposition DiscreteSeriesClassification holds.
- Premise 13. The proposition StrongApproxSU holds.
- Premise 14. B, X, I, l, Z, L, hT, Gi, Gl, Kc, Yd, cX, ex are arbitrary data of the stated types and W is any element of RealPackAlt ex.
- Premise 15. AllFamilyConditions W holds.
- Premise 16. The number B.R.rS is at least 1.
- Premise 17. PuNZ holds for the datum I.rec7 l Z.
- Conclusion. The condition MIstar2 of the object packageCoefficientSpace W, which is W.Q.Rl.toCx3 W.Q.F, holds when applied to W.Q.F.eV at the field zs of that object and to W.Q.sEE.

```
HarishChandraFinite ⇒ CuspRapidDecay ⇒ DiscreteSeriesCover ⇒ HarishChandraModules ⇒ CasselmanWallach ⇒ HoweUnram ⇒ WeilRepresentationUnitaryPair ⇒ WeilSiegelFormulaUnitary ⇒ SiegelWeilUnitaryConvergent ⇒ DoublingMethodLocalZetaIntegrals ⇒ UnramifiedDoublingGL ⇒ DiscreteSeriesClassification ⇒ StrongApproxSU ⇒ ∀ B, X, I, l, Z, L, hT, Gi, Gl, Kc, Yd, cX, ex (with D = I.rec7(l, Z)), ∀ W ∈ RealPackAlt(ex), AllFamilyConditions(W) ⇒ 1 ≤ B.R.rS ⇒ PuNZ(D) ⇒ MIstar2(C_W, W.Q.F.eV(zs(C_W)), W.Q.sEE), where C_W = W.Q.Rl.toCx3(W.Q.F)
```

The reading does not open the names `MIstar2`, `I.rec7 l Z`, `TC` and `DoublingMethodLocalZetaIntegrals`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that this is the pointwise form of line 21, where a single real package that meets all family conditions yields the multiplicity or isometry statement MIstar2 from published results on theta lifts for unitary groups, but the text does not show this.

The reader's confidence is low. The quantifiers and the thirteen hypotheses are visible, but the conclusion MIstar2, all six fields of AllFamilyConditions and the function rec7 are opaque, and 167 definitions were left out.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

#### A deeper reading, with the record D7 at hand

A second reader saw the dossier, the whole text of `D7` and the glossary. The check found 3 errors in this reading and, after they were corrected, 9 more, which were corrected too. At that point the reading had not passed the check. A second model, Gemini, then made 13 findings on it, and the text was changed in 13 places. A check of the changed text then found one error, which the text below corrects. A check of the corrected text found no error.

Assume thirteen propositions that the project states as published results without proving them, namely HarishChandraFinite, CuspRapidDecay, DiscreteSeriesCover, HarishChandraModules, CasselmanWallach, HoweUnram, WeilRepresentationUnitaryPair, WeilSiegelFormulaUnitary, SiegelWeilUnitaryConvergent, DoublingMethodLocalZetaIntegrals, UnramifiedDoublingGL, DiscreteSeriesClassification and StrongApproxSU. Then the following holds for every base record B, every record X over it, every I of type TC B X, every l in I.Laws and every later-stage record Z, which together give the D7 bundle D = I.rec7 l Z, every L of type SizeData₂ D, hT of type GatTies D, Gi of type G.Inst D L, Gl of type G.LatInst D, Yd of type DivX D and ex of type Extra D L hT Gi Gl Kc Yd cX, every Kc of type G.Consts and cX of type ExtraC, which do not depend on D, and for every package W of type RealPackAlt ex. Suppose W satisfies all six parts of AllFamilyConditions, the number B.R.rS is at least 1, and for every word u some element φ of the space (D.mem u).A.Mram has a pair ⟨φ.1, φ.2.1⟩ in (D.mem u).A.Mu0 that the inverse of the linear isomorphism D.s_Cu u carries into D.s.Cu u and that the map D.s.Pu u then sends to a nonzero element. Then the coefficient space C = W.Q.Rl.toCx3 W.Q.F satisfies the condition that the code calls MIstar2, applied to the maps W.Q.F.eV C.zs and W.Q.sEE. By the glossary, that condition says for the implicit map fc of MIstar2 there is some d of type C.MIDat fc such that the three opaque conditions C.MIUnit2 d, C.MIid (W.Q.F.eV C.zs) W.Q.sEE d and C.AuNZ d all hold.

- Premise 1. The proposition that the code calls HarishChandraFinite, which says that for every D7 bundle D, every θ with IsInfFam θ, every V of type HSp D, every subgroup U of GA D V that is open, every ε and fr with IsFrameFam V ε fr, every family of finite-dimensional complex modules W τ with representations ρ τ that all satisfy IsContRep, and every c, the complex span of forms θ V U ε fr ρ c is finite-dimensional.
- Premise 2. The proposition that the code calls CuspRapidDecay, which says that for every D7 bundle D, every θ with IsInfFam θ, every V of type HSp D with e satisfying IsExpFam θ V e, every complex function φ on GA D V that satisfies the conditions the code calls IsAutFun, IsSmoothInf, IsUnifModerate and IsCuspFun also satisfies the condition the code calls CuspDecay.IsRapidDecay θ V φ.
- Premise 3. The proposition that the code calls DiscreteSeriesCover, which says that for all p and q with p + q at least 1 and every T of type GrpData p q there is a map D from parameters to DSRep T such that each D lam has types lam and every R in DSRep T satisfies the condition the code calls UnitEquiv R (D lam) for some lam.
- Premise 4. The proposition that the code calls HarishChandraModules, which says that HarishChandraModulesOn T holds for every such T and that KFiniteAnalyticUJ holds.
- Premise 5. The proposition that the code calls CasselmanWallach, which says that for every σ on a complex Hilbert space H with IsURepOn and IsIrredOn for UJset ε, and every complete Hausdorff space E with seminorms p and maps π and dπ satisfying IsSmoothModRep, every linear map T₀ with IsGKMap has a linear map T that agrees with T₀ on the vectors with IsKFin and satisfies IsSmoothGMap, that is unique on the vectors with SmoothVec among such maps, whose image of those vectors is closed, and for which each sobNorm is bounded by a continuous seminorm of T w when T₀ is nonzero on some IsKFin vector.
- Premise 6. The proposition that the code calls HoweUnram, which says that for every datum satisfying the condition the code calls LocPair and every nonzero s in M with the condition the code calls LocVac ρ s such that the vectors ρ x s, for x over the n' by n matrices, span M, every vector w fixed by ω (g, 1) for all g whose matrix lies in the set the code calls GLint lies in the span of the vectors ω (1, h) s, and the same holds with the two factors swapped.
- Premise 7. The proposition that the code calls WeilRepresentationUnitaryPair, which says that for every D7 bundle D, every ψ with IsStdChar D ψ (−1), all S and T of type HSp D and all χS and χT with IsHeckeChar D χS, IsHeckeChar D χT, ResEta D χS S.rank and ResEta D χT T.rank there is a homomorphism ω that satisfies IsWeilDatumO ψ S T χS χT ω.
- Premise 8. The proposition that the code calls WeilSiegelFormulaUnitary, which says that for every D of type D7, all A and B of type HSp D and every Haar measure m on GA D B with 1 ≤ A.rank and either wittIdx B = 0 or A.rank + wittIdx B < B.rank, two things hold. First, for every d and every basis ε of D.host.E over D.host.F indexed by Fin d there is a seminorm ν that satisfies the condition the code calls IsContSeminorm ν and has absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) for all φ. Second, for every ψ, χ and ω with IsWeilDatumO ψ (dblSp A) B 1 χ ω and every f with IsThetaFunO ψ (dblSp A) B f, the descended function built from thetaKO ω g h f is integrable with respect to autMeasure B m for every g, and, when 2·A.rank < B.rank, for all ν and 𝓖 with IsCovolOne (ratL B A) ν 𝓖 the section swSection A B ν 𝓖 ω f satisfies LeftInv (siegelQ A), satisfies CosetConv (siegel A) (GQ (dblSp A)) at every g, and has a cosetSum at g equal to the average over q of that descended function with respect to autMeasure B m.
- Premise 9. The proposition that the code calls SiegelWeilUnitaryConvergent, which says that for every D of type D7, every ψ and all A and B of type HSp D with A.rank < B.rank, B.rank ≤ 2·A.rank and A.rank + wittIdx B < B.rank, and under further hypotheses with the names IsWeilDatumO, IsMaj, HasIwasawa, IsInfFam, IsCartanInv for sS and for sB, a commutation rule for the elements of Khat A a, IsCovolOne, a Haar measure ν and IsFockVec, the descended function built from thetaKO ω g h f is integrable with respect to autMeasure B ν for every g and Eis.EisValueAt holds for A, flat A a (swSec A B ω μ 𝓨 f) (sZero A B), sZero A B and thetaMean ω ν f.
- Premise 10. The proposition that the code calls DoublingMethodLocalZetaIntegrals, which is by definition the opaque proposition ResidueKilled.DM.
- Premise 11. The proposition that the code calls UnramifiedDoublingGL, which says that for every non-archimedean local field k of characteristic 0, every Haar measure μ on GL n over k giving KO measure 1, every representation π of GL n over k with α satisfying the condition the code calls HasSatake π α, and every ω with the condition the code calls IsZonal π (KO k (Fin n)) ω there is a real s₀ such that for every complex s with real part above s₀ the function g ↦ sphSection k (Fin n) s (io k (Fin n) (g, 1)) · ω g is integrable with respect to μ and its integral equals lFactor (resCard k) α (s + 1/2) · lFactor (resCard k) α⁻¹ (s + 1/2) · invNormFactor (resCard k) n s.
- Premise 12. The proposition that the code calls DiscreteSeriesClassification, which says that for every n there is a family of spaces H ε lam with maps π ε lam that, for strictly decreasing lam with lam a − (n − 1)/2 an integer, are complete and nontrivial and satisfy IsURepOn, IsIrredOn, IsSqIntOn and HasInfChar, have exactly one submodule S with IsKTypeOf for the parameter lam + rhoN ε − rhoC ε, and have every other parameter μ with IsKTypeOf equal to that one plus a sum of root a b with natural coefficients that vanish unless a < b, and that every complete nontrivial σ with IsURepOn, IsIrredOn and IsSqIntOn is carried onto H (ε ∘ s) mu by a linear isometry T with T (σ (g.submatrix s.symm s.symm) v) = π (ε ∘ s) mu g (T v) for g in UJset (ε ∘ s), for some such mu and some permutation s with s a < s b whenever a < b and ε (s a) = ε (s b).
- Premise 13. The proposition that the code calls StrongApproxSU, which says that for all number fields F and E with σ satisfying IsCMExt F E σ, every M ≥ 2 and J with IsHermND σ J, and all S₁, S₂ and ε with IsPlacesIdem S₁ S₂ ε such that SUSupp σ J ε is not compact, every g in SUAdelic σ J lies in the closure of the set of products γ·h with γ in SURat σ J and h in SUSupp σ J ε.
- Premise 14. W satisfies AllFamilyConditions, which means it satisfies PackageHypotheses, ValidRealPackage, GeometricFamilyConditions, TwStdAlt and LevelCondition', and a recursion of type IndefiniteRealisationRecursion W.Q exists.
- Premise 15. 1 ≤ B.R.rS.
- Premise 16. PuNZ (I.rec7 l Z), which says that for every word u there is an element φ of (D.mem u).A.Mram whose pair ⟨φ.1, φ.2.1⟩ in (D.mem u).A.Mu0 is carried into D.s.Cu u by the inverse of the isomorphism D.s_Cu u and then sent by D.s.Pu u to a nonzero element.
- Conclusion. The coefficient space packageCoefficientSpace W satisfies the condition that the code calls MIstar2 with the maps W.Q.F.eV (its zs) and W.Q.sEE, which by the glossary means that, for the implicit map fc of MIstar2, some d of type MIDat fc of that coefficient space satisfies its conditions MIUnit2 d, MIid (W.Q.F.eV zs) W.Q.sEE d and AuNZ d.

This reading opens `D7`, `D.R (Ranks)`, `D.s (SData)`, `D.s.Pu`, `D.s_Cu`, `D.mem (Member)`, `ColumnsAtT`, `MIstar2` and `sEE`.

It does not open `TC`, `rec7`, `rS` and `MIDat, MIUnit2, MIid, AuNZ, zs`.

The reader's confidence is low. The quantifier structure and the premises are visible, but the conclusion MIstar2 reduces to MIDat, MIUnit2, MIid and AuNZ, which have no body, and rec7, TC, rS and many conditions inside the premises are also unopened.

### Line 23, `zero_free_all_of_green_v_win`

The head is `UpperTheory.Top.zero_free_all_of_green_v_win`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Top Plug. The line gathers 12,029 declarations and hangs from line 4, `every_character_of_theta_integrals_local_matching`. Folded into the line is the wrapper `every_character_of_green_v_win`.

The theorem takes three hypotheses, namely a statement Green about complex functions on Gn g d, a statement VWin that says VWinAt ψ 401 holds for every ψ of type PChar, and the existence of an element of a record type HypsAlt built with a closure condition on LinkN and with DefiniteSideCondition. From these it concludes ZeroFreeAll, which unfolds to the statement that every ψ of type PChar satisfies a condition that the code calls ZeroFreeAbove with the value 1/2.

- Premise 1. Green holds, which says that for every prime g, every label datum L and every d > 0 there is a map τ from polynomials over the integers mod g to complex functions on Gn g d, such that for each P with IsPrimeLab d P the function τ P satisfies IsCuspOf L P and takes the value ∏ over 1 ≤ i < d of (g^i − 1) at 1, such that τ is injective on such P, and such that every χ with IsCusp χ equals τ P for some such P.
- Premise 2. VWin holds, which says that VWinAt ψ 401 holds for every ψ of type PChar.
- Premise 3. The type HypsAlt N DR has at least one element, where N sends a family class 𝒞 to Closed 𝒞 (LinkN) and DR is DefiniteSideCondition.
- Conclusion. ZeroFreeAll holds, that is, every ψ of type PChar satisfies ψ.ZeroFreeAbove (1/2).

```
Green ∧ (∀ ψ ∈ PChar, VWinAt(ψ, 401)) ∧ HypsAlt(𝒞 ↦ Closed(𝒞, Fm ↦ LinkN(Fm)), DefiniteSideCondition) ≠ ∅ ⇒ ∀ ψ ∈ PChar, ZeroFreeAbove(ψ, 1/2), where Closed(𝒞, P) = ∃ ε1 > 0, ∀ eps with 0 < eps ≤ ε1, ∃ K ∈ TransportedAlt, ∀ Fm ∈ FamP(eps), ∀ CH ∈ ℝ, 𝒞(Fm) ⇒ Fm.Large(K, CH) ⇒ P(Fm, CH)
```

The reading does not open the names `PChar` and `ZeroFreeAbove`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that PChar is a type of primitive Dirichlet or Hecke characters and that ZeroFreeAbove (1/2) says the L-function of ψ has no zeros with real part greater than 1/2, so the conclusion would be a generalised Riemann hypothesis for all such characters, conditional on Green's classification of cuspidal characters of finite general linear groups, a window condition with constant 401 and a large package of hypotheses, but the text does not show this.

The reader's confidence is low. The outer shape is clear, but PChar, ZeroFreeAbove and VWinAt are not shown, and the bodies of HypsAlt, DefiniteSideCondition and FamP are cut.

The check found two errors in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- A says in its field says that Green is a statement about complex functions on groups Gn g d, but the dossier does not show the body of Gn and the Lean text only has maps Gn g d → ℂ evaluated at 1, so calling Gn g d a group asserts a meaning that the text does not show.
- A says that τ P takes its value at the identity, where the Lean text has only τ P 1 and the dossier does not show what 1 is in Gn g d.

### Line 24, `topCovolSlim2_use_alt_alt`

The head is `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Top Covol Slim2 Use. The line gathers 52,094 declarations and hangs from line 3, `every_character_of_literature_of_vWin`.

The theorem is a chain of fifteen implications. If fifteen named propositions all hold, each taken here as a hypothesis, then the proposition that the code calls CovolumeBoundOfX holds. CovolumeBoundOfX is shown to say that a condition the code calls Closed holds for an object called FamHyp and for the following property of a pair (Fm, CH), namely that there is a real number C0 with 0 ≤ C0 such that a condition called EventuallyAtAllPoints holds for Fm and for the property of p which says that for every real C with C0 ≤ C a condition called L3, attached to p.S false, holds of p.N C CH.

- Premise 1. ResolutionCharZero holds, which says that every reduced scheme X with a locally finite type, quasi-compact, separated map g to the spectrum of a field k of characteristic zero has a map s from some X' to X that satisfies a condition called IsBlowupSeq, makes the composite to Sp k smooth, is an isomorphism over the smooth locus of g, and makes the object that the code calls preRed, formed from s and the closed complement of the smooth locus, satisfy a condition called Snc.
- Premise 2. PrincipalisationCharZero holds, which says that for X smooth of relative dimension d, quasi-compact and separated over a field k of characteristic zero, an ideal sheaf I whose support contains no irreducible component of X, and a closed set E whose vanishing ideal satisfies SncAt at each point of E, there are X', a map s from X' to X and a closed set E' with IsSncBlowupSeq g E s E', with the composite to Sp k smooth, with the pullback of I satisfying EffCartier, with the vanishing ideal of its support satisfying Snc, and with s an isomorphism away from the support of I.
- Premise 3. PoincareLelongInv holds, which is an identity between quantities called ptsIntegral, stating that the integral of logNorm A s on P against the potentials log B.h and log (L j).h equals a finite sum over the horizontal members W of divSupp P s of the multiplicity multAt (P + (s)) W times the integral of log B.h on W against the potentials log (L j).h, minus the integral of log B.h on P against log A.h and the potentials log (L j).h, under smoothness and conjugation-invariance premises on the L j, A and B, with B.a = 0, IsArithVar P (n + 2) and IsSectionOn P A s.
- Premise 4. HSUse holds, which is the conjunction of three propositions that the code calls ArithKleiman.Statement, G7.Statement and ArithmeticVolumeNef.Statement.
- Premise 5. MoriwakiBigStatement holds, which says that under eight listed conditions on a coordinate tuple y, a Hermitian datum A, an ideal P0 and an intersection system II, the number II K ι (mCoordIdeal y) (D + 1) (constant family A) is at most a quantity called arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D.
- Premise 6. FarguesExact holds, which says that for a prime p, an algebraically closed valued field C of characteristic zero with ring of integers O that is p-adically complete and has v(p) < 1, a PDivGroup G over O, a compatible system ζ of p-power roots with ζ(0) = 1 and ζ(1) ≠ 1, and any O-bilinear form B that matches the map called pairing, an element x has hodgeTateLinear G x = 0 exactly when B x y = 0 for every y with dlogLinear G y = 0.
- Premise 7. ZarhinStatement holds, which says that every abelian scheme A with a relatively ample line bundle datum over the spectrum of the ring of integers R of a valued algebraically closed field admits an object P of type PolAV over the same base and maps i from A to P.A and r from P.A to A, both satisfying IsMonHom, with i followed by r equal to the identity of A.
- Premise 8. NefRR holds, which says that under IsArithVar (mCoordIdeal y) (D + 1), Birational y and NefOnGenericDeg (mCoordIdeal y) a, over a field Ω of characteristic zero, each rational span of chartLatNm y a τ is finite-dimensional and D! times its dimension divided by τ^D tends to genDeg (mCoordIdeal y) D a as τ tends to infinity.
- Premise 9. SiegelToroidalIntegral holds, which says that for every g ≥ 1 there is a function φ with IsPolFan id g φ such that for every odd n ≥ 3 there exist a family F, a scheme S projective and smooth of relative dimension g(g+1)/2 over Sp (cycAway n), an open immersion j of F.X into S, a semi-abelian group object G over S smooth of relative dimension g, and further data BD, d ≥ 1 and N ≥ 1 that satisfy thirteen listed conditions, the last of which is an ampleness condition IsAmpleLB for all k from some k₀ on.
- Premise 10. ToroidalForFanKS holds, which says that for a CM number field E with data H, Dw with 1 ≤ Dw.p + Dw.q, a function φ with IsPolFan and NoSelfInt, a level l, a moduli object Xo and a coefficient object c, there exist a Model Y, a datum BD and naturals d ≥ 1 and k ≥ 1 that satisfy six listed conditions, among them smoothness of relative dimension Dw.dim, Snc of a boundary ideal, HasChartOf at boundary points, a conditional ampleness, and HasLogKS.
- Premise 11. SemiAbelianLieSeminegative holds, which says that over a scheme C that is smooth of relative dimension 1, projective and geometrically connected over a field k of characteristic zero, for a semi-abelian group object G over C and a module W with IsVB W r and a monomorphism from W to Lie G, the number interNum k (structureModule C) [det W r] is at most 0.
- Premise 12. PointSeparationPair holds, which says that on an integral, locally Noetherian, normal scheme X projective over the complex numbers of dimension n, under listed conditions on a line bundle datum M, a function Δ, data m, G, r, N₀, two distinct closed points x₁ and x₂ and positive reals c(e) with the sum over e from 1 to n of 2^(1/e) · e / c(e) at most 1, there is a section s of M whose nonzero locus contains exactly one of x₁ and x₂.
- Premise 13. ArDegree holds, which is the conjunction of two propositions that the code calls ArBirational and ChernDegree.
- Premise 14. PublishedHodgeBundleTheorems holds, which is a bundle of 28 propositions with field names p1 to q18, each a named proposition in the namespace GlobalTheory.Published whose body the dossier does not show.
- Premise 15. GrothendieckDeformation holds, which says that for every commutative ring R, ideal I with divided powers κ satisfying IsNilDP, and surjective ring map π from R to R₀ with kernel I, a condition called GrothendieckMessing.At κ π holds.
- Conclusion. The proposition that the code calls CovolumeBoundOfX holds, which is the condition Closed applied to FamHyp and to the property that some C0 ≥ 0 exists for which EventuallyAtAllPoints Fm holds of the statement that L3 holds at p.N C CH for every C ≥ C0.

```
ResolutionCharZero ⇒ PrincipalisationCharZero ⇒ PoincareLelongInv ⇒ HSUse ⇒ MoriwakiBigStatement ⇒ FarguesExact ⇒ ZarhinStatement ⇒ NefRR ⇒ SiegelToroidalIntegral ⇒ ToroidalForFanKS ⇒ SemiAbelianLieSeminegative ⇒ PointSeparationPair ⇒ ArDegree ⇒ PublishedHodgeBundleTheorems ⇒ GrothendieckDeformation ⇒ CovolumeBoundOfX, where CovolumeBoundOfX = Closed(FamHyp, (Fm, CH) ↦ ∃ C0 ∈ ℝ, 0 ≤ C0 ∧ EventuallyAtAllPoints(Fm, p ↦ ∀ C, C0 ≤ C ⇒ L3(p.S(false), p.N(C, CH))))
```

The reading does not open the names `Closed`, `FamHyp`, `EventuallyAtAllPoints`, `L3`, `HSUse`, `ArDegree` and `PublishedHodgeBundleTheorems`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the premises are published results (resolution of singularities and principalisation in characteristic zero, a Poincaré–Lelong formula, arithmetic Hilbert–Samuel and Moriwaki bigness results, a Fargues exactness result on the Hodge–Tate sequence, Zarhin's trick, toroidal compactification results and Grothendieck–Messing deformation theory) and that the conclusion is a bound on a covolume, valid eventually at all points of a family, for all sufficiently large constants C. The name preRed suggests the reduced preimage under s of the closed complement of the smooth locus.

The reader's confidence is low. The shape of the implication and most premises are visible, but the conclusion rests on the unseen names Closed, FamHyp, EventuallyAtAllPoints and L3, three premises are conjunctions or bundles of unseen propositions, and 113 definitions were left out of the dossier.

The check found two errors in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- In the premise SiegelToroidalIntegral A says that the data satisfy "twelve listed conditions", whereas the Lean text lists thirteen conjuncts from "IsProjOver s" to "∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB ...", and no way of setting aside "1 ≤ d" and "1 ≤ N" gives twelve.
- In the premise ResolutionCharZero A says "a certain closed preimage (preRed) of the complement of the smooth locus", whereas the Lean text only has "FinalTheorems.Snc (preRed s (g.smoothLocus : Set X)ᶜ g.smoothLocus.isOpen.isClosed_compl)" and the dossier does not show the body of preRed, so calling it a preimage asserts a meaning outside the field suggests.

A second model, Gemini, checked this reading again. 3 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found no error.

### Line 25, `deep_slim_use`

The head is `PositivityTheory.HtPt.Ah.deep_slim_use`, in the module Development › Weil Bound › Core Statements › Automorphic Kernels › Moriwaki Bigness › Hilbert Samuel Applications › Ah Slim U. The line gathers 30,169 declarations and hangs from line 24, `topCovolSlim2_use_alt_alt`.

If eight named propositions hold, each taken as a hypothesis, then the proposition that the code calls DeepStR holds. DeepStR says that there is a single real number C with 0 ≤ C such that, for every datum D of type D7, every T of type CoreJ D that satisfies LawsJ, with D.R.m² ≤ D.R.k, every natural j with 1 ≤ j < D.R.m, every Y of type Deep (T.toCore) j, every natural e and real o with Y.Good e o, and with the number Y.d.l₂.M' having at most 15 distinct prime factors, the condition MeanAll Y.U (xiR D) (ell D) C holds. MeanAll with these arguments says that for every weight u and real g with WtGap u g, a condition called MeanGe holds for Y.U, xiR D, u, bndB u g and C · errX (ell D) u g.

- Premise 1. h₁, ResolutionCharZero holds, which asserts for reduced separated quasi-compact schemes locally of finite type over a field of characteristic zero a map s satisfying IsBlowupSeq with smooth source, an isomorphism over the smooth locus, and Snc holding of the object preRed formed from s and the complement of the smooth locus.
- Premise 2. h₂, PrincipalisationCharZero holds, which asserts a sequence satisfying IsSncBlowupSeq after which the pulled-back ideal sheaf satisfies EffCartier, the vanishing ideal of its support satisfies Snc, and the map is an isomorphism off the support. This summary leaves out the hypotheses SmoothOfRelativeDimension d g, QuasiCompact g and IsSeparated g, the two conditions on I and E, and the conjunct Smooth (s ≫ g).
- Premise 3. hPL, PoincareLelongInv holds, which is an identity expressing a ptsIntegral of logNorm A s as a multiplicity-weighted sum of ptsIntegral terms over horizontal members of divSupp P s minus another ptsIntegral term. This summary leaves out the nine hypotheses of the identity, from IsArithVar P (n + 2) to IsSectionOn P A s, and the potentials that each ptsIntegral takes as arguments.
- Premise 4. hU, HSUse holds, which is the conjunction of ArithKleiman.Statement, G7.Statement and ArithmeticVolumeNef.Statement.
- Premise 5. hBig, MoriwakiBigStatement holds, which bounds II K ι (mCoordIdeal y) (D + 1) (constant family A) above by arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D under eight listed conditions.
- Premise 6. hF, FarguesExact holds, which says that hodgeTateLinear G x = 0 exactly when B x y = 0 for all y with dlogLinear G y = 0, for a PDivGroup G over a p-adically complete ring of integers O of an algebraically closed valued field of characteristic zero and a form B matching the map called pairing. This summary leaves out the hypotheses that p is prime and v(p) < 1 and the sequence ζ with ζ 0 = 1, ζ (n + 1) ^ p = ζ n and ζ 1 ≠ 1.
- Premise 7. hZ, ZarhinStatement holds, which says that an abelian scheme with a relatively ample line bundle datum over the ring of integers of a valued algebraically closed field is a retract, through maps satisfying IsMonHom, of the group object of a PolAV.
- Premise 8. hN, NefRR holds, which says that D! times the rational dimension of the span of chartLatNm y a τ divided by τ^D tends to genDeg (mCoordIdeal y) D a as τ tends to infinity, under IsArithVar, Birational and NefOnGenericDeg. This summary leaves out the hypothesis that Ω has characteristic zero and the first part of the conclusion, that the span of chartLatNm y a τ has finite dimension over ℚ for every τ.
- Conclusion. DeepStR holds, that is, one constant C ≥ 0 exists for which MeanAll Y.U (xiR D) (ell D) C holds for all admissible D, T, j, Y, e and o with at most 15 distinct prime factors in Y.d.l₂.M'.

```
ResolutionCharZero ∧ PrincipalisationCharZero ∧ PoincareLelongInv ∧ HSUse ∧ MoriwakiBigStatement ∧ FarguesExact ∧ ZarhinStatement ∧ NefRR ⇒ DeepStR, where DeepStR = ∃ C ∈ ℝ, 0 ≤ C ∧ ∀ D ∈ D7, ∀ T ∈ CoreJ(D), LawsJ(T) ⇒ D.R.m² ≤ D.R.k ⇒ ∀ j ∈ ℕ, 1 ≤ j ⇒ j < D.R.m ⇒ ∀ Y ∈ Deep(T.toCore, j), ∀ e ∈ ℕ, ∀ o ∈ ℝ, Good(Y, e, o) ⇒ #{primes dividing Y.d.l₂.M'} ≤ 15 ⇒ MeanAll(Y.U, xiR(D), ell(D), C), and MeanAll(U, x, s, C) = ∀ u, ∀ g ∈ ℝ, WtGap(u, g) ⇒ MeanGe(U, x, u, bndB(u, g), C · errX(s, u, g))
```

The reading does not open the names `D7`, `D.R.m and D.R.k`, `CoreJ`, `LawsJ`, `Good`, `Y.d.l₂.M'`, `MeanGe, WtGap, bndB, errX` and `HSUse`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the conclusion is a uniform lower bound on a mean of heights over deep-level covers of a unitary-type moduli space, with error term scaled by C and by a logarithmic size ell of the host field, derived from published results on resolution, arithmetic Hilbert–Samuel theory, Moriwaki bigness, the Hodge–Tate sequence and Zarhin's trick. The name preRed suggests the reduced preimage under s of the closed complement of the smooth locus.

The reader's confidence is medium. The eight premises and the quantifier structure of DeepStR and MeanAll are visible, but MeanGe, WtGap, bndB, errX, Good, Core, LawsM and most of D7 are not shown, and 32 definitions were left out.

The check found one error in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- In the premise h₁ A says "an Snc preimage of its complement", whereas the Lean text has "FinalTheorems.Snc (preRed s (g.smoothLocus : Set X)ᶜ g.smoothLocus.isOpen.isClosed_compl)" and the dossier does not show the body of preRed, so calling it a preimage asserts a meaning outside the field suggests.

A second model, Gemini, checked this reading again. 5 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found no error.

### Line 26, `deepStR_of_use`

The head is `GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_use`, in the module Development › Weil Bound › Core Statements › Automorphic Kernels › Moriwaki Bigness › Hilbert Samuel Applications › Deep St R Of Use. The line gathers 29,778 declarations and hangs from line 25, `deep_slim_use`.

The theorem is a chain of ten implications. If ten named propositions hold, each taken as a hypothesis, then the proposition that the code calls DeepStR holds. DeepStR says that there is one real C ≥ 0 such that, for every D of type D7, every T of type CoreJ D satisfying LawsJ, with D.R.m² ≤ D.R.k, every natural j with 1 ≤ j < D.R.m, every Y of type Deep (T.toCore) j, and every natural e and real o with Y.Good e o, if Y.d.l₂.M' has at most 15 distinct prime factors then MeanAll Y.U (xiR D) (ell D) C holds.

- Premise 1. ArithIntersectionSystemStatement holds, which says that there exists an object II of type IntersectionSystem that satisfies a condition called IsFullIntersectionSystem.
- Premise 2. HSUse holds, which is the conjunction of ArithKleiman.Statement, G7.Statement and ArithmeticVolumeNef.Statement.
- Premise 3. MoriwakiBigStatement holds, which bounds II K ι (mCoordIdeal y) (D + 1) (constant family A) above by arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D under eight listed conditions.
- Premise 4. ResKStatement holds, which says that for a field K of characteristic zero, naturals M and D, a scheme X with a map i to PSpace K M and an open U with IsResInput M i U D, there exist a natural r, a scheme X', a closed immersion j of X' into the fibre product of PSpace K M and PSpace K r, and a map f from X' to X compatible with i and j, such that IsResWithCoords holds. This summary leaves out the equation f ≫ i = j ≫ pullback.fst that the word compatible stands for, and the arguments (i ≫ PSpace.str K M) U D f of IsResWithCoords.
- Premise 5. SemiAbelianHomExtension holds, which says that over a Noetherian normal scheme S with a dense open U, every map f satisfying IsMonHom between the restrictions to U of two semi-abelian group objects G and H is the restriction of exactly one map F from G to H satisfying IsMonHom.
- Premise 6. FarguesHodgeTate holds, which says two things for a PDivGroup G over a p-adically complete ring of integers O of an algebraically closed valued field C of characteristic zero with v(p) < 1, first that κ · w lies in the range of hodgeTateLinear G for every w in G.dual.omega and every κ in O with v(κ) ≤ v(4) when p = 2 and v(κ)^(p−1) ≤ v(p) otherwise, and second that hodgeTateLinear G x = 0 exactly when B x y = 0 for all y with dlogLinear G y = 0, for any form B matching the map called pairing. This summary leaves out the hypothesis that p is prime, the sequence ζ with ζ 0 = 1, ζ (n + 1) ^ p = ζ n and ζ 1 ≠ 1, and the two equations with muTate and with pure tensors that the word matching stands for.
- Premise 7. GagaSections holds, which says that on a scheme X proper and smooth over the complex numbers with a line bundle datum L, any family of complex functions h(i) on complex points that is holomorphic along every map satisfying IsHolTo and obeys the transition rule h(i)(x) = g(i,j)(x) · h(j)(x) comes from a section σ of L whose value at each point of U(i) is h(i). This summary leaves out the condition x ≫ s = 𝟙 on the maps x from Sp ℂ to X that the words complex points stand for, and the conditions IsOpen B, ⊤ ≤ y b ⁻¹ᵁ L.U i and ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j).
- Premise 8. QuotientByFiniteFlatStatement holds, which says that for an abelian scheme A over Spec R with a relatively ample line bundle datum and a map h from Spec B to A satisfying IsFinFlatSub, there exist an abelian scheme A' with a relatively ample line bundle datum and a map q from A to A' that satisfies IsMonHom and is finite, flat and surjective, such that a point z of A with values in any R-algebra S maps to the identity under q exactly when z factors through h.
- Premise 9. ZarhinStatement holds, which says that an abelian scheme with a relatively ample line bundle datum over the ring of integers of a valued algebraically closed field is a retract, through maps satisfying IsMonHom, of the group object of a PolAV.
- Premise 10. NefRR holds, which says that D! times the rational dimension of the span of chartLatNm y a τ divided by τ^D tends to genDeg (mCoordIdeal y) D a as τ tends to infinity, under IsArithVar, Birational and NefOnGenericDeg. This summary leaves out the hypothesis that Ω has characteristic zero and the first part of the conclusion, that the span of chartLatNm y a τ has finite dimension over ℚ for every τ.
- Conclusion. DeepStR holds, that is, one constant C ≥ 0 exists for which MeanAll Y.U (xiR D) (ell D) C holds for all admissible D, T, j, Y, e and o with at most 15 distinct prime factors in Y.d.l₂.M'.

```
ArithIntersectionSystemStatement ⇒ HSUse ⇒ MoriwakiBigStatement ⇒ ResKStatement ⇒ SemiAbelianHomExtension ⇒ FarguesHodgeTate ⇒ GagaSections ⇒ QuotientByFiniteFlatStatement ⇒ ZarhinStatement ⇒ NefRR ⇒ DeepStR, where DeepStR = ∃ C ∈ ℝ, 0 ≤ C ∧ ∀ D ∈ D7, ∀ T ∈ CoreJ(D), LawsJ(T) ⇒ D.R.m² ≤ D.R.k ⇒ ∀ j ∈ ℕ, 1 ≤ j ⇒ j < D.R.m ⇒ ∀ Y ∈ Deep(T.toCore, j), ∀ e ∈ ℕ, ∀ o ∈ ℝ, Good(Y, e, o) ⇒ #{primes dividing Y.d.l₂.M'} ≤ 15 ⇒ MeanAll(Y.U, xiR(D), ell(D), C), and MeanAll(U, x, s, C) = ∀ u, ∀ g ∈ ℝ, WtGap(u, g) ⇒ MeanGe(U, x, u, bndB(u, g), C · errX(s, u, g))
```

The reading does not open the names `MeanGe, WtGap, bndB, errX, Good`, `D7`, `CoreJ and LawsJ`, `ArithIntersectionSystemStatement` and `HSUse`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that this is the same uniform mean-height bound as in line 25, here derived from a different list of published inputs (an arithmetic intersection theory, arithmetic Hilbert–Samuel results, Moriwaki bigness, a resolution statement with coordinates, extension of homomorphisms of semi-abelian schemes, Fargues's Hodge–Tate results, GAGA for sections, quotients of abelian schemes by finite flat subgroups, Zarhin's trick and a Riemann–Roch limit for nef classes).

The reader's confidence is medium. All ten premises and the quantifier structure of DeepStR and MeanAll are visible, but MeanGe, WtGap, bndB, errX, Good, IsFullIntersectionSystem, the three parts of HSUse and most of D7 are not shown, and 32 definitions were left out.

The check found no error in this reading.

A second model, Gemini, checked this reading again. 4 passages of the text above were changed after its findings were compared with the Lean text. A further check of the changed text found no error.

### Line 27, `goodTower_volume_of_reduced`

The head is `GlobalTheory.CompanionTheory.Ar.Top.goodTower_volume_of_reduced`, in the module Development › Automorphic Spectrum › Proofs › Geometry Proofs › Final Theorem Of Inputs Right. The line gathers 20,438 declarations and hangs from line 26, `deepStR_of_use`. Folded into the line are the wrappers `good_tower_volume_theorem_bis` and `final_theorem_of_inputs_right`.

The theorem is a pure implication between named propositions. If seventeen listed hypotheses all hold, then two conditions that the code calls GoodTowerExistsX and VolumeTheoremX both hold. GoodTowerExistsX says that for every CM number field E with the listed data, satisfying conditions called IsGlobal and SplitComps and with 1 ≤ p and 1 ≤ q, there exist a RootTower T and a GoodOrigin o with the property o.Extra. VolumeTheoremX says that one real constant C ≥ 0 exists, chosen before all other data, such that six opaque properties of T hold under the listed numerical conditions.

- Premise 1. The conjunction of PartI, N1ab, N1c and, for every CM number field E with a Host H and a Datum D, both ToroidalLevelCompatibility and ToroidalHeckeCompatibility for D.
- Premise 2. The proposition KeyFormula.
- Premise 3. The proposition SemiAbelianHomExtension.
- Premise 4. The proposition NumericalSegre.Statement.
- Premise 5. The proposition ResKStatement.
- Premise 6. The proposition FarguesHodgeTate.
- Premise 7. The proposition GagaSections.
- Premise 8. The proposition LineOfLargeDegree.Statement.
- Premise 9. The proposition PB.Inputs, a conjunction of seventeen named statements.
- Premise 10. The proposition Prov.HS, a conjunction of nine named statements.
- Premise 11. The proposition Prov.An, a conjunction of seven named statements.
- Premise 12. The proposition Prov.ZhangDimensionPushDownGrassmannianHeightBounds, a conjunction of four named statements and the trivially true proposition True.
- Premise 13. The proposition PtsIntegrableStatement.
- Premise 14. The proposition AvoidStatement.
- Premise 15. The proposition QuotientByFiniteFlatStatement.
- Premise 16. The proposition ZarhinStatement.
- Premise 17. The proposition ThetaUnifAV.
- Conclusion. Both GoodTowerExistsX and VolumeTheoremX hold.

```
(PartI ∧ N1ab ∧ N1c ∧ ∀ E,H,D (ToroidalLevelCompatibility_D ∧ ToroidalHeckeCompatibility_D)) ⇒ KeyFormula ⇒ SemiAbelianHomExtension ⇒ NumericalSegre ⇒ ResK ⇒ FarguesHodgeTate ⇒ GagaSections ⇒ LineOfLargeDegree ⇒ PB.Inputs ⇒ Prov.HS ⇒ Prov.An ⇒ Prov.Zhang… ⇒ PtsIntegrable ⇒ Avoid ⇒ QuotientByFiniteFlat ⇒ Zarhin ⇒ ThetaUnifAV ⇒ (GoodTowerExistsX ∧ VolumeTheoremX), where GoodTowerExistsX ≡ ∀ E CM number field, ∀ H,D,Xo,l,c,Y [IsGlobal(Xo,l,c,Y) ⇒ SplitComps(Y) ⇒ 1 ≤ p ⇒ 1 ≤ q ⇒ ∃ T ∈ RootTower(CMType H, p+q) ∃ o ∈ GoodOrigin(Y,T), o.Extra], and VolumeTheoremX ≡ ∃ C ∈ ℝ, 0 ≤ C ∧ ∀ E CM number field with IsAbelianGalois(ℚ,E), ∀ H,D,Xo,l,c,Y,T,o,II [IsGlobal(Xo,l,c,Y) ⇒ o.Extra ⇒ IsFullIntersectionSystem(II) ⇒ 1 ≤ q ⇒ 3q+1 ≤ p+q ⇒ |T.bad| ≤ 4·|CMType H|·(p+q)² ⇒ T.Proportional ∧ T.VolEq ∧ T.T1(II) ∧ T.ThmB(II, hhFl(CMType H, p+q, II)) ∧ T.T2(II, C, hostRd E, hostLval H) ∧ T.MeanSlope(II, C, hostRd E, hostLval H)], with p = D.p and q = D.q
```

The reading does not open the names `Level, Moduli, Coeff, Model, CMType, RootTower, GoodOrigin, IsGlobal, SplitComps, Extra` and `Proportional, VolEq, T1, ThmB, T2, MeanSlope, hhFl, hostRd, hostLval, IntersectionSystem, IsFullIntersectionSystem`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the conclusion is the existence of a good tower of models over unitary Shimura varieties of signature (p, q) and a volume or mean slope estimate for it with a uniform constant, and that the premises are published theorems of arithmetic geometry (GAGA, Fargues on Hodge–Tate maps, Zarhin's trick, Zhang's height bounds, arithmetic Hilbert–Samuel) taken as inputs, but the dossier does not confirm these readings.

The reader's confidence is medium. The logical shape and most hypotheses are shown with bodies, and a folded wrapper called final_theorem_of_inputs_right has the identical statement, but the two conclusions rest on about twenty names whose bodies are not shown and 96 definitions were left out.

The check found no error in this reading.

### Line 28, `good_tower_volume_theorem`

The head is `GlobalTheory.T.good_tower_volume_theorem`, in the module Development › Automorphic Spectrum › Proofs › Divisibility Proofs › Good Tower Volume Theorem Statement. The line gathers 17,143 declarations and hangs from line 27, `goodTower_volume_of_reduced`.

The theorem is a pure implication between named propositions. If the six propositions called Top.Given, PtsIntegrableStatement, AvoidStatement, Out.WeilSt, Num.FamilyExistsPos and Cmp.CmpPair all hold, then the two conditions that the code calls GoodTowerExistsX and VolumeTheoremX both hold. The two conclusions are the same as in line 27, namely the existence of a RootTower T and a GoodOrigin o with o.Extra, and one constant C ≥ 0 for which six opaque properties of T hold under listed numerical conditions.

- Premise 1. The proposition Top.Given, a conjunction of fourteen parts.
- Premise 2. The proposition PtsIntegrableStatement.
- Premise 3. The proposition AvoidStatement.
- Premise 4. The proposition Out.WeilSt.
- Premise 5. The proposition Num.FamilyExistsPos.
- Premise 6. The proposition Cmp.CmpPair.
- Conclusion. Both GoodTowerExistsX and VolumeTheoremX hold.

```
Given ⇒ PtsIntegrable ⇒ Avoid ⇒ WeilSt ⇒ FamilyExistsPos ⇒ CmpPair ⇒ (GoodTowerExistsX ∧ VolumeTheoremX), where Given ≡ (PartI ∧ N1ab ∧ N1c ∧ ∀ E,H,D (ToroidalLevelCompatibility_D ∧ ToroidalHeckeCompatibility_D)) ∧ KeyFormula ∧ SemiAbelianHomExtension ∧ NumericalSegre ∧ ResK ∧ SAStatement ∧ FarguesHodgeTate ∧ GagaSections ∧ SlopeBoundSt ∧ PB.Inputs ∧ Prov.HS ∧ Prov.An ∧ Prov.Zhang… ∧ AntisymPerturbation, and GoodTowerExistsX ≡ ∀ E CM number field, ∀ H,D,Xo,l,c,Y [IsGlobal(Xo,l,c,Y) ⇒ SplitComps(Y) ⇒ 1 ≤ p ⇒ 1 ≤ q ⇒ ∃ T ∈ RootTower(CMType H, p+q) ∃ o ∈ GoodOrigin(Y,T), o.Extra], and VolumeTheoremX ≡ ∃ C ∈ ℝ, 0 ≤ C ∧ ∀ E CM number field with IsAbelianGalois(ℚ,E), ∀ H,D,Xo,l,c,Y,T,o,II [IsGlobal(Xo,l,c,Y) ⇒ o.Extra ⇒ IsFullIntersectionSystem(II) ⇒ 1 ≤ q ⇒ 3q+1 ≤ p+q ⇒ |T.bad| ≤ 4·|CMType H|·(p+q)² ⇒ T.Proportional ∧ T.VolEq ∧ T.T1(II) ∧ T.ThmB(II, hhFl(CMType H, p+q, II)) ∧ T.T2(II, C, hostRd E, hostLval H) ∧ T.MeanSlope(II, C, hostRd E, hostLval H)], with p = D.p and q = D.q
```

The reading does not open the names `PartI, N1ab, N1c, ToroidalLevelCompatibility, ToroidalHeckeCompatibility, KeyFormula, NumericalSegre.Statement, ResKStatement, SAStatement` and `GoodOrigin, Extra, IsGlobal, SplitComps, Proportional, VolEq, T1, ThmB, T2, MeanSlope, hhFl, hostRd, hostLval`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest a theorem that produces a good tower over unitary Shimura varieties of signature (p, q) and a volume or mean slope estimate with a uniform constant from a bundle of quoted results, a Weil pairing statement, a family existence statement and a comparison of intersection numbers between two models, but the dossier does not confirm these readings.

The reader's confidence is medium. The implication and the quantifier structure of both conclusions are visible, but nine parts of Given and thirteen names inside the conclusions have no body in this dossier and 29 definitions were left out.

The check found no error in this reading.

### Line 29, `topCovolG_alt_alt`

The head is `SelfIntersectionVolumeEstimates.topCovolG_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Top Covol G. The line gathers 12,517 declarations and hangs from line 24, `topCovolSlim2_use_alt_alt`.

The theorem is a pure implication between named propositions. If the seven propositions called VolumeEstimateHypotheses, HypothesesX, PublishedHodgeBundleTheorems, HypothesesH, GrothendieckDeformation, HSCore.Quoted and DeepStR all hold, then a condition that the code calls CovolumeBoundOfX holds. Unfolded as far as the dossier allows, the conclusion says that there is ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is an object K such that every family Fm of type FamP eps and every real CH satisfying FamHyp Fm and Fm.Large K CH admit a real C0 ≥ 0 for which a condition L3 holds, for all C ≥ C0, in the sense called EventuallyAtAllPoints.

- Premise 1. The proposition VolumeEstimateHypotheses, which is SelfIntersectionBound together with SmallSectionsInject.
- Premise 2. The proposition HypothesesX, a bundle of five named statements.
- Premise 3. The proposition PublishedHodgeBundleTheorems, a bundle of twenty-eight named statements.
- Premise 4. The proposition HypothesesH, a bundle of four named statements.
- Premise 5. The proposition GrothendieckDeformation.
- Premise 6. The proposition HSCore.Quoted, a bundle of eight named statements.
- Premise 7. The proposition DeepStR.
- Conclusion. The condition CovolumeBoundOfX holds.

```
VolumeEstimateHypotheses ⇒ HypothesesX ⇒ PublishedHodgeBundleTheorems ⇒ HypothesesH ⇒ GrothendieckDeformation ⇒ Quoted ⇒ DeepStR ⇒ CovolumeBoundOfX, where CovolumeBoundOfX ≡ ∃ ε1 > 0 ∀ eps (0 < eps ≤ ε1 ⇒ ∃ K ∈ TransportedAlt ∀ Fm ∈ FamP(eps) ∀ CH ∈ ℝ [FamHyp(Fm) ⇒ Fm.Large(K, CH) ⇒ ∃ C0 ≥ 0, EventuallyAtAllPoints(Fm, p ↦ ∀ C ≥ C0, (p.S false).L3(p.N C CH))]), and DeepStR ≡ ∃ C ≥ 0 ∀ D ∈ D7 ∀ T ∈ CoreJ(D) [LawsJ(T) ⇒ m² ≤ k ⇒ ∀ j (1 ≤ j < m ⇒ ∀ Y ∈ Deep(T.toCore, j) ∀ e ∈ ℕ ∀ o ∈ ℝ (Y.Good(e, o) ⇒ #primeFactors(Y.d.l₂.M') ≤ 15 ⇒ MeanAll(Y.U, xiR D, ell D, C)))], with m = D.R.m and k = D.R.k
```

The reading does not open the names `FamHyp, FamP, TransportedAlt, Large, EventuallyAtAllPoints, L3, S, N` and `D7`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the conclusion is an upper or lower bound on a covolume of a lattice of sections that holds eventually along a family, derived from quoted theorems of algebraic and arithmetic geometry and from a mean slope estimate with a uniform constant, but the dossier does not confirm these readings.

The reader's confidence is low. The implication, the body of Closed and the body of DeepStR are visible, but the conclusion rests on eight names with no body, most premises are bundles of names with no body, three records are cut off and 47 definitions were left out.

The check found no error in this reading.

### Line 30, `automorphic_window_of_inputs`

The head is `UpperTheory.One.Join.automorphic_window_of_inputs`, in the module Development › Automorphic Arithmetic › Automorphic Varieties › Modularity Argument › Threshold Arguments › Dense Threshold Cases › Top Main Zj. The line gathers 55,754 declarations and hangs from line 2, `everyCharacter_of_row`. Folded into the line is the wrapper `vwin_of_row`.

Assume three things, namely a condition bundle that the code calls OpenImageCondition, a statement called BaseChangeIsobaricN, and a statement called RowT. Then the statement VWin holds, which says that for every primitive complex Dirichlet character ψ the window statement VWinAt ψ 401 holds. VWinAt ψ 401 says that for every real eps with 0 < eps < 1/52 and every function e from the reals to the natural numbers with PageN eps x (e x) for all x ≥ 1, there are a real J ≥ 1 and a real X0 such that for every X ≥ X0 and every pair of natural numbers q, d with WinPair eps (X^(1/J)) q d, some real Y with X^(1/J) ≤ Y and Y² ≤ X has VAt ψ eps 401 q d (e x) x for every x between Y and Y².

- Premise 1. OpenImageCondition holds, which the dossier shows to be a bundle with one field, and that field is exactly the statement RowT.
- Premise 2. BaseChangeIsobaricN holds, which says that for every CM number field E in which every finite prime is unramified over the ring of integers of the maximal real subfield, every n ≥ 1 and every space π of complex functions on the group UA E n satisfying IsAutRepU, there exist a number c, sizes N_1,…,N_c adding up to n, and further data V, σ, m, P satisfying a condition that the code calls IsBaseChangeN.
- Premise 3. RowT holds, which is Row0b applied to the notion IsRecT, and which says that for every CM number field E with algebraic closure Ω, every prime l, every ring isomorphism ι from Qbar l to ℂ, every a ≥ 1, every π of type CuspSub E a and every χ of type HChar on the maximal real subfield, if CG.mk π satisfies IsRegAlg and PolarizedPair π χ holds then there exist a group homomorphism r from G E Ω to GL_a(Qbar l), an integer wt and a function HT satisfying a condition that the code calls PropsB.
- Conclusion. VWin holds, that is, VWinAt ψ 401 holds for every primitive Dirichlet character ψ.

```
OpenImageCondition ∧ BaseChangeIsobaricN ∧ RowT ⇒ VWin, where VWin ⇔ ∀ ψ ∈ PChar, ∀ eps ∈ ℝ, 0 < eps < 1/52 ⇒ ∀ e ∈ (ℝ → ℕ), (∀ x ≥ 1, PageN(eps, x, e(x))) ⇒ ∃ J ≥ 1, ∃ X0 ∈ ℝ, ∀ X ≥ X0, ∀ q, d ∈ ℕ, WinPair(eps, X^(1/J), q, d) ⇒ ∃ Y ∈ ℝ, X^(1/J) ≤ Y ∧ Y² ≤ X ∧ ∀ x ∈ ℝ, Y ≤ x ≤ Y² ⇒ VAt(ψ, eps, 401, q, d, e(x), x)
```

The reading does not open the names `PageN`, `WinPair`, `VAt`, `PropsB`, `IsBaseChangeN` and `UA`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that existence of Galois representations attached to polarized cuspidal automorphic representations over CM fields, together with base change from unitary groups, yields a bound for sums twisted by a Dirichlet character in a window of ranges.

The reader's confidence is medium. The logical shape and all constants (401, 1/52, the exponents 1/J and 2) are visible, but PageN, WinPair, VAt and PropsB are shown without bodies, so the mathematical content of the conclusion and of RowT cannot be read off.

The check found no error in this reading.

A second model, Gemini, checked this reading again. One passage of the text above was changed after its findings were compared with the Lean text. A further check of the changed text found no error.

### Line 31, `v_window_of_automorphy_csd_ss_mono_odd`

The head is `UpperTheory.V.HV.DescentVanishingReductions.v_window_of_automorphy_csd_ss_mono_odd`, in the module Development › Automorphic Arithmetic › Automorphic Varieties › Modularity Argument › Threshold Arguments › Dense Threshold Cases › Window Bound Of Literature Level. The line gathers 55,113 declarations and hangs from line 30, `automorphic_window_of_inputs`. Folded into the line are the wrappers `v_window_of_depth_zero_residual_bc_cm` and `v_window_of_literal_automorphy_n`.

Assume a bundle of statements that the code calls LiteratureRankNHypothesis. Then VWin holds, which says that for every primitive complex Dirichlet character ψ the window statement VWinAt ψ 401 holds. The window statement has the same form as in line 30, with the bounds 0 < eps < 1/52, a real J ≥ 1, a threshold X0, and a real Y with X^(1/J) ≤ Y and Y² ≤ X.

- Premise 1. LiteratureRankNHypothesis holds, which is a bundle of four parts named loc (of type LitLocAlt), aut (of type LiteratureAutomorphyHypothesis), coh (of type LitCoh) and cm (of type LiteratureCMHypothesis).
- Conclusion. VWin holds, that is, VWinAt ψ 401 holds for every primitive Dirichlet character ψ.

```
LiteratureRankNHypothesis ⇒ VWin, where LiteratureRankNHypothesis ⇔ LitLocAlt ∧ LiteratureAutomorphyHypothesis ∧ LitCoh ∧ LiteratureCMHypothesis, and VWin ⇔ ∀ ψ ∈ PChar, ∀ eps ∈ ℝ, 0 < eps < 1/52 ⇒ ∀ e ∈ (ℝ → ℕ), (∀ x ≥ 1, PageN(eps, x, e(x))) ⇒ ∃ J ≥ 1, ∃ X0 ∈ ℝ, ∀ X ≥ X0, ∀ q, d ∈ ℕ, WinPair(eps, X^(1/J), q, d) ⇒ ∃ Y ∈ ℝ, X^(1/J) ≤ Y ∧ Y² ≤ X ∧ ∀ x ∈ ℝ, Y ≤ x ≤ Y² ⇒ VAt(ψ, eps, 401, q, d, e(x), x)
```

The reading does not open the names `LitLocAlt`, `LiteratureAutomorphyHypothesis`, `LitCoh`, `LiteratureCMHypothesis`, `PageN, WinPair, VAt` and `GlobalTheory.coh`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the premise collects published theorems from the literature (local representation theory of GL_n, automorphic forms and base change, Galois cohomology, and complex multiplication) and that the theorem derives the character window bound from them. The dossier also shows two folded wrappers, one identical in statement and one deriving VWin from OpenImageCondition, BaseChangeIsobaricN, RowT and LiteratureCMHypothesis.

The reader's confidence is low. The premise is a bundle of fifty-six named propositions almost none of whose bodies are shown, and the conclusion ends in the opaque conditions PageN, WinPair and VAt, so only the outer logical shape is visible.

The check found no error in this reading.

### Line 32, `vwin_of_hypotheses_H_E_alt`

The head is `UpperTheory.V.HV.DescentVanishingReductions.vwin_of_hypotheses_H_E_alt`, in the module Development › Automorphic Arithmetic › Automorphic Varieties › Modularity Argument › Threshold Arguments › Dense Threshold Cases › Window Bound Of Literature Level. The line gathers 47,836 declarations and hangs from line 31, `v_window_of_automorphy_csd_ss_mono_odd`.

Assume a bundle of statements that the code calls HypothesesH'. Then VWin holds, which says that for every primitive complex Dirichlet character ψ the window statement VWinAt ψ 401 holds, in the same form as in lines 30 and 31. The bundle consists of an earlier bundle Hypotheses' with ten parts, plus five further statements named descU, cyc, cyc2, quat and ssR.

- Premise 1. HypothesesH' holds, which consists of Hypotheses' (parts litN, cohC, conjC, borelC, galR, smoR, gkR, admR, bc, newform) together with DescWeak, CycC, Desc2, DefQuatExists and CuspSemisimpleReal.
- Conclusion. VWin holds, that is, VWinAt ψ 401 holds for every primitive Dirichlet character ψ.

```
HypothesesH' ⇒ VWin, where HypothesesH' ⇔ Hypotheses' ∧ DescWeak ∧ CycC ∧ Desc2 ∧ DefQuatExists ∧ CuspSemisimpleReal, Desc2 ⇔ DescS ∨ Down2, and VWin ⇔ ∀ ψ ∈ PChar, ∀ eps ∈ ℝ, 0 < eps < 1/52 ⇒ ∀ e ∈ (ℝ → ℕ), (∀ x ≥ 1, PageN(eps, x, e(x))) ⇒ ∃ J ≥ 1, ∃ X0 ∈ ℝ, ∀ X ≥ X0, ∀ q, d ∈ ℕ, WinPair(eps, X^(1/J), q, d) ⇒ ∃ Y ∈ ℝ, X^(1/J) ≤ Y ∧ Y² ≤ X ∧ ∀ x ∈ ℝ, Y ≤ x ≤ Y² ⇒ VAt(ψ, eps, 401, q, d, e(x), x)
```

The reading does not open the names `Hypotheses'`, `Desc2` and `PageN, WinPair, VAt`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the premise gathers classical and published theorems (the literature bundle of line 31, results attributed to Clozel and Borel, Galois representations for GL2 over totally real fields, strong multiplicity one, cyclic base change, descent to unitary groups, existence of definite quaternion algebras, and semisimplicity of cusp forms) and that the window bound follows from them.

The reader's confidence is low. Five of the added premises have visible bodies, but the ten parts of Hypotheses' and the conditions PageN, WinPair and VAt in the conclusion are opaque, as are most of the names inside the visible bodies.

The check found no error in this reading.

### Line 33, `galoisLocalGlobalStrong_recParameter`

The head is `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`, in the module Development › Automorphic Arithmetic › Foundations › Galois Representations › Integral Structures › Row Src. The line gathers 51,784 declarations and hangs from line 1, `everyCharacter`.

With no premises, the statement Row0b holds for the notion recT, which is the notion IsRecT. In words, for every CM number field E with an algebraic closure Ω, every prime l, every ring isomorphism ι from an algebraic closure of the l-adic numbers to ℂ, every a ≥ 1, every π of type CuspSub E a and every χ of type HChar on the maximal real subfield of E, if the class of π satisfies IsRegAlg and the pair satisfies PolarizedPair π χ, then there exist a group homomorphism r from the automorphism group of Ω over E to GL_a over the l-adic algebraic closure, an integer wt, and a function HT assigning a multiset of integers to each field embedding of E into the l-adic algebraic closure, such that PropsB recT π ι r wt HT holds. PropsB asserts that r is continuous, that r satisfies IsSSRep, a condition AwayB at each finite prime not containing l, two explicit identities for HT, and a condition AboveB.

- Conclusion. Row0b recT holds, that is, every π over a CM field with IsRegAlg and PolarizedPair has some r, wt and HT with PropsB recT π ι r wt HT.

```
∀ E CM number field, ∀ Ω algebraic closure of E, ∀ l prime, ∀ ι ∈ (Qbar_l ≅ ℂ as rings), ∀ a ≥ 1, ∀ π ∈ CuspSub(E, a), ∀ χ ∈ HChar(E⁺), IsRegAlg([π]) ∧ PolarizedPair(π, χ) ⇒ ∃ r ∈ Hom(Aut_E(Ω), GL_a(Qbar_l)), ∃ wt ∈ ℤ, ∃ HT ∈ ((E → Qbar_l) → Multisets(ℤ)), PropsB(recT, π, ι, r, wt, HT). Inside PropsB, r is continuous ∧ IsSSRep(r) ∧ (∀ w ∌ l, ∀ A, ∀ h ∈ IsPlaceOver(A, w), ∀ rc, IsRecT(h, rc) ⇒ ∀ σ, IsLocComp(π, w, σ) ⇒ AwayB(wdOf(h, ι, r), rc(algNorm σ))) ∧ (∀ τ, HT(τ) = {(a − 1)/2 − z, z ∈ infChar([π], ι∘τ)} as multisets in ℂ) ∧ (∀ τ, HT(τ∘c) = {wt − n, n ∈ HT(τ)}, c complex conjugation of E) ∧ (∀ P, AI, LocTied(l, P, AI) nonempty ⇒ ∀ w, A, h, O, Bw, hj, AboveB(recT, π, ι, r, HT, P, h, Bw, hj))
```

The reading does not open the names `IsRecT`, `HChar`, `IsRegAlg`, `IsSSRep`, `AwayB`, `AboveB` and `IsPlaceOver, WD, IrrGL, wdOf, algNorm, LocPrime, LocAinf, LocTied, LocBridge, Induces`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest the existence of l-adic Galois representations attached to regular algebraic, polarized cuspidal automorphic representations of GL_a over a CM field, semisimple and continuous, compatible with a local Langlands correspondence at primes away from l, with Hodge–Tate weights determined by the infinitesimal character, and with a p-adic Hodge theoretic condition at primes above l.

The reader's confidence is medium. The quantifier structure, the existence claim and the two weight identities are fully visible, but IsRegAlg, IsSSRep, AwayB, AboveB, LawsT and the underlying automorphic types are shown without bodies.

The check found no error in this reading.

### Line 34, `galoisRepresentations_of_thetaLift`

The head is `UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift`, in the module Development › Automorphic Arithmetic › Foundations › Galois Representations › Integral Structures › Galois Representations Of Theta Lift. The line gathers 48,992 declarations and hangs from line 33, `galoisLocalGlobalStrong_recParameter`.

Assume the statement that the code calls TLiftK. Then Row0b recT holds, which is exactly the conclusion of line 33. That is, for every CM number field E with algebraic closure Ω, prime l, ring isomorphism ι from Qbar l to ℂ, a ≥ 1, π of type CuspSub E a and χ of type HChar on the maximal real subfield, if IsRegAlg and PolarizedPair π χ hold then some homomorphism r, integer wt and function HT satisfy PropsB recT π ι r wt HT.

- Premise 1. TLiftK holds, which says that for every CM number field E with maximal real subfield E⁺, every B of type Base with GoodK (cj E) B, every n ≥ 1 and every X of type Spc of size n with X.J = 1 and X.IsHerm (cj E) B n 0, there is a natural number d₀ such that for every d ≥ d₀, every W of type Spc of size d with W.J equal to δ times the identity matrix for some δ in E and W.IsSkew (cj E) B d 0, every pair of characters χX, χW satisfying IsHecke, ResEtaPow with exponents n and d respectively, and HasExp with integer families mX and mW, every space U of functions on UA E n with IsAutRepU U, and every family lam of weights with HasWeightAt U at each infinite place w and with d + mW(w) ≤ 2·lam(w)_k for all w and k, there exists a space U' of functions on UA E d with IsLift B χX χW mX mW lam U U'.
- Conclusion. Row0b recT holds, that is, every π over a CM field with IsRegAlg and PolarizedPair has some r, wt and HT with PropsB recT π ι r wt HT.

```
TLiftK ⇒ Row0b(recT), where TLiftK ⇔ ∀ E CM, ∀ B ∈ Base(E⁺, E), GoodK(cj, B) ⇒ ∀ n ≥ 1, ∀ X ∈ Spc(n), X.J = 1 ⇒ IsHerm(X, cj, B, n, 0) ⇒ ∃ d₀ ∈ ℕ, ∀ d ≥ d₀, ∀ W ∈ Spc(d), ∀ δ ∈ E, W.J = δ·I_d ⇒ IsSkew(W, cj, B, d, 0) ⇒ ∀ χX, χW, mX, mW, IsHecke(χX) ⇒ IsHecke(χW) ⇒ ResEtaPow(K, χX, n) ⇒ ResEtaPow(K, χW, d) ⇒ HasExp(B.emb, χX, mX) ⇒ HasExp(B.emb, χW, mW) ⇒ ∀ U, ∀ lam, IsAutRepU(U) ⇒ (∀ w, HasWeightAt(U, B.emb(w), lam(w))) ⇒ (∀ w, k, d + mW(w) ≤ 2·lam(w)_k) ⇒ ∃ U', IsLift(B, χX, χW, mX, mW, lam, U, U'), with K the image of (E⁺)ˣ in the unit group of the adele ring of E⁺, and Row0b(recT) ⇔ ∀ E CM, Ω, l, ι, a ≥ 1, π, χ, IsRegAlg([π]) ∧ PolarizedPair(π, χ) ⇒ ∃ r, wt, HT, PropsB(recT, π, ι, r, wt, HT)
```

The reading does not open the names `HasWeightAt`, `IsHerm, IsSkew` and `IsRegAlg, IsSSRep, AwayB, AboveB, LawsT`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that a theta lifting statement between unitary groups of sizes n and d, for all sufficiently large d, is enough to construct the Galois representations of line 33.

The reader's confidence is medium. Both the premise and the conclusion have fully visible quantifier structure, but the key conditions IsHerm, IsSkew, IsLiftWt, LocPair, HasWeightAt, IsRegAlg, AwayB and AboveB are opaque.

The check found no error in this reading.

### Line 35, `geoOne_holds`

The head is `UpperTheory.Gal.Int.Geo.geoOne_holds`, in the module Development › Automorphic Arithmetic › Foundations › Galois Representations › Integral Structures › Geometric Flag Bases › Weight One Geometric Realization. The line gathers 43,403 declarations and hangs from line 34, `galoisRepresentations_of_thetaLift`.

With no premises, the statement GeoOne holds. GeoOne takes a CM number field E with algebraic closure Ω, a prime l, a ring isomorphism ι from Qbar l to ℂ, an odd a, a natural number d with FieldOK E l d, an x in E with x² = −d, a finite set T of primes of E none of which satisfies IsSplitAt, two primes w₀ and v' of E that contain l, lie over different primes of the maximal real subfield and satisfy OneK x w₀ v', a finite set S of primes, and a space U of complex functions on UA E a satisfying AutOffT T U, TyEll E l a w₀ U, SphOffU w₀ S U, SatU U v' B for some B, and LacWtAt ι v' U. It concludes three things, namely that some size dd and homomorphism ρ from the automorphism group of Ω over E to GL_dd(Qbar l) satisfy VBase ι d U ρ, that at every prime w with UsPl d w, not containing l and with some SatU datum there is such a ρ that also satisfies ESAt ι ρ w (algSat a (normV w) B) for every B with SatU U w B, and that at every prime w containing l with OneK x w v', apart from w₀ and from v' and with some SatU datum, there is such a ρ with CrysAt ρ w and JumpsOcc U ι ρ w and there is such a ρ with PhiKilled ι ρ w a B for every B with SatU U w B.

- Conclusion. GeoOne holds, a universally quantified statement whose own hypotheses and three-part conclusion are described in the entry of line 35, with each part asserting the existence of its own dd and ρ.

```
∀ E CM number field, ∀ Ω algebraic closure of E, ∀ l prime, ∀ ι ∈ (Qbar_l ≅ ℂ), ∀ a ∈ ℕ, Odd(a) ⇒ ∀ d ∈ ℕ, FieldOK(E, l, d) ⇒ ∀ x ∈ E, x² = −d ⇒ ∀ T finite set of primes of E, NonSplitSet(T) ⇒ ∀ w₀, v' primes of E, l ∈ w₀ ⇒ l ∈ v' ⇒ Apart(v', w₀) ⇒ OneK(x, w₀, v') ⇒ ∀ S finite set of primes, ∀ U ⊆ (UA(E, a) → ℂ), AutOffT(T, U) ⇒ TyEll(E, l, a, w₀, U) ⇒ SphOffU(w₀, S, U) ⇒ (∃ B, SatU(U, v', B)) ⇒ LacWtAt(ι, v', U) ⇒ [ (∃ dd, ρ, VBase(ι, d, U, ρ)) ∧ (∀ w, UsPl(d, w) ⇒ l ∉ w ⇒ (∃ B, SatU(U, w, B)) ⇒ ∃ dd, ρ, VBase(ι, d, U, ρ) ∧ ∀ B, SatU(U, w, B) ⇒ ESAt(ι, ρ, w, algSat(a, normV(w), B))) ∧ (∀ w, l ∈ w ⇒ OneK(x, w, v') ⇒ Apart(w, w₀) ⇒ Apart(w, v') ⇒ (∃ B, SatU(U, w, B)) ⇒ (∃ dd, ρ, VBase(ι, d, U, ρ) ∧ CrysAt(ρ, w) ∧ JumpsOcc(U, ι, ρ, w)) ∧ (∃ dd, ρ, VBase(ι, d, U, ρ) ∧ ∀ B, SatU(U, w, B) ⇒ PhiKilled(ι, ρ, w, a, B))) ]
```

The reading does not open the names `SatU`, `LacWtAt`, `CrysAt`, `JumpsOcc`, `PhiKilled` and `UA`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest a geometric construction of l-adic Galois representations attached to automorphic representations of a definite unitary group of odd rank over a CM field containing an imaginary quadratic field, with the Eichler–Shimura relation at good split primes, and crystallinity, Hodge–Tate jumps and control of the crystalline Frobenius at primes above l.

The reader's confidence is medium. The full quantifier structure and many middle-level definitions are visible, but the innermost conditions (IsSplitAt, ImQ, SqAt, HasSatGL, IsCompAlong, IsSSRep, HTRichEx, IsCrysAt, IsJumpsAt, IsFrob, Lacunary) are shown without bodies, and nineteen further definitions were left out of the dossier.

The check found no error in this reading.

### Line 36, `geometric_realization_of_weight_one`

The head is `UpperTheory.Gal.Int.Geo.geometric_realization_of_weight_one`, in the module Development › Automorphic Arithmetic › Foundations › Galois Representations › Integral Structures › Geometric Flag Bases › Geometric Realization Of Weight One. The line gathers 41,443 declarations and hangs from line 35, `geoOne_holds`.

Assume the statement that the code calls HolomorphicLefschetzFormula, a fixed-point trace formula for pairs of finite étale maps between complex schemes. Then the statement GeoOne holds. GeoOne says that, for a CM number field E, a prime l, an odd number a and a complex space U of functions on a group UA E a meeting a list of conditions, there exist matrix representations ρ of the automorphism group of an algebraic closure of E over the field Qbar l that satisfy a condition called VBase, together with further conditions ESAt at certain primes not containing l and CrysAt, JumpsOcc and PhiKilled at certain primes containing l.

- Premise 1. HolomorphicLefschetzFormula holds, which reads as follows. For every scheme Z smooth of relative dimension d over Spec ℂ and satisfying IsProjOver, every scheme Y over Spec ℂ with two maps c1 and c2 from Y to Z over Spec ℂ that are both finite and étale, every finite set F of complex points of Y that consists exactly of the points y with y followed by c1 equal to y followed by c2, and every assignment A of d by d complex matrices such that each y in F satisfies IsTan with A y and det(1 − A y) ≠ 0, and for every natural number a, all the spaces hodgeH s a b are finite dimensional over ℂ and the sum over b from 0 to d of (−1)^b times the trace of hodgeTrace for c1 composed with hodgePull for c2 on hodgeH s a b equals the sum over y in F of the coefficient of X^a in det(1 + X·A y) divided by det(1 − A y).
- Conclusion. GeoOne holds, which reads as follows. For all E, Ω, l, ι, odd a, d with FieldOK E l d, x in E with x² = −d, T with NonSplitSet T, primes w₀ and v' containing l with Apart v' w₀ and OneK x w₀ v', every finite set S of primes and every U with AutOffT T U, TyEll at w₀, SphOffU w₀ S U, some B with SatU U v' B, and LacWtAt ι v' U, three things hold. First, some dimension dd and some ρ satisfy VBase ι d U ρ. Second, for every prime w with UsPl d w, not containing l and having some B with SatU U w B, some dd and ρ satisfy VBase and ESAt ι ρ w (algSat a (normV w) B) for every B with SatU U w B. Third, for every prime w containing l with OneK x w v', Apart w w₀, Apart w v' and some B with SatU U w B, some dd and ρ satisfy VBase, CrysAt ρ w and JumpsOcc U ι ρ w, and some possibly different dd and ρ satisfy VBase and PhiKilled ι ρ w a B for every B with SatU U w B.

```
HLF ⇒ GeoOne, where HLF is [∀ Z, s ∈ Hom(Z, Spec ℂ), d ∈ ℕ, s smooth of relative dimension d, IsProjOver(s) ⇒ ∀ Y, s' ∈ Hom(Y, Spec ℂ), c1, c2 ∈ Hom(Y, Z) with c1≫s = s', c2≫s = s', c1 and c2 finite étale ⇒ ∀ finite F ⊆ CxPts(s') with (∀ y, y ∈ F ⇔ y≫c1 = y≫c2), ∀ A from CxPts(s') to M_d(ℂ) with (∀ y ∈ F, IsTan(d, c1, c2, y, A y) ∧ det(1 − A y) ≠ 0), ∀ a ∈ ℕ, (∀ b, dim_ℂ hodgeH(s, a, b) < ∞) ∧ Σ_{b=0}^{d} (−1)^b tr(hodgeTrace_{c1}(a, b) ∘ hodgePull_{c2}(a, b)) = Σ_{y ∈ F} coeff_{X^a} det(1 + X·A y) / det(1 − A y)] and GeoOne is [∀ E CM number field, Ω algebraic closure of E, l prime, ι a ring isomorphism Qbar_l ≅ ℂ, a ∈ ℕ odd, d ∈ ℕ with FieldOK(E, l, d), x ∈ E with x² = −d, T finite set of primes of O_E with NonSplitSet(T), primes w₀, v' with l ∈ w₀, l ∈ v', Apart(v', w₀), OneK(x, w₀, v'), S finite set of primes, U a ℂ-subspace of the functions UA(E, a) → ℂ with AutOffT(T, U), TyEll(E, l, a, w₀, U), SphOffU(w₀, S, U), (∃ B, SatU(U, v', B)), LacWtAt(ι, v', U) ⇒ (∃ dd, ρ ∈ Hom(Aut_E(Ω), GL_dd(Qbar_l)), VBase(ι, d, U, ρ)) ∧ (∀ w, UsPl(d, w) ⇒ l ∉ w ⇒ (∃ B, SatU(U, w, B)) ⇒ ∃ dd, ρ, VBase(ι, d, U, ρ) ∧ ∀ B, SatU(U, w, B) ⇒ ESAt(ι, ρ, w, algSat(a, normV(w), B))) ∧ (∀ w, l ∈ w ⇒ OneK(x, w, v') ⇒ Apart(w, w₀) ⇒ Apart(w, v') ⇒ (∃ B, SatU(U, w, B)) ⇒ (∃ dd, ρ, VBase(ι, d, U, ρ) ∧ CrysAt(ρ, w) ∧ JumpsOcc(U, ι, ρ, w)) ∧ (∃ dd, ρ, VBase(ι, d, U, ρ) ∧ ∀ B, SatU(U, w, B) ⇒ PhiKilled(ι, ρ, w, a, B)))]
```

The reading does not open the names `Qbar l`, `NonSplitSet`, `FieldOK`, `UsPl`, `UA E a`, `AutOffT`, `TyEll`, `SatU`, `SphOffU`, `LacWtAt`, `VBase`, `ESAt`, `CrysAt`, `JumpsOcc`, `PhiKilled`, `IsProjOver`, `CxPts` and `hodgeH, hodgePull, hodgeTrace`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that the hypothesis is the holomorphic Lefschetz fixed-point formula for a correspondence on a smooth projective complex variety acting on Hodge cohomology, and that the conclusion is the construction, in the cohomology of unitary Shimura varieties, of l-adic Galois representations attached to automorphic representations of a unitary group, with local-global compatibility at unramified split places, crystallinity, Hodge–Tate weights and a Frobenius eigenvalue relation at places above l.

The reader's confidence is medium. The full logical shape of both the hypothesis and GeoOne is shown, but most leaf conditions rest on names without bodies and 61 definitions were left out of the dossier.

The check found no error in this reading.

### Line 37, `steps_holds`

The head is `UpperTheory.Gal.Int.Geo.steps_holds`, in the module Development › Automorphic Arithmetic › Foundations › Galois Representations › Integral Structures › Geometric Flag Bases › Geometric Realization Of Weight One. The line gathers 26,301 declarations and hangs from line 36, `geometric_realization_of_weight_one`.

The theorem states, with no hypothesis, that a bundle of seventeen propositions that the code calls Steps holds. Most of the seventeen are universally quantified implications about homomorphisms ρ from the group G E Ω, for a number field E with an algebraic closure Ω, into invertible matrices over the field Qbar l, about objects H of a type HTower E with a function θ on H.Γ, or about general matrix representations of a group. One of them, CharEx, instead asserts the existence of a map L that sends pairs (χ, n) to homomorphisms from G E Ω to the units of Qbar l, and another, SatCard, concerns a function space U and a multiset B and no representation. Nearly all the conditions that these implications relate are names whose bodies this dossier does not show.

- Conclusion. All seventeen fields of Steps hold, namely RepEx, ESStep, CrysStep, JumpStep, PhiStep, CutStep, TwES, TwCrys, TwJ, TwPhi, PhiOf, SatCard, JumpsOf, RichOf, CharEx, SSLeft and ContLeft.

```
Steps = RepEx ∧ ESStep ∧ CrysStep ∧ JumpStep ∧ PhiStep ∧ CutStep ∧ TwES ∧ TwCrys ∧ TwJ ∧ TwPhi ∧ PhiOf ∧ SatCard ∧ JumpsOf ∧ RichOf ∧ CharEx ∧ SSLeft ∧ ContLeft. Throughout, E is a number field, Ω an algebraic closure of E, l a prime, ι a ring isomorphism Qbar_l ≅ ℂ, H ∈ HTower(E), θ a function H.Γ → Qbar_l, ρ ∈ Hom(G(E, Ω), GL_dd(Qbar_l)), w a prime of O_E. RepEx is [Nice(H) ⇒ ∃ dd, ρ, ρ continuous ∧ IsSSRep(ρ) ∧ IsPiece(H, θ, ρ)]. ESStep is [Nice(H), ρ continuous, IsPiece(H, θ, ρ), l ∉ w, CongAt(H, θ, w, n, ϑ), HasRoots(ι, w, n, ϑ, R) ⇒ ESAt(ι, ρ, w, R)]. CrysStep is [Nice(H), ρ continuous, IsPiece(H, θ, ρ), l ∈ w, C ∈ Cover(H, θ, Ow(w)), C.Onto ⇒ CrysAt(ρ, w)]. JumpStep is [Nice(H), ρ continuous, IsPiece(H, θ, ρ), l ∈ w, GoodAt(H, θ, w) ⇒ JOcc(ι, ρ, w, HodgeAt(ι, H, θ))]. PhiStep is [Nice(H), ρ continuous, IsPiece(H, θ, ρ), l ∈ w, CongAt(H, θ, w, n, ϑ), HasRoots(ι, w, n, ϑ, R) ⇒ PhiK(ι, ρ, w, R)]. CutStep is [for any field L and θ with values in L, Nice(H) ⇒ ∀ w, (GoodAtW(H, θ, w) ⇒ GoodAt(H, θ, w)) ∧ ∀ n, ϑ, CongAtW(H, θ, w, n, ϑ) ⇒ CongAt(H, θ, w, n, ϑ)]. With χ ∈ Hom(G(E, Ω), Qbar_l^×), ρ and χ continuous, c ∈ ℂ, m a function from embeddings E → ℂ to ℤ, and Cl(ι, rk1 χ, w, {c}, τ ↦ {m(ι∘τ)}) assumed, TwES is [l ∉ w, ESAt(ι, ρ, w, R) ⇒ ESAt(ι, tw(ρ, χ), w, R·c)], TwCrys is [CrysAt(ρ, w) ⇒ CrysAt(tw(ρ, χ), w)], TwJ is [∀ Q, JOcc(ι, ρ, w, Q) ⇒ JOcc(ι, tw(ρ, χ), w, (τ, j) ↦ Q(τ, j − m τ))], TwPhi is [PhiK(ι, ρ, w, R) ⇒ PhiK(ι, tw(ρ, χ), w, R·c)]. PhiOf is [|B| = a, PhiK(ι, ρ, w, algSat(a, normV(w), B)) ⇒ PhiKilled(ι, ρ, w, a, B)]. SatCard is [E CM, SatU(U, w, B) ⇒ |B| = a]. JumpsOf is [E CM, (∀ τ, OverPl(ι, τ, w) ⇒ ∀ lam, HasWeightAt(U, τ, lam) ⇒ ∀ j ∈ wtJumps(lam), Q(τ, j)), JOcc(ι, ρ, w, Q) ⇒ JumpsOcc(U, ι, ρ, w)]. RichOf is [E CM, l ∈ v, LacWtAt(ι, v, U), JumpsOcc(U, ι, ρ, v) ⇒ HTRichEx(ρ, a)]. CharEx is [∀ E, Ω, l, ι, ∃ L sending (χ ∈ HChar(E), n) to a homomorphism G(E, Ω) → Qbar_l^×, (∀ χ, n, IsAlgPos(χ, n) ⇒ L(χ, n) continuous ∧ ∀ w, χ.UnrAt(w) ⇒ Cl(ι, rk1(L(χ, n)), w, {χ.val(w)}, τ ↦ {−n(ι∘τ)})) ∧ (∀ χ, n, χ', n', IsAlgPos(χ, n) ⇒ IsAlgPos(χ', n') ⇒ L(χ, n) = L(χ', n') ⇒ χ = χ')]. SSLeft is [∀ group Γ, field k, a, b, (∀ r, s, IsSSRep(sumRep(r, s)) ⇒ IsSSRep(r)) ∧ (∀ r, r', RepIso(r, r') ⇒ IsSSRep(r) ⇒ IsSSRep(r')) ∧ (∀ r, c, IsSSRep(r) ⇒ IsSSRep(tw(r, c)))]. ContLeft is [∀ topological group Γ, field k with a topological ring structure, a, b, (∀ r, s, sumRep(r, s) continuous ⇒ r continuous) ∧ (∀ r, r', RepIso(r, r') ⇒ r continuous ⇒ r' continuous) ∧ (∀ r, c, r continuous ⇒ c continuous ⇒ tw(r, c) continuous) ∧ (∀ c, c continuous ⇒ rk1(c) continuous)]
```

The reading does not open the names `HTower, Nice, IsPiece, Cover, Ow, GoodAt, GoodAtW, CongAt, CongAtW, HasRoots, HodgeAt, JOcc, PhiK`, `ESAt, CrysAt, JumpsOcc, PhiKilled, SatU, OverPl, HasWeightAt, wtJumps, LacWtAt, HTRichEx, IsSSRep`, `tw, rk1, sumRep, RepIso, Cl, HChar, IsAlgPos` and `G E Ω, Qbar l, normV, algSat, UA`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest a checklist of the steps of a construction of Galois representations from the cohomology of a tower of varieties with Hecke eigenvalues θ, covering existence of a semisimple piece, the Eichler–Shimura congruence relation away from l, crystallinity, Hodge–Tate jumps and a Frobenius relation at l, compatibility of each property with twisting by a character, Galois characters attached to algebraic Hecke characters, and the stability of semisimplicity and continuity under direct summands, isomorphism and twists. The name G E Ω suggests the automorphism group of Ω over E, which is the absolute Galois group of E.

The reader's confidence is low. The conjunction and the quantifier shape of every field are visible, but almost every condition named inside the fields is shown without a body, so the mathematical content cannot be read off.

The check found two errors in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- A says that "each of the seventeen is a universally quantified implication" about representations ρ, towers H or general matrix representations, but the Lean text of CharEx is "∀ … (ι : Qbar l ≃+* ℂ), ∃ L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ)" followed by a conjunction, which is an existence statement about a map L to characters, and SatCard reads "SatU U w B → B.card = a" and concerns U and B and no representation.
- A calls G E Ω "the automorphism group of an algebraic closure of a number field E" and writes "Aut_E(Ω)" in the notation, but this dossier shows only "abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]" without a body, so the meaning of G is asserted outside the field suggests.

The check found two errors in the second reading, which the text above does not use.

### Line 38, `kodaira_spencer_of_weight_one`

The head is `UpperTheory.Gal.Int.Geo.kodaira_spencer_of_weight_one`, in the module Development › Automorphic Arithmetic › Foundations › Galois Representations › Integral Structures › Geometric Flag Bases › Geometric Realization Of Weight One. The line gathers 11,850 declarations and hangs from line 36, `geometric_realization_of_weight_one`.

Assume the statement that the code calls HolomorphicLefschetzFormula, a fixed-point trace formula for pairs of finite étale maps between complex schemes. Then a bundle of six propositions that the code calls KSAll holds. The six say that a base object gb with IsStd exists when D.a = 1, that the type KS L gb k is never empty when Sc D G holds, and that the tower T.tower N g obtained from any member T of KS satisfies the conditions Nice, GoodAtW and CongAtW under stated hypotheses, and that the object bcAlong (T.tower N g) τ, for a ring map τ from R to ℂ, satisfies HOcc under stated hypotheses.

- Premise 1. HolomorphicLefschetzFormula holds, which reads as follows. For every scheme Z smooth of relative dimension d over Spec ℂ and satisfying IsProjOver, every scheme Y over Spec ℂ with two maps c1 and c2 from Y to Z over Spec ℂ that are both finite and étale, every finite set F of complex points of Y that consists exactly of the points y with y followed by c1 equal to y followed by c2, and every assignment A of d by d complex matrices such that each y in F satisfies IsTan with A y and det(1 − A y) ≠ 0, and for every natural number a, all the spaces hodgeH s a b are finite dimensional over ℂ and the sum over b from 0 to d of (−1)^b times the trace of hodgeTrace for c1 composed with hodgePull for c2 on hodgeH s a b equals the sum over y in F of the coefficient of X^a in det(1 + X·A y) divided by det(1 − A y).
- Conclusion. All six fields of KSAll hold, namely StdEx, KSEx, KSNice, KSGood, KSCong and KSHodge.

```
HLF ⇒ StdEx ∧ KSEx ∧ KSNice ∧ KSGood ∧ KSCong ∧ KSHodge, with HLF as in line 36. Throughout, p is a prime, D ∈ Datum(p), G ∈ HTGroup(p), L ∈ Link(D, G). StdEx is [∀ p, D with D.a = 1, ∀ number field E, ring isomorphism e from D.F to E, ∃ gb ∈ GBase(D.toG, E), IsStd(e, gb)]. KSEx is [∀ p, D, G, L, Sc(D, G) ⇒ ∀ field R that is a ℚ-algebra, gb ∈ GBase(D.toG, R), k ∈ ℕ, KS(L, gb, k) ≠ ∅]. KSNice is [Sc(D, G) ⇒ ∀ R, gb, k, T ∈ KS(L, gb, k), N ∈ Lv(p), index type J, g from J to Mem(L, N), Nice(T.tower(N, g))]. KSGood is [Sc(D, G) ⇒ ∀ number field E, e from D.F to E, gb ∈ GBase(D.toG, E), IsStd(e, gb) ⇒ ∀ k, T ∈ KS(L, gb, k), N, J, field A, g from J to Mem(L, N), θ from J to A, prime w of O_E, ideal 𝔴 of O_{D.F}, IsPl(e, w, 𝔴) ⇒ GoodGrp(g, θ, 𝔴) ⇒ GoodAtW(T.tower(N, g), θ, w)]. KSCong is [same data and IsPl(e, w, 𝔴) ⇒ ∀ ϑ from ℕ to A, CongGrp(g, θ, 𝔴, ϑ) ⇒ CongAtW(T.tower(N, g), θ, w, D.n, ϑ)]. KSHodge is [Sc(D, G) ⇒ ∀ lam assigning to each embedding τ of D.F in ℂ a non-increasing function Fin(G.n) → ℕ, ∃ k ∈ ℕ, ∀ field R over ℚ, gb ∈ GBase(D.toG, R), T ∈ KS(L, gb, k), N, J, g from J to Mem(L, N), θ from J to ℂ, f from G.GAf to ℂ, IsFnL(L, N.1, f) ⇒ Spec(L, lam, L.KN(N.1), j ↦ (g j).fn, θ, f) ⇒ ∀ ring map τ from R to ℂ with τ(gb.ρ) = D.ρc and (∀ i, c, τ(gb.t_i(c)) = D.tau_i(c)), ∀ ring automorphism σ of ℂ, i₀ ∈ Fin(D.a), h from Fin(G.n) to ℕ, IsHExp(D.tau_{i₀}, epsOf(D), conjWt(σ, lam), h) ⇒ ∀ i, HOcc(bcAlong(T.tower(N, g), τ), j ↦ σ(θ j), h i)]
```

The reading does not open the names `Sc, IsStd, IsPl, KS, Lv, Mem, GoodGrp, CongGrp`, `Nice, GoodAtW, CongAtW, HOcc, bcAlong`, `IsFnL, Spec, IsHExp, conjWt, epsOf`, `D.toG, T.tower, L.KN, G.GAf, (g j).fn` and `IsProjOver, CxPts, IsTan, hodgeH, hodgePull, hodgeTrace`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that KS stands for a Kodaira–Spencer type package attaching to PEL data of unitary type with one distinguished embedding a tower of varieties with automorphic sheaves of weight k, and that the six fields say this package exists, is well behaved, has good reduction and a congruence relation at suitable primes, and has the Hodge numbers predicted by the weight lam, the last being where the Lefschetz formula is used. The name bcAlong suggests the base change of a tower along the ring map τ, so that the last field concerns the tower after base change to ℂ.

The reader's confidence is medium. The hypothesis and the quantifier shape of all six fields are shown in full, but the central objects KS, Sc, IsStd, Nice, GoodAtW, CongAtW and HOcc are shown without bodies and 24 definitions were left out.

The check found one error in the first version of this reading. The text above is the corrected version, which passed the check after one round of correction.

- A says that the tower satisfies HOcc "after base change to ℂ", but the Lean text reads "HOcc (bcAlong (T.tower N g) τ) (fun j => σ (θ j)) (h i)" and the dossier shows only "def bcAlong (H : HTower k) {K : Type} [Field K] (τ : k →+* K) : HTower K" without a body, so the meaning of bcAlong is asserted outside the field suggests.

## Two lines of the exact outline

The outline of the exact graph, [`OUTLINE-EXACT.txt`](OUTLINE-EXACT.txt), has two lines that `OUTLINE.txt` lacks. [`README.md`](README.md) describes that graph. The heads of the two lines gather at least 10,000 declarations only in the exact tree, so the outline of the 38 lines leaves them out. They were read with the same briefs as the 38 lines, and their readings are in `reading-exact.json`. The numbers 39 and 40 continue the count of the 38 lines and give no place in the outline. The column Gathers gives the count of the exact tree.

| Line | Head | Hangs from | Gathers | Conclusion of the statement | Confidence |
|---:|---|---:|---:|---|---|
| 39 | `main_alt_alt` | 15 | 10,275 | Fm satisfies ConclF, which says that real numbers C′ and x0 exist such that for every x ≥ x0 with Fm.x1 < x and every index i, ShaFinOdd for Fm.D x i … | medium |
| 40 | `shape_closed_link_n_of_green` | 23 | 11,590 | TopG holds, which reads that for every real la with 1 < la and every G of type FReq, if HostExW la G.req holds and if every family Fm of every FamP … | medium |

### Line 39, `main_alt_alt`

The head is `GlobalTheory.NLinkClose.main_alt_alt`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Imports Further Tail. The line stands only in `OUTLINE-EXACT.txt`, gathers 10,275 declarations in the exact tree and hangs from line 15, `linkN_of_twGood_galoisPreconditions`. Folded into the line is the wrapper `conclF_of_family_facts_and_bound_at_two_three`.

Assume a bundle of seven background statements that the code calls Hypotheses₂, and then take any real number eps, any family record Fm of type FamP eps, any real number C and any natural number CT. If 0 ≤ C, and Fm satisfies the condition TwGood, the condition FactsFAlt with the constants C and CT, and the condition BoundAtTwoThreeFamilyFonAlt, then Fm satisfies ConclF. The dossier unfolds ConclF to the claim that real numbers C′ and x0 exist such that, for every real x ≥ x0 with Fm.x1 < x and every index i in Fm.Ix x, if the data record Fm.D x i satisfies ShaFinOdd then a record X of type HubData exists for which a fifteen-part condition that the code calls Concl holds for the size record Fm.L x i, the parameter record that Fm.params gives at x and i, the record X and the constant C′.

- Premise 1. The bundle Hypotheses₂ holds, which is assumed before eps, Fm, C and CT are chosen and which consists of seven named statements.
- Premise 2. The real number C satisfies 0 ≤ C.
- Premise 3. Fm satisfies TwGood, which unfolds to the existence of a real x0 such that for every x ≥ x0 with Fm.x1 < x and every index i a condition that the code calls TwConjAt holds and some N0 and S make a condition that the code calls TwGoodAt hold.
- Premise 4. Fm satisfies FactsFAlt with C and CT, which says that for every x with Fm.x1 < x and every index i the data record Fm.D x i satisfies a bundle that the code calls NormChoiceFacts and a condition that the code calls ExtraAlt with C and CT.
- Premise 5. Fm satisfies BoundAtTwoThreeFamilyFonAlt, which says that real numbers C″ and x0 exist such that for every x ≥ x0 with Fm.x1 < x, every index i and every choice of data HW, F, a comparison datum, a HubData record X and a real C₂, the bundle SetupAlt for these data implies the condition BoundAtTwoThree for Fm.L x i, the component ρ of X and C″.
- Conclusion. Fm satisfies ConclF, which says that real numbers C′ and x0 exist such that for every x ≥ x0 with Fm.x1 < x and every index i, ShaFinOdd for Fm.D x i implies that a HubData record X exists with Concl for Fm.L x i, Fm.params at x and i, X and C′.

```
Hypotheses₂ ⇒ ∀ eps ∈ ℝ ∀ Fm ∈ FamP(eps) ∀ C ∈ ℝ ∀ CT ∈ ℕ ( (0 ≤ C ∧ TwGood(Fm) ∧ FactsFAlt(Fm, C, CT) ∧ BoundAtTwoThreeFamilyFonAlt(Fm)) ⇒ ConclF(Fm) ), where hx denotes a proof of Fm.x1 < x, i ranges over Fm.Ix(x), D = Fm.D x i, S = Fm.L x i, nch = (Fm.ex x hx i).nch, and TwGood(Fm) ⇔ ∃ x0 ∈ ℝ ∀ x ≥ x0 ∀ hx ∀ i ( TwConjAt(D, nch) ∧ ∃ N0 ∃ T TwGoodAt(D, nch, ⟨twE(Fm, x, hx, i), N0, T⟩) ), FactsFAlt(Fm, C, CT) ⇔ ∀ x ∈ ℝ ∀ hx ∀ i ( NormChoiceFacts(D, nch) ∧ ExtraAlt(D, C, CT) ), BoundAtTwoThreeFamilyFonAlt(Fm) ⇔ ∃ C″, x0 ∈ ℝ ∀ x ≥ x0 ∀ hx ∀ i ∀ HW ∀ F ∀ cmp ∀ X ∈ HubData(D) ∀ C₂ ∈ ℝ ( SetupAlt(S, nch, HW, X, C₂) ⇒ BoundAtTwoThree(S, X.ρ, C″) ), ConclF(Fm) ⇔ ∃ C′, x0 ∈ ℝ ∀ x ≥ x0 ∀ hx ∀ i ( ShaFinOdd(D) ⇒ ∃ X ∈ HubData(D) Concl(S, Fm.params x hx i, X, C′) )
```

The reading does not open the names `Hypotheses₂`, `LocalEulerCharK`, `LocalFinitenessK`, `FamP`, `D7`, `TwGoodE`, `twE`, `NormChoiceFacts`, `ExtraAlt`, `HWOf`, `FonOf`, `CmpOf`, `SetupAlt`, `BoundAtTwoThree`, `ShaFinOdd`, `HubData` and `Concl`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The names suggest that Hypotheses₂ gathers published theorems (Fontaine's theory of B_cris, global Artin reciprocity, the Bloch–Kato local conditions, local Tate duality, the local Euler characteristic formula, finiteness of local Galois cohomology and an integral result of Bhatt and Scholze), that H0, H1 and H2 are cohomology groups of a local Galois group GK, that ShaFinOdd expresses finiteness of Tate–Shafarevich-type groups, and that BoundAtTwoThree is a bound at the primes 2 and 3, and the dossier leaves each of these readings unconfirmed.

The reader's confidence is medium. The dossier shows the whole logical skeleton of the statement, of its four conditions on Fm and of ConclF, yet nearly every condition inside them ends in a name without a shown body, the listings of FamP and D7 are cut, and five definitions were left out.

The check found no error in this reading.

### Line 40, `shape_closed_link_n_of_green`

The head is `UpperTheory.Top.shape_closed_link_n_of_green`, in the module Development › Automorphic Arithmetic › Theta Correspondence › Theta Pair Lifts › Third Place Series › Top Shape. The line stands only in `OUTLINE-EXACT.txt`, gathers 11,590 declarations in the exact tree and hangs from line 23, `zero_free_all_of_green_v_win`.

The theorem says that if the condition the code calls Green holds, then TopShapeAlt True True N TopG holds, where N is the requirement on a family class 𝒞 that LinkN holds in the Closed sense on 𝒞, which means that there is ε1 > 0 such that for every eps with 0 < eps ≤ ε1 there is a K for which LinkN Fm holds for every family Fm in FamP eps that lies in 𝒞 and satisfies Fm.Large K CH for some real CH. By the shown body of TopShapeAlt this unfolds to the claim that, under Green, for every family class 𝒜, every function cT of two real variables and every choice of the 51 further bound items (auxiliary selection data and hypotheses, among them two trivially true hypotheses in the slots V and NR and the hypothesis N applied to the class D3 3 𝒜), the condition the code calls TopG holds. TopG says that for every real la greater than 1 and every G of the type FReq, if HostExW la G.req holds and every family Fm in the class G.cls la satisfies HypV, then the class G.cls la satisfies a condition that the code calls FamilyClassConnected.

- Premise 1. Green holds, which is a shown statement about complex-valued functions on the matrix groups GL_d over the integers modulo a prime g, built on the opaque conditions IsPrimeLab, IsCuspOf and IsCusp.
- Premise 2. 𝒜 is an arbitrary family class, that is, a predicate on the families Fm of FamP eps for every real eps.
- Premise 3. cT is an arbitrary function that takes two real numbers to a real number.
- Premise 4. hEx says that MinkDiv implies ExS 𝒜 cT.
- Premise 5. sel is an arbitrary twist selection for 𝒜, which gives for every family Fm in 𝒜 a real threshold (sel Fm hc).1 and one object for each selected point, where a selected point means a real eps, a family Fm in FamP eps, a proof hc that 𝒜 Fm holds, a real x with Fm.x1 < x and (sel Fm hc).1 ≤ x, and an index i in Fm.Ix x.
- Premise 6. hduty says that every family Fm in 𝒜 satisfies Duty Fm.
- Premise 7. selS is a choice, at every selected point, of an element of STiesRAlt for the object that sel gives there.
- Premise 8. selP is a choice, at every selected point, of a P of type RowSideFamily (Fm.ex x hx i) together with a proof of RowSideDeterminedAlt for the field T of the object that sel gives there and P.
- Premise 9. selDH is a choice, at every selected point, of a pair p of natural numbers with (Fm.D x i).s.Del = p.1 and (Fm.L x i).etaSz = (Fm.D x i).R.m · p.2.
- Premise 10. selC is a choice, at every selected point, of an element of SquareIntegrableColumns for the field T of the object that sel gives there and the P that selP gives there.
- Premise 11. selB is a choice, at every selected point, of an element of RealTBAlt built from the choices of sel, selP, selC, selDH and selS at that point.
- Premise 12. hRB says that at every selected point IndefiniteRealisationBoundedRows holds for the element that selB gives there.
- Premise 13. hTw says that at every selected point TieTwRec (Fm.L x i) Tw holds, where Tw is the field S0.Tw of the P that selP gives there.
- Premise 14. hPA says that AllRealisationsPrimitive holds for sel and for the realisation choice read off from selB by indefiniteRealisationChoiceOfSelection.
- Premise 15. hLamP says that at every selected point RowsHoldLam3 P holds for the P that selP gives there.
- Premise 16. hDivG says that at every selected point DivRows3G P holds for the P that selP gives there.
- Premise 17. hDcPtG says that at every selected point DcPtG P holds for the P that selP gives there.
- Premise 18. hTu says that, in the Closed sense on the class WithTw (WithSm (WithChN 𝒜)), the inequality cT eps Fm.CYL ≤ Fm.CTu implies TuSize Fm.
- Premise 19. hn4 says that, in the Closed sense on the same class WithTw (WithSm (WithChN 𝒜)), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev holds for every real x with Fm.x1 < x and every index i in Fm.Ix x.
- Premise 20. hLit says that LitThin holds.
- Premise 21. hVC is a proof of the slot V, which the theorem sets to the trivially true proposition True.
- Premise 22. hWu says that WuDecayOfGap holds.
- Premise 23. hRF says that RowsFinDim holds.
- Premise 24. hTF says that, in the Closed sense on the class D3 3 𝒜, TFrame Fm (Fm.CYL + 1) (1/4) 3 (1/2) Fm.CTu 3 holds.
- Premise 25. c30 is an arbitrary map from finite lists of real numbers to the type CountingConstants.
- Premise 26. hc30 says that for every family Fm the constants c30 Fm.cOut satisfy 0 ≤ (c30 Fm.cOut).C and 2 · (Fm.CYL + 1) ≤ (c30 Fm.cOut).A.
- Premise 27. sTy is an element of what the code calls TypeP, which is shown without a body.
- Premise 28. sNG is an element of what the code calls RowNGP, which is shown without a body.
- Premise 29. sM is an element of what the code calls RowMainEqP, which is shown without a body.
- Premise 30. sLp says that LoopRowS holds for the constant 3, the class D3 3 𝒜 and the selection that pairs the threshold (sel Fm (d3_a hc)).1 with the toSTies part of selS.
- Premise 31. sO says that, in the Closed sense on D3 3 𝒜, for every proof hc that Fm lies in D3 3 𝒜, TheoremSSelected holds for Fm, the constant 3 and the same pair of the threshold (sel Fm (d3_a hc)).1 and the toSTies part of selS.
- Premise 32. h30 says that, in the Closed sense on D3 3 𝒜, CountAllPointsClass PLevT' Fm holds with the five constants n0, A, C, c and cb of c30 Fm.cOut.
- Premise 33. hInstR says that at every selected point both VolSigIndep (Fm.D x i) and ClassItemsAt (Fm.D x i) r hold, where r is ((Fm.D x i).sp.Y 0).rank.
- Premise 34. selJ is an element of IndefiniteRealisationSelection for 𝒜, sel, selS, selP, selDH, selC, the kernel choice kernelChoiceOfSelection selB and the realisation choice indefiniteRealisationChoiceOfSelection selB.
- Premise 35. jOn says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that BaseVectorImageFull (Fm.D x i) holds for every x ≥ x0 and every index i in Fm.Ix x.
- Premise 36. hMt says that for every family Fm in 𝒜 there is a real x0 such that for every x ≥ x0, every index i in Fm.Ix x and every μ in (Fm.D x i).what₂.Tup, the set Mtilde μ is closed under scalar multiplication by embLL a for every a in the ring of integers of the field (Fm.D x i).what₂.LL.
- Premise 37. rRows says that, in the Closed sense on D3 3 𝒜 with the real CH kept as an argument, for every proof hc that Fm lies in D3 3 𝒜, RowsAtSelAlt holds for sel, the realisation choice from selB, the row condition DefRowsFAlt of that realisation choice, SingleMapCondition selB, Fm, d3_a hc and CH.
- Premise 38. aPt0 says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that Conclusion6 (Fm.D x i) u holds for every x with x0 ≤ x and Fm.x1 < x, every index i in Fm.Ix x and every u.
- Premise 39. aPtTw says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw holds for every x with x0 ≤ x and Fm.x1 < x and every index i in Fm.Ix x.
- Premise 40. aPer0 says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that PeriodClassSumWeyl (Fm.D x i) holds for every x with x0 ≤ x and Fm.x1 < x and every index i in Fm.Ix x.
- Premise 41. aPerTw says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw holds for every x with x0 ≤ x and Fm.x1 < x and every index i in Fm.Ix x.
- Premise 42. aP10 says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that for every x with x0 ≤ x and Fm.x1 < x, every index i in Fm.Ix x and every u, both Conclusion5Sharp (Fm.D x i) u and TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u hold.
- Premise 43. aAtG says that, in the Closed sense on D3 3 𝒜, there is a real C1 such that familySizeBoundAtTypePrime Fm C1 holds and such that, for some real x0, UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 holds for every x with Fm.x1 < x and x0 ≤ x and every index i in Fm.Ix x.
- Premise 44. aC2 says that, in the Closed sense on D3 3 𝒜, FamilySecondComplementInputs Fm holds.
- Premise 45. hServ says that SelectionServed holds for the class D3 3 𝒜 and the selection that sends Fm and hc to sel Fm (d3_a hc).
- Premise 46. nR is a proof of the slot NR, which the theorem sets to the trivially true proposition True.
- Premise 47. nRest says that, in the Closed sense on D3 3 𝒜, LinkN Fm holds, which is the slot N of the theorem applied to the class D3 3 𝒜.
- Premise 48. cIc is an arbitrary real number.
- Premise 49. hcI says that 0 < cIc.
- Premise 50. irrC says that, in the Closed sense on D3 3 𝒜, there is a real x0 such that for every x ≥ x0 and every index i in Fm.Ix x there is an A of type AllRows (Fm.D x i) with LabelCountGoodInjective A, AllJoinA A and CountAllRows A (epsC cIc r f), where r is (Fm.D x i).R.r and f is (Fm.D x i).R.f.
- Premise 51. zL says that, in the Closed sense on D3 3 𝒜, for every proof hc that Fm lies in D3 3 𝒜 there is a real xr such that for every x with Fm.x1 < x, (sel Fm (d3_a hc)).1 ≤ x and xr ≤ x, every index i in Fm.Ix x and every k below (Fm.D x i).R.m, the map that multiplies vectors by the matrix lPrj, formed from the P that selP gives at that point, is surjective.
- Premise 52. tie says that, in the Closed sense on D3 3 𝒜, RealPlaceSecondLayerConditions Fm holds.
- Premise 53. hU says that MassRatioUnderVolume D holds for every D.
- Premise 54. hG says that GenusMassAt D 2 holds for every D.
- Conclusion. TopG holds, which reads that for every real la with 1 < la and every G of type FReq, if HostExW la G.req holds and if every family Fm of every FamP eps with G.cls la Fm satisfies HypV Fm.toFamCore, then FamilyClassConnected (G.cls la) holds.

```
Green ⇒ ∀𝒜∈FamClass ∀cT∈(ℝ→ℝ→ℝ) ∀sel∈TwistSelection(𝒜) ∀selS ∀selP ∀selDH ∀selC ∀selB ∀c30∈(List ℝ→CountingConstants) ∀cIc∈ℝ ( [ (MinkDiv ⇒ ExS(𝒜,cT)) ∧ (∀eps ∀Fm∈FamP(eps), 𝒜(Fm) ⇒ Duty(Fm)) ∧ (∀pt, IndefiniteRealisationBoundedRows(selB(pt))) ∧ (∀pt, TieTwRec(L, P.S0.Tw)) ∧ AllRealisationsPrimitive(sel, QB) ∧ (∀pt, RowsHoldLam3(P)) ∧ (∀pt, DivRows3G(P)) ∧ (∀pt, DcPtG(P)) ∧ Closed(𝒲, Fm ↦ (cT(eps, Fm.CYL) ≤ Fm.CTu ⇒ TuSize(Fm))) ∧ Closed(𝒲, Fm ↦ ∀x ∀hx∈(Fm.x1<x) ∀i∈Fm.Ix(x), ClassNumberFormula₂(D, ex.lev)) ∧ LitThin ∧ True ∧ WuDecayOfGap ∧ RowsFinDim ∧ Closed(𝒟, Fm ↦ TFrame(Fm, Fm.CYL+1, 1/4, 3, 1/2, Fm.CTu, 3)) ∧ (∀eps ∀Fm∈FamP(eps), 0 ≤ c30(Fm.cOut).C ∧ 2·(Fm.CYL+1) ≤ c30(Fm.cOut).A) ∧ TypeP ∧ RowNGP ∧ RowMainEqP ∧ LoopRowS(3, 𝒟, s) ∧ Closed(𝒟, Fm ↦ ∀hc∈𝒟(Fm), TheoremSSelected(Fm, 3, s(Fm,hc))) ∧ Closed(𝒟, Fm ↦ CountAllPointsClass(PLevT', Fm, k.n0, k.A, k.C, k.c, k.cb) with k = c30(Fm.cOut)) ∧ (∀pt, VolSigIndep(D) ∧ ClassItemsAt(D, (D.sp.Y 0).rank)) ∧ IndefiniteRealisationSelection(𝒜, sel, selS, selP, selDH, selC, kernelChoiceOfSelection(selB), QB) ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x≥x0 ∀i∈Fm.Ix(x), BaseVectorImageFull(D)) ∧ (∀eps ∀Fm∈FamP(eps), 𝒜(Fm) ⇒ ∃x0∈ℝ ∀x≥x0 ∀i∈Fm.Ix(x) ∀μ∈D.what₂.Tup ∀a∈𝒪(D.what₂.LL) ∀y∈Mtilde(μ), embLL(a)•y ∈ Mtilde(μ)) ∧ Closed(𝒟, (Fm,CH) ↦ ∀hc∈𝒟(Fm), RowsAtSelAlt(sel, QB, DefRowsFAlt(QB), SingleMapCondition(selB), Fm, d3_a(hc), CH)) ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x (x0≤x ⇒ ∀hx∈(Fm.x1<x) ∀i∈Fm.Ix(x) ∀u, Conclusion6(D,u))) ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x (x0≤x ⇒ ∀hx∈(Fm.x1<x) ∀i∈Fm.Ix(x), TwistedPointIntegral(D, ex.tw))) ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x (x0≤x ⇒ ∀hx∈(Fm.x1<x) ∀i∈Fm.Ix(x), PeriodClassSumWeyl(D))) ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x (x0≤x ⇒ ∀hx∈(Fm.x1<x) ∀i∈Fm.Ix(x), TwistedPeriodAdmissible(D, Fm.X x i, ex.tw))) ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x (x0≤x ⇒ ∀hx∈(Fm.x1<x) ∀i∈Fm.Ix(x) ∀u, Conclusion5Sharp(D,u) ∧ TwistedColumnBoundAtT(Fm.X x i, ex.tw, u))) ∧ Closed(𝒟, Fm ↦ ∃C1∈ℝ ((∃x0∈ℝ ∀x ∀hx∈(Fm.x1<x) (x0≤x ⇒ ∀i∈Fm.Ix(x), UsedTuplesBoundByConstant(D, L, ex.errX, C1))) ∧ familySizeBoundAtTypePrime(Fm, C1))) ∧ Closed(𝒟, Fm ↦ FamilySecondComplementInputs(Fm)) ∧ SelectionServed(𝒟, (Fm,hc) ↦ sel Fm (d3_a hc)) ∧ True ∧ Closed(𝒟, Fm ↦ LinkN(Fm)) ∧ 0 < cIc ∧ Closed(𝒟, Fm ↦ ∃x0∈ℝ ∀x≥x0 ∀i∈Fm.Ix(x) ∃A∈AllRows(D), LabelCountGoodInjective(A) ∧ AllJoinA(A) ∧ CountAllRows(A, epsC(cIc, D.R.r, D.R.f))) ∧ Closed(𝒟, Fm ↦ ∀hc∈𝒟(Fm) ∃xr∈ℝ ∀x ∀hx∈(Fm.x1<x) ∀h∈((sel Fm (d3_a hc)).1≤x) (xr≤x ⇒ ∀i∈Fm.Ix(x) ∀k∈Fin(D.R.m), (v ↦ M_k·v) is surjective)) ∧ Closed(𝒟, Fm ↦ RealPlaceSecondLayerConditions(Fm)) ∧ (∀D, MassRatioUnderVolume(D)) ∧ (∀D, GenusMassAt(D, 2)) ] ⇒ TopG ), where the data binders are pulled to the front and the hypotheses keep the order of the text, where ∀pt abbreviates ∀eps∈ℝ ∀Fm∈FamP(eps) ∀hc∈𝒜(Fm) ∀x∈ℝ ∀hx∈(Fm.x1<x) ∀h∈((sel Fm hc).1≤x) ∀i∈Fm.Ix(x), where D = Fm.D x i, L = Fm.L x i, ex = Fm.ex x hx i, P = (selP Fm hc x hx h i).1, 𝒲 = WithTw(WithSm(WithChN 𝒜)), 𝒟 = D3 3 𝒜 = Des(WithChN 𝒜, 3), QB = indefiniteRealisationChoiceOfSelection(selB), s(Fm,hc) = ⟨(sel Fm (d3_a hc)).1, (x,hx,h,i) ↦ (selS Fm (d3_a hc) x hx h i).toSTies⟩, M_k = lPrj(D, P'.A3.A, P'.P0, P'.ψ0, P'.A3.fam3.toSub2(P'.Zs), k, P'.A3.A.μ0) with P' = (selP Fm (d3_a hc) x hx h i).1, where Closed(𝒞,φ) ⇔ ∃ε1∈ℝ (0<ε1 ∧ ∀eps∈ℝ (0<eps ⇒ eps≤ε1 ⇒ ∃K∈TransportedAlt ∀Fm∈FamP(eps) ∀CH∈ℝ (𝒞(Fm) ⇒ Fm.Large(K,CH) ⇒ φ(Fm,CH)))), where LinkN(Fm) ⇔ ∃C,x0∈ℝ ∀x≥x0 ∀i∈Fm.Ix(x) (ShaFinOdd(D) ⇒ ∀j∈{1,…,D.R.m}, LinkN_at(L,j,C)), where LinkN_at(L,j,C) ⇔ (the series Σ_l vvTerm(D,l) is summable ⇒ etaSum(L,j) ≤ L.dZ0(j)·(C·(D.R.f·D.R.m·L.sc.b·(L.sc.L)² + (log L.sc.x)²·L.Nc) + Σ_l vvTerm(D,l))), where ShaFinOdd(D) ⇔ ∀ prime p ∀e∈ℕ (0<e ⇒ e<D.R.t ⇒ shaLen(D.nd.ldat p, e) ≠ ⊤), where TopG ⇔ ∀la∈ℝ ∀G∈FReq (1<la ⇒ HostExW(la, G.req) ⇒ (∀eps∈ℝ ∀Fm∈FamP(eps), G.cls(la)(Fm) ⇒ HypV(Fm.toFamCore)) ⇒ FamilyClassConnected(G.cls(la))), and where Green ⇔ ∀ prime g ∀L∈LabelDatum(g) ∀d∈ℕ (0<d ⇒ ∃τ∈((ℤ/g)[X] → (GL_d(ℤ/g) → ℂ)) [ (∀P, IsPrimeLab(d,P) ⇒ IsCuspOf(L,P,τ(P)) ∧ τ(P)(1) = ∏_{i=1}^{d−1} (g^i − 1)) ∧ (∀P ∀P', IsPrimeLab(d,P) ⇒ IsPrimeLab(d,P') ⇒ τ(P)=τ(P') ⇒ P=P') ∧ (∀χ∈(GL_d(ℤ/g) → ℂ), IsCusp(χ) ⇒ ∃P, IsPrimeLab(d,P) ∧ χ=τ(P)) ])
```

The reading does not open the names `LabelDatum`, `IsPrimeLab`, `IsCuspOf`, `IsCusp`, `FamP`, `FamCore`, `Large`, `etaSum`, `vvTerm`, `shaLen`, `D7`, `SizeData₂`, `FReq`, `HostExW`, `HypV`, `FamilyClassConnected`, `Des`, `d3_a`, `DesignChoices`, `TwistSelectionFunctions`, `kernelChoiceOfSelection`, `CountingConstants`, `TypeP`, `RowNGP`, `RowMainEqP`, `LoopRowS`, `TheoremSSelected`, `CountAllPointsClass`, `VolSigIndep`, `ClassItemsAt`, `IndefiniteRealisationSelection`, `BaseVectorImageFull`, `RowsAtSelAlt`, `Conclusion6`, `TwistedPointIntegral`, `PeriodClassSumWeyl`, `TwistedPeriodAdmissible`, `Conclusion5Sharp`, `TwistedColumnBoundAtT`, `UsedTuplesBoundByConstant`, `familySizeBoundAtTypePrime`, `FamilySecondComplementInputs`, `SelectionServed`, `AllRows`, `epsC`, `lPrj`, `RealPlaceSecondLayerConditions`, `MassRatioUnderVolume` and `GenusMassAt`.

The next sentences are a suggestion from the names, which the Lean text of the dossier does not show. The name Green together with the value ∏(g^i − 1) suggests J. A. Green's description of the cuspidal characters of GL_d over the field with g elements, labelled by irreducible polynomials, the names shaLen and ShaFinOdd suggest finiteness of Tate–Shafarevich-type groups, and the head name with its parent zero_free_all_of_green_v_win suggests that this theorem reduces a zero-free statement to Green plus the one remaining input LinkN, but the dossier confirms none of these readings.

The reader's confidence is medium. The dossier shows the head statement, TopShapeAlt, Green, Closed, LinkN and TopG in full, so the logical form and every constant are visible, but the conclusion TopG rests on the unseen names FReq, HostExW, HypV and FamilyClassConnected, the class D3 rests on the unseen Des, the condition Large is not shown, FamP is cut, 8 definitions were left out and most hypotheses are names without bodies.

The dossier shows the definition TopShapeAlt in full, taken from the source file, because the statement splitter cuts it before its conclusion. A first reading from the cut dossier had confidence low.

The check found no error in this reading.
