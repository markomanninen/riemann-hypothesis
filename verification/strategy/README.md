# The strategy of the proof, followed through the Lean text

The proof in [`src`](../../src) derives the five theorems of [`Main.lean`](../../src/Main.lean)
from one inequality. The first theorem states that a Dirichlet L-function has no zero with real
part above 1/2, and the other four follow from it. The inequality says that a weighted sum over
the prime powers up to x is at most x^(1/2 + cε) for all x between Y and Y^(3/2), for arbitrarily
large Y, every small ε > 0 and a constant c. The proof gets the inequality by bounding the slope
of one lattice from two sides. A divisibility inequality bounds the slope from above by m times a
main term, where m is the number of theta lifts in a chain between unitary groups. A slope
inequality bounds the same slope from below. The two bounds leave an error of about x/m + m for
the weighted sum, and that error is smallest when m is about √x.

This document follows that route through the Lean text. It goes from `Main.lean` down to the
upper bound for one lift and the lower bound for the maps into the lattice, and then through the
assembly of the conditions and the branches that supply the premises. For each step it names the
theorem that carries the step, says what the theorem states and how much of its proof was read,
and gives the number of declarations that the theorem rests on.

A language model, Claude, read the route in one session on 23 and 24 November 2026. Seven further
runs of the same model each read one branch and reported back. A table below names the seven
readings, and a section names the reading behind a sentence that comes from a report. A sentence
without a named reading reports what this session read. No mathematician has checked
the readings, and Lean was not run for this document. A reading shows what the text states and
how the proofs call each other. It leaves open whether a definition is the mathematical object
that its name suggests.

The counts of this document come from compiled files of the project, which
`lake exe cache get` downloads from the build cache of the repository. The check that the
[README](../../README.md) of the repository describes, `lake comparator`, compiles the source
and checks the proof against `Challenge.lean`, and that README records no complete run of it on
the current source.

## Words used here

- A declaration, a module, the outline and the verb gathers mean what the
  [README of the skeleton](../skeleton/README.md) says. A constant is a compiled declaration or
  a name that Lean creates for one, such as the constructor of a record.
- A theorem rests on the declarations of the project that its compiled statement and proof reach
  through other constants of the project, the theorem itself included. [`cone.py`](cone.py)
  counts them in the exact graph of [`../decl-graph`](../decl-graph/README.md), which was built
  on 2026-11-23. Mathlib and Lean's library are outside the count. The outline counts what a
  theorem gathers, which is the part that the five theorems reach through that theorem alone, so
  a number of the outline of the exact graph is at most the number given here.
- A proof was read in full when every line of it was read. A proof was read at its top when its
  first call and the premises passed to that call were read. A theorem was read by statement
  when its statement was read and its proof was left unread.
- This session means the model session that wrote this document.
- A premise is a hypothesis of a theorem. A premise is supplied when a call of the theorem passes
  a proof of it. A closed theorem is a theorem that takes no premises.
- A record is a Lean `structure`. A bundle is a record whose fields are propositions, so a field
  of it is one premise.
- A datum is a value of the code's record `D7`, which [`D7.md`](../skeleton/D7.md) opens. It
  holds a host, lattices, maps and the number m of lifts. A datum has a finite set of words, the
  code's type `what₂.Word`. A family holds a datum for every large x and every index of a set
  that depends on x.
- A host is the code's record for an auxiliary abelian number field.
- The slope of a lattice and the height of a map are the code's numbers `mu` and `h`. This
  document uses them as the code names them and did not open their definitions.
- A link is one of the conditions on a family in
  [`GlobalTheoremInputs.lean`](../../src/Formalism/SharpRestriction/GlobalTheoremInputs.lean)
  whose names begin with `Link`.
- The note is the four-page note by the author of the Lean source at
  <https://alpo.ge/remark.pdf>. Its timeline has 20 numbered entries.
- A sentence that says the names suggest something, or that calls itself an interpretation or a
  guess, goes beyond what the Lean text shows.

The seven parallel readings are these. Each brief asked for the Lean text only, and each report
marked its own guesses.

| Name used below | What it read |
|---|---|
| the Landau reading | the proof of `zeroFree_of_rpow_window`, 22 lemmas in full and 11 by statement |
| the reading of six proofs | `Ga_bound5`, `boundsMu`, `height_chain_atR` and `young_diagram_step_origin` in full, the statement `divIneqRecord` that `RecNums.divIneq` applies, and the beginning of `core_ineq` |
| the reading of the chain | the premises of `rowsU_of_colPins_alt`, at the top of each proof |
| the reading of the links | `linkCore` in full and the statements of the links |
| the reading of `VWin` | the statement of `VWin` two definitions deep, and the proofs above it at their tops |
| the reading of `Row` | the statement of `Row` with its definitions, and the proofs above it at their tops |
| the wiring reading | the file of `every_character_of_literature_of_vWin`, and three proofs in full |

## The route in nine steps

1. The five theorems follow from one statement, that a Dirichlet L-function has no zero with
   real part above 1/2. The Lean statement sets aside the trivial character at s = 1.
2. That statement follows from an upper bound x^θ, for every θ above 1/2, for a weighted prime
   sum `Gm x` on the intervals from Y to Y^(3/2). The step is a Landau argument.
3. The sum `Gm` belongs to a finite set of wanted characters. The proof places these characters
   among all characters of an auxiliary abelian field and bounds the sums of the other characters
   separately.
4. The sum over all characters of the auxiliary field equals an arithmetic quantity `ASK` minus
   its main term, by finite Fourier inversion.
5. `ASK` is bounded through the slope of a lattice. A divisibility inequality `DIV` bounds the
   slope from above, and a slope inequality `SlopeIneq` bounds it from below.
6. Both bounds concern linear maps into that lattice, one map for each word of a datum. Each map
   is the composite of a chain of m theta kernels between unitary groups of ranks k + j(t + 1),
   for j from 0 to m.
7. The upper bound adds one term a·log a − a for each lift and each top place, where a is the
   top weight at that place. Interlacing weights and a hook product leave exactly that term
   unmatched.
8. The lower bound needs each map to be nearly an isometry, and two maps of different words to
   overlap by no more than a stated amount.
9. After division by m the two bounds leave an error of about x/m + m for the weighted sum. The
   error is smallest at m = √x, where it is 2√x, and that gives the exponent 1/2.

The sections below have names and no numbers, and the word step means one of these nine. The
four parts of the Landau argument are called stages.
The section on the two bounds covers steps 4, 5 and 9. Two sections cover the upper bound and
step 7, one covers the chain of step 6, and one covers the lower bound of step 8.

Further branches supply the premises of this route. One proves a bound on lengths of Galois
cohomology groups, which the code calls `VWin`. One proves the existence of Galois
representations, which the code calls `Row`. The largest one builds a record of 46 fields that
holds the chains of lifts and their properties, and a covolume bound feeds it.

## What the note says about the strategy

The note gives the idea in one paragraph and a timeline. This session read the PDF directly.

- The note says that "In Stepanov's argument resolving Riemann over function fields one uses a
  divisor involving multiplicity" and that the argument "is a descendant of Stepanov's, but
  multiplicity is hard to find over the integers".
- Entry 5 of the timeline switches to the sum Σ Λ(n)·(X/n − 1) over n ≤ X, minus X log X, plus
  (1 + γ)·X. The Lean definition `Gz`, which the section on the prime sum gives, is this
  expression, and it is the part of the sum `Gm` of step 2 that belongs to the trivial character.
- Entry 7 speaks of "GGP periods, with values 0, 1 meaning interlacing weights".
- Entry 8 reads "Iterated theta lifts U(X_0) → U(X_1) → ··· → U(X_m) between totally definite
  unitary groups, π ↦ π ⊞ μ_j[t], wins multiplicity m. Time to take m like √X".
- Entries 9, 10, 12, 13 and 16 name the norms of the lifts with divisibility "via
  Chowla-Selberg, Weyl, and Siegel mass", a lower bound on the divisibility of the m-fold lift,
  a seesaw that makes the period of the iterated lift a Bessel period, the Bost slope inequality,
  and the "approximate orthogonality of the columns of the integral structure".
- Entry 17 speaks of classes in H¹(𝒪_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) and "a significant weakening of
  Vandiver".

The author writes that Claude provided the timeline, that parts of it paraphrase a summary
"which might make zero sense", and that he presents the argument "before having mastered a
massive neighbourhood around its mathematics". A section below names an entry where the Lean
text matches it by a formula or by its names.

## From the five theorems to one statement

[`Statements.lean`](../../src/Statements.lean) states the five propositions.

- `LFunction_ne_zero_of_half_lt_re` says that the value of a Dirichlet L-function of Mathlib is
  not zero at any s with real part above 1/2, except for a trivial character at s = 1.
- `riemannHypothesis` is Mathlib's proposition `RiemannHypothesis`, and `riemannZeta_eq_zero_re`
  says that every zero of the zeta function other than the trivial zeros has real part 1/2.
- `LFunction_eq_zero_re` says that every zero of a Dirichlet L-function with real part between
  0 and 1 has real part 1/2, and `LFunction_eq_zero_re_of_isPrimitive` says the same for
  primitive characters.

`riemannHypothesis` applies `Claim.zeta` to the first theorem, and `LFunction_eq_zero_re` applies
`Claim.strip` to it. The two remaining theorems are restatements of these two. `Claim.zeta` rests
on 9 declarations of the project and `Claim.strip` on 7, and whatever else the two proofs use is
Mathlib's. This session did not read them. [`NOTES.md`](../NOTES.md) describes the step as the standard argument with the functional
equation, which moves a zero with real part below 1/2 to one above it.

The proof of the first theorem is the theorem `everyCharacter` of
[`MainConclusion.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean).
The calls below it run as follows. This session read the proofs of rows 1, 2, 5 and 6 in full,
and the wiring reading read those of rows 3 and 4 in full.

| Row | Theorem | What its proof does | Rests on |
|---:|---|---|---:|
| 1 | `everyCharacter` | applies `everyCharacter_of_row` to `galoisLocalGlobalStrong_recParameter`, which proves `Row` | 800,327 |
| 2 | `everyCharacter_of_row` | passes `Row` and `vwin_of_row` to `every_character_of_literature_of_vWin` | 743,776 |
| 3 | `every_character_of_literature_of_vWin` | supplies seven premises of the next theorem | 670,733 |
| 4 | `every_character_of_theta_integrals_local_matching` | calls the next theorem with `Green`, `VWin` and a record | 478,597 |
| 5 | `every_character_of_green_v_win` | applies `imprimitive` to `zero_free_all_of_green_v_win` | 54,878 |
| 6 | `zero_free_all_of_green_v_win` | concludes zero-freeness for primitive characters | 54,874 |

The first four lines of [`OUTLINE.txt`](../skeleton/OUTLINE.txt) are the theorems of rows 1 to
4, and its fifth line is `nonempty_hyps_definite_side_of_closed_bound`, which builds the record.

Rows 5 and 6 are the passage from three inputs to the statement, and that passage rests on about
55,000 declarations. The other 745,000 declarations behind `everyCharacter` supply the inputs.

| Input of row 5 | Supplied by | Rests on |
|---|---|---:|
| `Green`, a parametrisation of characters of finite general linear groups | `green_of_regular`, which takes a statement on regular characters as a premise | 64 |
| `VWin`, a bound on lengths in Galois cohomology | `vwin_of_row`, which takes `Row` as a premise | 173,628 |
| a record of type `HypsAlt` with the condition `DefiniteSideCondition` | `nonempty_hyps_definite_side_of_closed_bound` | 463,949 |

`Row`, the existence of Galois representations, enters one level higher. Its proof
`galoisLocalGlobalStrong_recParameter` rests on 195,170 declarations. The numbers 173,628,
463,949 and 195,170 add up to more than the 800,327 behind `everyCharacter`, so the branches
share declarations.

## From a bound on intervals to zero-freeness

### What `zero_free_all_of_green_v_win` states and how it splits

The theorem in
[`TopPlug.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean)
takes `Green`, `VWin` and the existence of one record of type `HypsAlt`. It concludes
`ZeroFreeAll`, which unfolds into Mathlib terms. For every primitive Dirichlet character ψ and
every s with real part above 1/2, `DirichletCharacter.LFunction ψ.χ s ≠ 0`. The theorem
`imprimitive`, which rests on 7 declarations, extends the conclusion to all characters through
the Euler factors.

The proof is one line. It calls `zeroFreeAll_of_topG`, which rests on 791 declarations and
contains the first two rows of the next table, and it passes the last two rows to it as
supplies. This session read the proofs of all four rows in full, without the theorems that they
call.

| Part | Theorem | What it gives | Rests on |
|---|---|---|---:|
| Landau step | `formB` | an upper bound for a prime sum on intervals gives zero-freeness | 108 |
| Main inequality | `level_gm_le_on_family_scales` | a tied family gives that upper bound with exponent 1/2 + cε | 546 |
| Supply of tied families | `shape_closed_link_n_of_green` | the record and `Green` give a tied family for every small ε | 51,775 |
| Supply of fields | `supplyChi` | `VWin` gives the hosts that the families live on | 3,488 |

A tied family is a family that satisfies the code's condition `ChainTied`, which the section on
the wanted characters describes. The structure `ChainTie` of the section on the chain is a
different object. This document calls `shape_closed_link_n_of_green` the shape theorem.

### The prime sum

The definitions are in
[`Analytic.lean`](../../src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean)
and
[`ExplicitFormulaErrorOfHostConditions.lean`](../../src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean).
Write Λ(n) for the von Mangoldt function and γ for Euler's constant.

- `Sz x` is the sum of Λ(n)·(x/n − 1) over n ≤ x.
- `Gz x` is `Sz x` − x log x + (1 + γ)x.
- `gChi χ y` for a nontrivial character χ is the sum of Λ(n)·χ(n)·(y/n − 1) over n ≤ y, plus y
  times the logarithmic derivative of L(χ, s) at s = 1. For a trivial character it equals
  `Gz y`.
- A level holds a finite set `KEPT` of primitive characters, which contains the trivial
  character, and a natural number `o`. The sum `Gm y` of the level is `Gz y` plus the real parts
  of `gChi ψ y` over the nontrivial ψ in `KEPT`, each with a positive weight. The weight is
  1/(3·`o` + 1), except for one optional character `psK` whose weight is 1.

### The Landau step

`formB` states the step for every level. Let 0 < θ < 1 and la > 1. Suppose that for every bound
there is a Y above it such that `Gm x ≤ x^θ` holds for all x between Y and Y^la. Then the
L-function of every character of `KEPT`, the zeta function among them, has no zero with real
part above θ. The condition asks only for an upper bound, and only on such intervals. The proof
of `zero_free_all_of_green_v_win` uses la = 3/2.

`formB` reduces to `zeroFree_of_rpow_window`, which rests on 86 declarations. The Landau reading
read that proof, and this session read in full the lemma `landau_tails` that the reading had
read by statement. The account below has four stages and follows the report, except for stage 3.

1. Put g(u) = `Gm`(e^u). Its Laplace transform Φ(s), the integral of g(u)·e^(−su) over u > 0,
   exists for real part above 2. Φ continues to real part above 0 with a simple pole at every
   zero of one of the L-functions. The residue at a zero ρ is −S/(ρ(ρ − 1)), where S adds the
   weights of the characters whose L-function vanishes at ρ, each times a multiplicity. The
   weights are positive, so S is positive and the pole stays when two characters share a zero.
2. For σ > 2 and a real τ, the Taylor coefficient of order k of Φ at σ + iτ is (−1)^k times the
   integral of g(u)·u^k·e^(−(σ + iτ)u)/k! over u > 0. The interval of x from Y to Y^la is the
   interval from U to (1 + δ)U in the variable u, with U = log Y and δ = la − 1. On it the bound
   on `Gm` gives |g| + g ≤ 2R with R = e^(θu). The integral of R·e^(−θu) over the interval is
   δ·U, which is below e^(ηU) for every η > 0 and large U, and the weight
   u^k·e^(−(σ − θ)u)/k! is at most (σ − θ)^(−k). Together these bound the part of the integral
   on the interval by a multiple of e^(ηU)/(σ − θ)^k, for the sum of two quantities. One is the
   norm of the integral at σ + iτ and the other is the integral at σ itself.
3. `landau_tails` handles the part of the integral outside the interval. It picks σ from δ alone
   and the order k = ⌈(1 + δ/2)·σ·U⌉. The weight u^k·e^((2 − σ)u)/k! then has its peak inside the
   interval, and the lemma bounds its integral outside the interval by C/σ^k with a constant C
   that is the same for every U. On each side of the interval the proof multiplies the weight by
   an exponential factor that is at least 1 there and integrates over all u > 0.
4. Suppose a zero has real part above θ. Stages 2 and 3 bound the sum of the norm at σ + iτ and
   the integral at σ by a multiple of e^(ηU)/(σ − θ)^k. The proof splits into two cases. In the
   first a zero ρ at height τ is the singularity nearest to σ + iτ, at a distance d below σ − θ,
   and the integral at σ + iτ has norm about c/d^k. By the report a disc around σ with a radius
   e above d holds no singularity in this case, and a Cauchy estimate keeps the integral at σ
   above −M/e^k. In the second case the nearest singularity of σ is a real zero at a distance d
   below σ − θ, and its positive residue makes the integral at σ about c/d^k, while the norm at
   σ + iτ is at least 0. In both cases c/d^k is at most M/e^k plus a multiple of
   e^(ηU)/(σ − θ)^k, with d below e and e at most σ − θ. The order k grows in proportion to U, so
   for a small η the left side outgrows the right side, and the two contradict each other for
   large U.

The hypothesis enters once for each large U, so one interval for each Y of an unbounded sequence
suffices. By the report the proof uses Mathlib's analytic continuation of the L-functions and
their nonvanishing for real part at least 1, and no functional equation. The lemmas
`landau_pole_asym`, `landau_cauchy`, `landau_nearest` and `landau_finite`, which carry stage 4,
were read by statement.

## The wanted characters inside an auxiliary field

`core_gm` in
[`CoreGm.lean`](../../src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean) proves
the main inequality at one point x, and `level_gm_le_on_family_scales` applies it on the
intervals. `core_gm` rests on 440 declarations, and this session read its statement and its
proof. For a level and all large x it takes a host and two conditions on the host. The
conclusion is `Gm x ≤ x^(1/2 + (eD + eL + 7)·ε)`, where `eD` and `eL` are two constants of the
conditions.

- The condition `CoreAtH` is an existence statement with 23 witnesses and sixteen conditions.
  It says that a record `Data` of real numbers exists over the host with the condition
  `SizeData₂` of the next section and fifteen further conditions. `ChainTied` is the form of the
  same statement for a family, with four further conditions that tie the numbers of the record
  to the data of the family, and `tiedCore_of_chainTied` passes from it to the form for a host.
- The condition `EAtH` concerns the characters. Its field `kept` places the characters of the
  level among the characters of the host. Its field `bdG` asks that every other character of
  the host, taken as a primitive Dirichlet character χ, satisfies `‖gChi χ x‖ ≤ x^(1/2 + ε)` at
  the same point x.

The field `bdG` is a bound of square-root size for the other characters, so its source matters.
`cone.py --users` lists `sigA_le` as the one constant that mentions the field. That theorem,
which rests on 108 declarations and was read by statement, bounds the sum `SigA` of the other
characters by 4·`o`·x^(1/2 + ε).

`cone.py --users` also lists one theorem that mentions the constructor of the record `EAtH`,
which is `supplyOfAdmOf` in
[`supplyOfAdmOf.lean`](../../src/Development/AutomorphicArithmetic/ShortNorms/supplyOfAdmOf.lean).
It rests on 1,964 declarations, `supplyChi` reaches it, and this session read its proof in full.
The proof fills `bdG` from the theorem `boundedTw`, and `boundedTw` reads it off the condition
`PairGood` in
[`PairGood.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean).

- The host depends on two primes q and d. The condition `WinPair` fixes them for a parameter Y.
  The logarithm of q lies between Y^(ε/5)/2 and Y^(ε/5), the logarithm of d lies between
  Y^(ε/5)·(log Y)²/2 and Y^(ε/5)·(log Y)², q divides d + 1, and every odd prime up to Y^(ε/5)
  divides d + 1.
- The other characters are the characters of a modulus M that the level fixes, multiplied by
  the quadratic characters of q and d, with at least one of the two present. The field `bounds`
  of `PairGood` says that each of them satisfies `‖gChi χ y‖ ≤ y^(1/2 + ε/2)` for every y
  between Y and Y^A, for an exponent A ≥ 1 that the caller chooses.
- `pairEx` proves that such a pair exists for every large Y, and it rests on 1,271 declarations.
  It takes the pair from `pair_exists`, which takes it from `pair_share`. That theorem states
  that both ranges hold primes, that all but a share η of the primes q in the first range meet a
  condition `GoodQ`, and that for each such q all but a share η of the primes d in the second
  range meet a condition `GoodD`. `pair_exists` applies it with η = 1/2.

This session read the statements of `pair_share`, `pairEx` and `PairGood` and the proofs of
`boundedTw`, `pairEx` and `pair_exists`. The proof of `pair_share` lies in the folder
[`MeanSquareBounds`](../../src/Development/AutomorphicArithmetic/MeanSquareBounds) and is unread.
For each fixed exponent B the primes q and d exceed Y^B once Y is large, since the logarithm of q
is at least Y^(ε/5)/2, while y stays below Y^A. The bound therefore concerns short sums of
characters with a very large modulus. That observation follows from the ranges above and is this
session's own.

A third condition, `ThinScales`, is one of the sixteen conditions of `CoreAtH`. It concerns the
sums at arguments far above x. The statement `PropTwoSixThinScales` writes it as
`‖gChi χ y‖ ≤ y·exp(−c·x^(ε/8))` for y at least exp(x^(ε/3))/3. The code derives it from three
statements that it bundles as `LitThin` and that `litThin` in
[`LitThin.lean`](../../src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LitThin.lean)
proves. They are a zero-density bound near real part 1, the classical zero-free region with one
possible exceptional real zero, and a truncated explicit formula. `litThin` rests on 319
declarations. This session read the three statements, and it read neither their proofs nor the
derivation of `ThinScales` from them.

## From the two bounds on the slope to the exponent 1/2

Two theorems carry the main inequality. This session read both proofs in full, without all the
lemmas that they call. Neither proof contains a theta lift or a lattice. The lifts appear as m
copies of one term and as real numbers in a record.

### `ch_core`

`ch_core` in
[`ChCore.lean`](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean)
rests on 177 declarations. It works with the characters of a finite abelian group `E0 × H` that
stands for the Galois group of the host. `ASK` is a sum of log p terms over primes that are
inert in a subfield, and `MAIN` is its expected size, of the order a·log a. Here a is a number
`a t` for each element t of a finite set `TT`, and a condition `SizesA` keeps every `a t / b`
within 1 of x, for a scale b of the record. The theorem assumes the bound that `ch_top` proves
for `ASK − MAIN`, summed over `TT` and over the m lifts. It concludes the bound for the weighted
prime sum of the kept characters.

| Row | Lemma | What it does | Rests on |
|---:|---|---|---:|
| 1 | `ch_balance` | proves the exact identity `ASK − MAIN = De` by orthogonality of characters | 67 |
| 2 | `th_le` | moves every prime sum inside `De` to one common argument | 55 |
| 3 | `core` | sums over a subgroup `A0`, which removes every character that is nontrivial on it | 134 |
| 4 | `one_char` | replaces the sum over `TT` by the value at x | 16 |
| 5 | `proposition_size_bound` | divides by the size of the sum and reads off the exponent | 9 |

This session read the lemmas of rows 2 to 4 in full and those of rows 1 and 5 by statement.
`De` is an average of twisted von Mangoldt sums over the characters of `E0 × H`, so row 1 is
finite Fourier inversion between primes in classes and character sums. The summand of row 3
does not depend on the lift index j, so the sum over the m lifts multiplies it by m. Row 4 uses
a premise on the set `TT`. The sum of a nontrivial kept character over `TT` differs from its
expected value by at most a constant times x^(−1 + ε) times the size of `TT`.

Row 5 divides the error by `nT * m * b`, where `nT` is the size of `TT`. By this session's own
check of the arithmetic two terms survive. One is about x/m, and the premise x^(1/2 − ε) ≤ m
keeps it below x^(1/2 + ε). The other is m times a factor of at most x^(9ε/8), and the premise
m ≤ x^(1/2 + ε/2) keeps it below x^(1/2 + 13ε/8), the exponent that appears in the proof. Without
the factors x^(cε) the two terms are x/m and m, which are equal at m = √x, the chain length that
the note gives. This session did not record which terms of the bound of `ch_top` give x/m and
which give m. `core_gm` calls `ch_core` with the constant C = `eD` + `eL` + 3, for which
`ch_core` gives the exponent 1/2 + (C + 3)·ε, and its own conclusion has one ε more.

### `ch_top`

`ch_top` in
[`ChTop.lean`](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean)
proves the assumption of `ch_core`. It bounds `ASK − MAIN`, summed over `TT` and the lifts, by
an explicit expression that the code calls `errorBracketSizeWindows`. It rests on 90
declarations. Its premise `SizeData₂`, defined in
[`SChain.lean`](../../src/Formalism/SizeWindowBrackets/SChain.lean), is a conjunction of eleven
conditions on a record `Data` of 39 real numbers and real-valued functions from
[`MeanBoundSecondForm.lean`](../../src/Formalism/RankGapBounds/MeanBoundSecondForm.lean). The
record has an index u that runs over a finite set, an index t that runs over a set in bijection
with `TT`, and a field `aT t` that equals the `a t` of `ch_core`. Its number `Main` stands for
the sum of `MAIN` over `TT` and the lifts. The code writes `ph y` for y log y − y. Two of the eleven
conditions hold the idea.

- `DIV` bounds a number `muCC` from above. For every u it says that `muCC + h u − Fo` is at most
  the sum over t of `m * (ph (aT t) − aT t * logOm) − aT t * log (T u)`, plus error terms. Here
  `Fo` and `T u` are further numbers of the record, and `logOm` is a constant that the section
  on one lift describes. Among the eleven conditions this is the one in which the number m of
  lifts multiplies the main term.
- `SlopeIneq` bounds `muCC` from below. It says that a weighted mean over u of `muN u − h u`,
  minus the logarithm of the number of indices u and further correction terms, is at most
  `muCC`.

The mean of `DIV` over u, taken with the weights of `SlopeIneq`, and `SlopeIneq` together cancel
`muCC` and the mean of `h` and leave an upper bound for the mean of `muN`. The conditions `QuotientSlopeBoundsWith` and `LossBounds`
bound `ASK` from above through a quantity `Ga`, and `Ga` through the mean of `muN`, so
`ASK ≤ Main` plus errors follows. The theorem `each_unit_bound_statement`, which rests on 58
declarations, states this deduction, and this session checked by hand that the leftover terms add
up to `Main`. The reading of six proofs read the proof `Ga_bound5` behind it in full and found
the same cancellation of `muCC`. The rest of `ch_top` shows that the errors fit inside the
bound. It calls `core_ineq`, an inequality between real numbers whose proof has about 10,000
characters, of which the reading of six proofs read the beginning.

## The upper bound for the lattices of a datum

### What the numbers of the record are

The eleven conditions speak about real numbers without saying what they measure. The condition
`TieLocal` in
[`TieGlobal.lean`](../../src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean) says
it, for a datum `D` of a family. The index u of the record runs over the words of the datum.

- `muCC` is the slope of the dual of a Hermitian lattice `div.RR` of the datum.
- `muN u` is the slope of a lattice `div.Nu u`, one for each word.
- `h u` is the height of a linear map `div.Bk u` from `Nu u` into the dual of `RR`.
- The set of lifts is `Finset.Icc 1 D.R.m`, so m is a field of the datum.

The slope inequality of step 5 is therefore about the maps `Bk u` of the words into one lattice,
and the number m of lifts enters through the height of each map.

### The path of the divisibility inequality

For the lattices of a datum the inequality says that the dual slope of `RR` plus `h u` minus
`Fo` is at most a main term plus error terms, and the main term contains m times a sum of
`ph (aT t)` over `TT`. The proof passes through
[`RecBridge.lean`](../../src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean) and its
neighbours in the folder [`Divisibility`](../../src/Formalism/LocalToGlobal/Divisibility).

| Theorem | What it does | Rests on | Read |
|---|---|---:|---|
| `linkDIVt_of_bridge_kernel` | gives the inequality for every datum of a family | 2,662 | statement |
| `wordFacts_of_face` | moves it from coordinates to the lattices of the datum | 157 | in full |
| `divClausesR_of` | derives it from a record of inputs, `DivInputsR` | 814 | in full |
| `IndefSide.boundsMu` | bounds the dual slope of `RR` from above | 111 | in full, by the reading of six proofs |
| `height_chain_atR` | bounds the height of a product of maps by the sum of the heights | 87 | in full, by the reading of six proofs |
| `RecNums.divIneq` | adds the slope bound and the height bound | 34 | in full |
| `rhs_le_record` | shows that the sum stays below the main term plus errors | 206 | in full |

This session read the rows that are marked in full without a named reading. Three sums run over
a set J of lifts, and the record `RecNums` in
[`Inputs.lean`](../../src/Formalism/LocalToGlobal/Divisibility/Inputs.lean) fixes the size of J
as m.

- The first sum is in the height. The number `hu` of the record, which stands for `h u`, is `hA`
  plus the sum over j of `hB j − hX j`. The fact `weight_height_sum_le` of the record bounds the
  part of each such term at an element t of `TT` by `ph (aT t)`. Each lift contributes the same
  main term, and m lifts give m times that term.
- The second sum is in the slope. `boundsMu` bounds the dual slope of `RR` by a sum over the
  lifts of numbers `l3 j` and further sums. By the reading of six proofs it uses five
  propositions, a slope bound `slope_bounds`, a determinant formula, a Gram identity for a
  quotient metric, a gluing of local lattices and a bound at ramified places. The numbers `l3`,
  `F0` and `E1` are fields of a record, bounded by further fields of the same record.
- The third sum is in the chain. By the same reading `height_chain_atR` is submultiplicativity
  of the operator norm at each place, written in logarithms, with the matrices of the chain
  grouped by their lift.

The theorem of the first row derives the link `LinkDIV` from two premises, `LinkEta` and
`DIVinN`. `divinN_of_hypV`, which rests on 72 declarations, gets `DIVinN` from the bound of
`VWin` over the host. This is where entry 17 of the note enters the divisibility. The form of
`LinkDIV` at one datum, `LinkDIV_at`, also includes `BesselId`, which says that a pairing `Bu`
of the datum equals a nonzero constant times a pairing `besS` after two isometries. The names
match the Bessel period of entry 12.

## The chain of lifts

The chain is a concrete object in the code. A record `ColChain` holds matrices `Kj` between
spaces with metrics, a field `fact` says that the pairing of the datum factors through their
product, and a field `lf` places each lift on a matrix.

- The structure `ChainTie` in
  [`DivisionHeightBoundStatement.lean`](../../src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean)
  links a `ColChain` to a chain of kernels. Its field `kerF` says that the matrix `Kj j`, read
  in coordinates, is the kernel operator number j. Its field `metF` says that the metric of a
  space is the inner product on the forms of that space.
- `chainOf` builds the `ColChain` from a chain of kernels by choosing bases. It rests on 54
  declarations.
- [`FiniteSumNonzeroLargeDepth.lean`](../../src/Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean)
  defines the family `chF u j` of spaces for a word u and a number j. Its group is `UF E (N j)`
  times two further groups. `UF E n` is the isometry group of the standard Hermitian form on
  Eⁿ, the sum of `star (x i) * y i`, so it is a unitary group.
- The rank is `N j = k + j * (t + 1)` for natural numbers k and t of the datum, so the rank
  grows by t + 1 from each j to the next. Entry 8 of the note writes a lift as π ↦ π ⊞ μ_j[t].
  That the letter t of the note is this t is an interpretation.
- The condition `ChIdx.Ok` requires `R.m = m2 + 2` for a natural number `m2`, so m is at least
  2. The chain has m − 1 matrices and a final pairing, and its ranks run from `N 0` to `N m`.
- The record `ChTh` holds one distribution of type `ThDist` for each of the m − 1 matrices and
  one more for the final pairing into rank `N m`, which makes m in all. `ThDist.Ok` requires
  equivariance under both unitary groups. `XiEntry` writes a kernel entry as a product of local
  functions over primes.

This session read these definitions and the statement of `rowsU_of_colPins_alt`, which proves
that a datum with its ties has a `ColChain` with a `ChainTie`. That theorem rests on 14,837
declarations, and `link_brest_alt`, which carries it into the shape theorem, rests on 27,645.
The name `ThDist`, a condition named `WeilTied` on the additive characters and the folder name
Theta Pair Lifts say theta and Weil. That the definitions fit a theta kernel for a pair of
unitary groups is this session's interpretation.

The reading of the chain followed the premises of `rowsU_of_colPins_alt`.

- The kernel of the chain is defined from the distributions. The code sets `matK` to
  `kerOf (T.th i)` applied to `XiEntry`, so the kernel number i is the kernel of the
  distribution number i by definition. The statement `KerEquivC`, which the theorem `kerEquivC`
  proves, adds equivariance.
- That each lift is a theta lift is the content of a condition `ThHyp` with companions
  `AnaStep` and `FamilyLaws`. The reading did not trace them for the data of a family.
- The numbers of the heights come from a record `HtNums`, which by the reading is built in one
  theorem from two halves. The half for the kernels is proved by `kerSide_chainS`, which rests
  on 12,981 declarations and uses a theorem named `meanLogPeriod_chowlaSelberg`. The half for the
  final pairing is a statement `LastSide`, which the reading did not open.
- The lattice `Nu u` is defined through a field `nprimeDef` of the family, whose construction
  the reading did not trace.
- The valuation condition `val2` of the inputs is a theorem. It follows from `val2AllAtR`,
  which rests on 269 declarations, and from a condition `adm2`, which says that every period
  value is zero or has at least a prescribed valuation. This session found the supply of `adm2`
  in the proof of the shape theorem, where `closed_family_admissible_twist_link_alt`, resting on
  5,172 declarations, derives it from fields of the record.
- `BesselId` is proved by `besselId_of_joins` from join data that the field `selJ` of the record
  feeds. The reading did not follow `selJ` further.

## The bound for one lift

[`Numbers.lean`](../../src/Formalism/LocalToGlobal/Divisibility/Numbers.lean) defines the
numbers of a lift from one record for each place, `HCParam`. A top place is a place in the set
`TT`. This session read the definitions and the statement of each theorem of this section.

- A place carries k numbers `u`, k − 1 numbers `v` and m numbers `e`. The fields `u_gt_v` and
  `v_gt_u` say that the numbers u and v interlace, so u₀ > v₀ > u₁ > … > u_{k−1}. These letters
  u and v are unrelated to the words u and to the v of the bullet on `kerPlace`.
- The top weight `aT t` at a top place t is `u 0` − (k − 1)/2. The code uses the letter t both
  for a top place and for the number t of the rank `N j`, and the two are unrelated.
- The weights `nu` of lift j have one entry for each index below `N (j − 1)`. The first k
  entries come from the numbers u. The rest come in blocks of t + 1 consecutive values, one
  block for each earlier lift, centred at minus the number `e` of that lift.
- `kerPlace` is the sum of `ph` over the weights minus the sum of the weights times `logOm`.
  Here `logOm` is γ + log(π/v) minus the logarithmic derivative at 1 of the L-function of a
  quadratic character, with a positive number v of the record `Data`.
- `logHook` is the logarithm of the hook product of a Young diagram whose rows are built from
  the numbers v of the place.
- The height `hU` adds `kerPlace` and subtracts `logHook`, summed over places and over the m
  lifts.

`stepE_num` in
[`NumbersLink.lean`](../../src/Formalism/LocalToGlobal/Divisibility/NumbersLink.lean) proves two
facts for every lift j and place ρ, and it rests on 160 declarations. The sum of `ph` over the
weights minus `logHook` is at most `ph (aT ρ)` at a top place and at most 0 elsewhere, up to an
error term. The sum of the weights is `aT ρ` + k·w at a top place, up to a bounded error, where
w is a shift that all rows of the lift share at that place. Two statements
about rows of natural numbers carry it.

- `young_diagram_hook`, which rests on 5 declarations, says that for every Young diagram the
  sum of the logarithms of the factorials of the row lengths is at most the logarithm of the
  hook product. This session read its proof. The hook of a cell is at least as long as the part
  of its row from the cell to the end, and the product of those lengths along a row of length L
  is L!.
- `young_diagram_step_origin`, which rests on 55 declarations, takes k rows built from the
  numbers u and k − 1 rows built from the numbers v, with the interlacing as a premise, and
  concludes the two facts. The reading of six proofs read its proof in full. The proof pairs
  each of the k − 1 lower rows of the lift with a row under the hook product, bounds the
  difference of each pair through the interlacing, and leaves the top row, of length `aT` plus
  w, without a partner. By the reading the weights of the blocks are bounded separately and go
  into the error term. The error term of the statement grows with w, and this document does not
  record how the proof moves the shift w of the top row into it.

The unmatched top row gives one `ph (aT t)` for each lift, and the sum of the weights gives one
`aT t * logOm`. The main term is m times their difference, summed over `TT`. The multiplicity of
the note is, in this code, the number of lifts.

`numFacts_rec`, which rests on 266 declarations, proves the premises of `stepE_num` for the data
of a family from size conditions and a choice of parameters. Three interpretations in this
section are guesses from the names and the note. They are `logOm` as the Chowla-Selberg period
and the hook product as the Weyl dimension formula, both of entry 9, and the interlacing as the
interlacing weights of entry 7.

## The lower bound for the lattices of a datum

`Frame_at` in
[`QuadraticLogDerivCongr.lean`](../../src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean)
is the slope inequality for the lattices of a datum. This session read the statements of this
section and, of the proofs, that of `frame_at_of`.

| Theorem | What it does | Rests on |
|---|---|---:|
| `frame_at_of` | derives `Frame_at` from a general statement about several maps into one lattice | 441 |
| `joint_a_ramified_holds` | proves that general statement | 400 |
| `blockReal_at_of` | takes the blocks of the maps from `BesselId` | 59 |
| `matKF_of` | builds the matrices of the maps for a family | 178 |
| `data_SlopeIneq` | turns `Frame_at` into the condition `SlopeIneq` of the record `Data` | 137 |
| `link_alt_alt_bis` | supplies the link `LinkS` | 11,188 |

Of the 400 declarations behind `joint_a_ramified_holds`, 190 lie in the folder
[`HarderNarasimhan`](../../src/Formalism/HarderNarasimhan) and 74 in the folder LatticeSlopes.
[`Statement.lean`](../../src/Formalism/HarderNarasimhan/Statement.lean) states a slope inequality
for a map of bounded norm between lattices.

The general statement needs bounds on the Gram matrix of the maps, and the link `LinkS` supplies
them in the following form, for numbers `duS u`, `Dstar` and `Dall` of the datum whose names
suggest ranks.

- For two different words u and u′ a number `hsSq u u′` is at most
  (1 + η0)·`duS u`·`duS u′`/`Dstar`.
- For every word u a number `hsDiagFull u` is at most e0·`duS u`.
- `Dall` is at most (1 + η1)·`Dstar`.

The link gives η0, η1 and e0 below exp(−x^(ε/8)). The names `hsSq` and `hsDiagFull` suggest the
squared Hilbert-Schmidt norm of a block of two maps and the distance of the block of one map
from the identity. Under that interpretation each map is an isometry up to a small relative
error. The bound for two different maps is the value that two subspaces of ranks `duS u` and
`duS u′` in general position inside a space of rank `Dstar` have, up to the factor 1 + η0, and
it is not a bound near zero. The note's entry 16 calls its statement the approximate
orthogonality of the columns, and entry 13 names the Bost slope inequality.

## How the conditions are assembled

The reading of the links read `linkCore` in
[`LossesSmallShares.lean`](../../src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean)
in full. It rests on 373 declarations and builds every witness of `ChainTied` from a family. The
number m is the field `R.m` of the datum. A further witness, which the code calls θ and which
is unrelated to the θ of the Landau step, enters `ThinScales` and is exp(−c6·x^(ε/8)) for a
constant c6. The reading found every witness constructed and none left free. The table gives the source of each part of `SizeData₂` as the
reading reports it. The report names no source for the eleventh part, `HidaSetting`, which is a
list of sign conditions.

| Part | Comes from |
|---|---|
| `DIV`, `EComp5`, `HComp` | the link `LinkDIV` |
| `Count5` | `PartFiveFamilyBounds` |
| `Slopes` | two conditions on the slopes of the family |
| `QuotientSlopeBoundsWith` | the links `LinkG` and `LinkMu` |
| `LossBounds` | `stLoss7` and a condition on weights |
| `SlopeIneq` | `frameF_of`, the form of `frame_at_of` for a family, with `LinkDIV`, `LinkIRR` and `LinkS` |
| `HHBound` | `LinkDIV` |
| `FParams` | the link `LinkIRR` |

`topDesWin`, which rests on 724 declarations and whose proof this session read, takes the links
as premises, and the proof of the shape theorem supplies them by these theorems.

| Link | What it states, by the reading | Supplied by | Rests on |
|---|---|---|---:|
| `LinkG` | local length bounds and a bound on von Mangoldt sums | `closed_linkG_of_duty` | 19,922 |
| `LinkS` | the bounds of the section on the lower bound | `link_alt_alt_bis` | 11,188 |
| `LinkEta` | a covering condition on places | `closed_linkEta_of_duty` | 1,008 |
| `LinkIRR` | 0 ≤ `delp` ≤ exp(−x^(c/7)) for a number `delp` of the datum and a constant c | `closed_linkIRR_of_join_count` | 1,840 |
| `LinkDIV` | the divisibility inequality | `closed_linkDIVt_of_closed_bridge_kernel` | 2,704 |
| `LinkMu` | a bound on the difference of two slopes | `linkMu_of_linkDIV`, from `LinkDIV` | 219 |
| `LinkGLOBAL` | the passage from the links to `ChainTied` | `link_gl`, which reaches `linkCore` | 15,442 |

The proof of the shape theorem passes `Green` to one call, the supplier of `LinkIRR`. By the
reading `Green` is Green's parametrisation of the cuspidal characters of GL_d over a prime field.
`green_of_regular`, of whose proof the wiring reading read about two thirds, derives it from a
statement about regular characters that `greenCuspidalCharsByRegularChars_proof` proves, resting
on 1,170 declarations.

The shape theorem takes `Green` and 53 further hypotheses, which
[`TopShapeAlt.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShapeAlt.lean)
lists. The theorem `goal_of_shape_of_hyps` in
[`ShapeOf.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean)
fills the 53 from the 46 fields of the record. It passes 45 fields to one hypothesis each, three
of them through a conversion, and derives six hypotheses from the remaining field, a selection
σ. The other two hypotheses, `hVC`
and `nR`, are the proposition `True` in this use, and `zero_free_all_of_green_v_win` fills them
with `trivial`.

## The supply branches

### `VWin`, the bound on lengths

The reading of `VWin` read the statement in
[`ExistsPageN.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean).

- For a number field E, a prime l and a twist e, `shaLen` is the length over ℤ_l of a group of
  classes. The classes lie in the first continuous cohomology of the Galois group of the maximal
  extension of E unramified outside l, with coefficients ℚ_l/ℤ_l twisted by the power −e of the
  cyclotomic character, and they vanish at every place above l. The formula suggests the group
  of entry 17 of the note, with the added condition at the places above l.
- `VWin` concerns the subfields E of cyclotomic fields that a primitive character ψ, the two
  primes q and d and an exponent cut out. It says that the lengths are finite for every prime l
  and every twist e below x^401. It also says that for every finite set of primes the sum of
  log l times the lengths, over the primes l of the set and the twists e below x^401, is at most
  √exp(x^ε).
- The reading found two uses of the bound. `supplyOfAdmOf` uses it to declare a host good, and
  `divinN_of_hypV` uses it to absorb a term of the divisibility inequality.

For each fixed exponent B the allowed bound exp(x^ε/2) exceeds x^B once x is large. That
estimate is this session's own and follows from the formula alone.

The proof runs through these theorems, each read at its top.

| Theorem | Rests on |
|---|---:|
| `vwin_of_row` | 173,628 |
| `automorphic_window_of_inputs` | 173,460 |
| `v_window_of_depth_zero_residual_bc_cm` | 150,837 |
| `v_window_of_automorphy_csd_ss_mono_odd` | 132,516 |
| `vwin_of_hypotheses_H_E_alt` | 128,455 |

By the reading the last theorem combines a project theorem `ferreroWashington`, which rests on
5,560 declarations and bounds indices of class groups in a cyclotomic tower, with bounds of the
form (l·n·e)^C on lengths, for a number n of the host, in five cases named `CountI`, `CountII`,
`CountIII`, `CountV` and `CountZ`. The supplier of the first case,
`count_i_of_printed_bound_k_kato_automorphy`, rests on 101,821 declarations. Statements named
after Poitou and Tate, Greenberg and Wiles, and Bloch and Kato enter as fields of a record, and
each field is filled by a theorem of the project, for example `blochKatoLocal`, which rests on
6,075. The reading read those statements and the one-line proofs that fill the fields, and left
the proofs of the theorems unread.

### `Row`, the Galois representations

The reading of `Row` read the statement in
[`WeightsConjBis.lean`](../../src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean).
`Row` says that for every CM field E, every prime l and every cuspidal automorphic
representation π of GL_n over E that is regular algebraic and polarized, there is a continuous
semisimple representation of the Galois group of E in GL_n over the algebraic closure of ℚ_l
with a condition `PropsB`. The fields of `PropsB` fix the Hodge-Tate weights and compare the
representation with π at the places away from l and above l.

| Theorem | What its proof does | Rests on |
|---|---|---:|
| `galoisLocalGlobalStrong_recParameter` | applies the next theorem to a theta lift existence theorem | 195,170 |
| `galoisRepresentations_of_thetaLift` | combines the lift with a geometric realisation | 169,094 |
| `tLift_holds_k` | proves that lifts to unitary groups of all large ranks exist | 29,973 |
| `geoOne_holds` | proves the geometric realisation | 99,280 |
| `kodaira_spencer_of_weight_one` | supplies six parts of it | 45,942 |

By the reading `geoOne_holds` takes one premise, a Lefschetz fixed-point formula for finite étale
correspondences, and `lefschetz_fixedPoint_finite_etale_correspondence`, which rests on 4,259
declarations, proves it inside the project. The reading counted 77 statements of the namespace
`GlobalTheory.Published` behind `Row`. For 69 of them it found a closed theorem that proves the
statement, and for 8 it found only derivations from other statements, which it did not trace.

`Row` is passed on in two ways. `vwin_of_row` derives `VWin` from it. `everyCharacter_of_row`
puts it into a record `OpenLiteratureStatements`, and three theorems derive from that record
three fields of a bundle of the next section, which state variants of `Row` for unitary groups.

### The record and the two bundles

The wiring reading read
[`EveryCharacterOfLiteratureOfVWin.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean)
and the proofs of rows 3 and 4 of the table of calls below `everyCharacter` and of
`nonempty_hyps_definite_side_of_closed_bound` in full.

- `every_character_of_literature_of_vWin` takes the record `OpenLiteratureStatements` of three
  fields and `VWin`. It supplies the seven premises of row 4 of that table. They are two bundles, two premises
  from `theoremK_head2`, which rests on 25,083 declarations, the covolume bound `hX`, the
  existence of a local map, and `VWin` itself.
- The two bundles have 58 and 49 fields. [`READING.md`](../skeleton/READING.md) reports at least
  28 and 29, because the text it worked from was cut.
- The reading sampled 16 of the 107 fields. Each sampled field is filled by a theorem of the
  project whose statement is the field. Fourteen of those theorems are closed, and two take
  premises that further theorems of the project supply.
- `nonempty_hyps_definite_side_of_closed_bound` builds the record `HypsAlt` with its 46 fields.
  Its last call is `hypotheses_nonempty_of_unramified_exponents_alt`, which rests on 421,135
  declarations. Eight fields are named propositions that closed theorems fill, for example the
  statements on thin scales from `litThin`.
- The condition `DefiniteSideCondition` of the record says that a bundle with the numbers of
  the section on one lift and its ties has the tied chain of the section on the chain, for
  every word.

The conclusion of `nonempty_hyps_definite_side_of_closed_bound` is the existence of a record,
written with `Nonempty`. The proof of `zero_free_all_of_green_v_win` takes a record out of that
existence, and `goal_of_shape_of_hyps` passes every field of it to a hypothesis of the shape
theorem, as the section on the assembly describes.

### The covolume bound

The premise `hX` of `every_character_of_theta_integrals_local_matching` is a covolume bound. By the wiring reading `topCovolSlim2_use_alt_alt`,
which rests on 157,435 declarations, derives it from fifteen premises, and a theorem of the
project fills each of them. The largest are these.

| Premise | Supplied by | Rests on |
|---|---|---:|
| a toroidal compactification statement | `toroidalForFanKS` | 52,864 |
| a toroidal integral of Siegel | `siegelToroidalIntegral_holds` | 52,439 |
| a bigness statement named after Moriwaki | `moriwakiBig_outright` | 24,601 |
| an arithmetic Hilbert-Samuel statement | `hsUse_outright` | 24,600 |
| resolution of singularities in characteristic zero | `resolutionCharZero` | 7,699 |

The descriptions in the first column follow the names. By the reading the bound goes into one
call, where it becomes the entry `covol` of the field `rRows` of the record.

## What a checker should know

The readings looked for premises that hold by construction, for wrappers and for definitions
that are weaker than their names. They found the following.

- `IsRecT`, the notion of a local Langlands map in `Row`, constrains the map on GL₁ and on twists
  of depth-zero representations over the field ℚ_g of g-adic numbers. The definition requires
  the laws `twist`, `central`, `dual`, `inj` and `depth` only for representations whose cuspidal
  support is of that kind. This session confirmed in the definition `cuspEx` of
  [`RecTExists.lean`](../../src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean)
  that every other cuspidal representation is sent to a fixed fallback object of the right
  dimension. The theorem `recTExists`, which rests on 12,598 declarations, proves that such a
  map exists, and the reading of `Row` read its proof except for three steps.
- `AwayB`, the comparison of `Row` at a place away from l, has three clauses. It asks for equal
  dimension, for equality of the two objects in a torsion case, and for equal characteristic
  polynomials in a tame case. This session confirmed the three clauses in the source. The usual
  local-global compatibility asks for an isomorphism at every such place.
- `OpenLiteratureStatements` holds `Row` twice and the existence of a local map once, and
  `everyCharacter_of_row` fills both `Row` fields with the same proof. Of the 194 theorems named
  `…_of_literature` in the file of `every_character_of_literature_of_vWin`, three read a field of
  that record. The others take
  the record and prove their statement without it.
- `OpenImageCondition` is a record whose one field is `Row`, and the theorems named `…_of_open`
  that take it prove their statements without it.
- `llOf_alt` returns its first premise and ignores eleven others. `field_of_starFull_alt`
  ignores one premise.
- One field type of the first bundle, `UnusedSlot72`, is the proposition `True`, and its field
  is filled by `trivial`. The two hypotheses `hVC` and `nR` of the shape theorem are `True` as
  well, as the section on the assembly says. `FamP.Large` contains a conjunct `True`.
- The hypothesis `hθ1` of the Landau step, θ < 1, is passed along and stays unused in the proofs
  that were read.
- Several premises reach their use as fields of a record, for example `StdKer`,
  `RecordCompatibleExtended` and the field `sharp` of `KerTies`. A checker who looks for the use
  of such a premise has to follow the projection of the field. The ties of
  `rowsU_of_colPins_alt` are stated with heterogeneous equalities, which the proof removes by
  substitution.
- Two names mislead. `admissibleClassesTwistedChar` names both a theorem about ranks and an
  unrelated definition. A field of `HtNums` is called `MainNotions`, which is the name of a
  namespace and says nothing about the bound that the field enters.

[`../decl-graph`](../decl-graph/README.md) reports that the five theorems rest on the axioms
`propext`, `Classical.choice` and `Quot.sound` and on no other axiom. This session read that
report and did not repeat its check.

Every premise that a reading followed to its end was supplied by a theorem of the project or by
a field of the record. The next section lists what stayed unread.

## What stays unread

- `Claim.zeta` and `Claim.strip`, which carry the passage to the other four theorems.
- The four lemmas of stage 4 of the Landau argument and six further lemmas of it, which were
  read by statement.
- The proof of `pair_share`, which gives the bound of square-root size for the other characters
  of the host, the proofs of the three statements behind `litThin`, and the derivation of
  `ThinScales` from them.
- The proofs of `ch_balance`, `proposition_size_bound` and `sigA_le`, and most of the proof of
  `core_ineq`.
- The proofs of `linkDIVt_of_bridge_kernel`, of `slope_bounds` and of the four other
  propositions that `boundsMu` uses.
- The proof of `rowsU_of_colPins_alt` below its top, the conditions `ThHyp`, `AnaStep` and
  `FamilyLaws`, which say that each lift is a theta lift, the statement `LastSide`, the field
  `nprimeDef` and the field `selJ` behind `BesselId`.
- The proofs of `stepE_num` and `numFacts_rec`.
- The proofs that carry the lower bound, which are those of `joint_a_ramified_holds`,
  `blockReal_at_of`, `matKF_of`, `data_SlopeIneq` and `link_alt_alt_bis`, and the definitions of
  `hsSq`, `hsDiagFull`, `duS`, `Dstar` and `Dall`.
- The suppliers of the links other than `linkCore`.
- The proofs below the first call in the supply branches, for example `ferreroWashington`,
  `count_i_of_printed_bound_k_kato_automorphy`, `tLift_holds_k` and the fifteen suppliers of the
  covolume bound.
- The eight statements of `GlobalTheory.Published` behind `Row` for which the reading found no
  closed theorem.
- Most of the 463,949 declarations behind the record.
- The definitions of the slope of a lattice and of the height of a map, and whether the
  definitions of the project are the mathematical objects that their names suggest, which is a
  question for a mathematician.

## Scripts and files

```bash
python3 -I verification/strategy/cone.py NAME            # what a constant rests on
python3 -I verification/strategy/cone.py --users NAME    # the constants that mention it
python3 -I verification/strategy/check.py                # checks this document against the graph
```

`cone.py` needs `data/exact_graph.npz` and `data/exact_nodes.tsv.gz` of `../decl-graph`, which
`exact_graph.py` of that folder writes. A count takes about three seconds.

`check.py` reads this document. It takes every piece of code font that has the form of a Lean
name and no file ending, and looks it up among the compiled constants of the project. It
computes again every count of `cones.json` and looks for it in the paragraph or table row that
names its theorem. It tests that every linked file exists. With `--write` it writes the counts
of `cones.json` anew.

| File | Content |
|---|---|
| `cone.py` | counts what a constant rests on, and lists the constants that mention a constant |
| `check.py` | checks the names, the counts and the links of this document |
| `cones.json` | the full name and the count of every theorem whose count this document gives |
