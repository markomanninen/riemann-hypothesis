# The strategy of the proof, followed through the Lean text

The proof in [`src`](../../src) derives the five theorems of [`Main.lean`](../../src/Main.lean)
from one inequality. The first theorem states that a Dirichlet L-function has no zero with real
part above 1/2, and the other four follow from it. The inequality says that a weighted sum over
the prime powers up to x, with its main terms subtracted, is at most x^(1/2 + cε) for all x
between Y and Y^(3/2). This holds for every small ε > 0 and for arbitrarily large Y, with a
constant c that depends on neither ε nor Y. The proof gets the inequality by bounding the slope
of one lattice from two sides. A divisibility inequality bounds that slope, together with a
height term, from above by m times a main term, where m is the number of lifts in a chain
between unitary groups. The author's note calls them theta lifts. A slope inequality bounds the
same slope from below. The two
bounds leave error terms of about x/m and about m for the weighted sum, and the proof assumes
that m lies in a window around √x, where both terms are about √x.

This document follows that route through the Lean text. It goes from `Main.lean` down to the
upper bound for one lift and the lower bound for the maps into the lattice, and then through the
assembly of the conditions and the branches that supply the premises. For each step it names the
theorem that carries the step, says what the theorem states and how much of its proof was read,
and gives the number of declarations that the theorem rests on.

A language model, Claude, read the route in one session on 23 and 24 November 2026. Seven further
runs of the same model each read one branch and reported back. A table below names the seven
readings, and a section names the reading behind a sentence that comes from a report. A sentence
without a named reading reports what this session read. On 24 November two more runs of the same
model compared the nine steps with the Lean text, one for each half of the route, and their
twenty findings are worked in. No mathematician has checked
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
- The slope of a lattice is the code's number `mu`.
  [`Statement.lean`](../../src/Formalism/LatticeSlopes/Statement.lean) defines the covolume
  `covol` of a lattice in a Euclidean space as the square root of the Gram determinant of a
  basis, the degree as minus the logarithm of the covolume, and the slope as the degree divided
  by the rank. The largest slope `muMax` is the supremum of the slopes of the nonzero
  sublattices. The smallest slope `muMin` is the infimum of the slopes of the quotients of the
  lattice by its saturated proper sublattices. For a Hermitian lattice over a number field K the definition `muDef` in
  [`StatementPl.lean`](../../src/Formalism/HarderNarasimhan/StatementPl.lean) sets `mu` to twice
  the slope of the lattice, minus log 2, plus the quotient of log |d_K| by the degree of K over
  the rational numbers, where d_K is the discriminant of K.
- The height of a map is the code's number `htMap` in the file of `muDef`. It is the mean, over
  the infinite places of K, of the logarithm of the squared operator norm of the map. The
  number `h` of a word of a datum is a different number. It is a real field of the datum, the
  condition `WordFacts` requires that the height of the map of the word, when the map is not
  zero, is at most `h`, and in a family a formula named `hExpl6` gives `h`.
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
   sum `Gm x` on the intervals from Y to Y^(3/2), for arbitrarily large Y. The sum has its main
   terms subtracted. The step is a Landau argument.
3. The sum `Gm` is a weighted sum of the prime sums of a finite set of characters, the wanted
   characters. The proof places them among the characters of an auxiliary abelian field, the
   host. A sum over a subgroup removes the characters that are nontrivial on it, and the proof
   bounds the prime sum of each remaining unwanted character separately. The host depends on
   two primes q and d. A count of zeros and a mean square bound show that at least half of the
   candidates for q, and then at least half of the candidates for d, give every such character
   a prime sum of at most y^(1/2 + ε/2) for the y from Y to Y^A, where A ≥ 1 is an exponent
   that the caller chooses. The sections below call the wanted characters kept and the
   unwanted characters that remain the other characters.
4. The sum over all characters of the auxiliary field equals an arithmetic quantity `ASK` minus
   its main term, by finite Fourier inversion.
5. `ASK` is bounded through the slope of a lattice. A divisibility inequality `DIV` bounds the
   slope from above, and a slope inequality `SlopeIneq` bounds it from below.
6. Both bounds concern linear maps into that lattice, one map for each word of a datum. A
   pairing of each word factors through a chain of m kernels between unitary groups of ranks
   k + j(t + 1), for j from 0 to m, where k and t are two natural numbers of the datum. The
   first m − 2 kernels are composed one after the other, the last two are composed inside a
   finite sum, and one more linear map follows. This document does not record how the pairing
   is tied to the map.
7. The main term of the upper bound holds one term a·log a − a − a·`logOm` for each lift and
   each top place, where a is the top weight at that place and `logOm` is a constant of the
   host. For one lift, interlacing weights and a hook product bound a sum over its weights by
   a·log a − a plus an error term.
8. The lower bound applies a general statement about several maps into one lattice. It takes
   two bounds on products of matrices of the maps and one bound on their number of rows, which
   a link supplies for a second set of maps, and it takes a family with many words. A premise
   says that such families exist, and this document does not follow where that premise is
   proved. By this document's interpretation the bounds say that each map is nearly an
   isometry and that the images of the maps fill the target evenly.
9. After a division the two bounds leave error terms of about x/m and about m for the weighted
   sum, and a further term of about √x that does not depend on m. The proof assumes that m lies
   between x^(1/2 − ε) and x^(1/2 + ε/2). With further premises on the numbers of the error,
   that keeps every term at most 4·x^(1/2 + 13ε/8) and gives the exponent 1/2 + cε.

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

The definitions are in [`StatementOC.lean`](../../src/Formalism/StatementOC.lean),
[`Analytic.lean`](../../src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean)
and
[`ExplicitFormulaErrorOfHostConditions.lean`](../../src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean).
Write Λ(n) for the von Mangoldt function and γ for Euler's constant. The sum `Sz x` below has
the order x·log x, and `Gz x` is that sum with its main terms subtracted.

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
of `zero_free_all_of_green_v_win` uses la = 3/2. `zeroFreeAll_of_topG` applies the step to every
primitive character ψ separately. It takes the level `Level.cyc ψ` of the powers of ψ, and the
theorem `Level.mem_cyc` says that ψ is among the kept characters of that level.

`formB` reduces to `zeroFree_of_rpow_window`, which rests on 86 declarations. The Landau reading
read that proof, and this session read in full the lemma `landau_tails` that the reading had
read by statement. The account below has four stages and follows the report, except for stage 3.

1. Put g(u) = `Gm`(e^u). Its Laplace transform Φ(s), the integral of g(u)·e^(−su) over u > 0,
   exists for real part above 2. Φ continues to real part above 0 with a simple pole at every
   zero of one of the L-functions. The theorem `poleData` builds Φ from each character and its
   inverse, with half of the weight each. The residue at a zero ρ is −S/(ρ(ρ − 1)), where S
   adds, for each character and for its inverse, half of the weight times the multiplicity of ρ
   as a zero of its L-function. The weights are positive, so S is positive and the pole stays
   when two characters share a zero. A growth bound |g(u)| ≤ C·e^(2u) is part of the same
   record of facts about g and Φ.
2. For σ > 2 and a real τ, the Taylor coefficient of order k of Φ at σ + iτ is (−1)^k times the
   integral of g(u)·u^k·e^(−(σ + iτ)u)/k! over u > 0. The interval of x from Y to Y^la is the
   interval from U to (1 + δ)U in the variable u, with U = log Y and δ = la − 1. On it the bound
   on `Gm` gives |g| + g ≤ 2R with R = e^(θu). The integral of R·e^(−θu) over the interval is
   δ·U, which is below e^(ηU) for every η > 0 and large U, and the weight
   u^k·e^(−(σ − θ)u)/k! is at most (σ − θ)^(−k). Together these bound the part of the integral
   on the interval by a multiple of e^(ηU)/(σ − θ)^k, for the sum of two quantities. One is the
   norm of the integral at σ + iτ and the other is the integral at σ itself.
3. `landau_tails` handles the part of the integral outside the interval. It picks σ from δ alone
   and the order k = ⌈(1 + δ/2)·σ·U⌉. The lemma bounds the integral of the weight
   u^k·e^((2 − σ)u)/k! outside the interval by C/σ^k with a constant C that is the same for
   every U. The factor e^(2u) of the weight comes from the growth bound of stage 1. By this
   session's own calculation, which the Lean text does not state, the weight peaks at
   u = k/(σ − 2), and that point lies inside the interval when σ is above 4(1 + δ)/δ and U is
   large. On
   each side of the interval the proof
   multiplies the weight by
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
conditions. The statement `ChebyshevInequalityAtWindowScale` in
[`TopWin.lean`](../../src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean)
asks for `eD` and `eL` first and for every small ε after them, so the exponent is 1/2 + c·ε with
a constant c that depends on neither ε nor Y.

- The condition `CoreAtH` is an existence statement with 23 witnesses and sixteen conditions.
  It says that a record `Data` of real numbers exists over the host with the condition
  `SizeData₂` of the next section and fifteen further conditions. `ChainTied` is the form of the
  same statement for a family, with four further conditions that tie the numbers of the record
  to the data of the family, and `tiedCore_of_chainTied` passes from it to the form for a host.
- The condition `EAtH` concerns the characters and has six fields. Its field `kept` places the
  characters of the level among the characters of the host. Its field `bdG` speaks about the
  set `Bounded`, which holds the characters of the host that are trivial on a subgroup `A0` and
  are not kept. The field asks that each of them, taken as a primitive Dirichlet character χ,
  satisfies `‖gChi χ x‖ ≤ x^(1/2 + ε)` at the point x of `core_gm`. This document calls the
  characters
  of `Bounded` the other characters. A field `bdL` asks for a bound on their logarithmic
  derivatives at 1.

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
  between Y and Y^A, for an exponent A ≥ 1 that the caller chooses, and that its logarithmic
  derivative at 1 is at most 4·log y in absolute value. A further field `boxes` gives a
  zero-free box for the real ones among them.
- `pairEx` proves that such a pair exists for every large Y, and it rests on 1,271 declarations.
  It takes the pair from `pair_exists`, which takes it from `pair_share`. That theorem states
  that both ranges hold primes, that all but a share η of the primes q in the first range meet a
  condition `GoodQ`, and that for each such q all but a share η of the primes d in the second
  range meet a condition `GoodD`. `pair_exists` applies it with η = 1/2.

This session read the statement of `PairGood` and read in full the proofs of `boundedTw`,
`pairEx` and `pair_exists`. The subsection on the pair of primes at the end of this section
follows the proof of `pair_share`. The logarithms of q and d are both at least Y^(ε/5)/2 once
log Y ≥ 1, so for each fixed exponent B both primes exceed Y^B once Y is large. The argument y
of the field `bounds` is at most Y^A, which is at most (2·log q)^(5A/ε). The field `bounds`
therefore concerns sums whose length is at most a fixed power of the logarithm of the modulus.
That observation follows from the ranges above and is this session's own.

One of the sixteen conditions of `CoreAtH` is `ThinScales`. It concerns the prime sums at
arguments far above x, and it says that each of them is at most y·θ in absolute value for every
y from a third of a bound X′ on, with two free numbers X′ and θ. The statement
`PropTwoSixThinScales` is a second statement of that shape, for a datum. For every character χ
of the host it has the conclusion `‖gChi χ y‖ ≤ y·exp(−c·x^(ε/8))` for y at least
exp(x^(ε/3))/3 and a constant c, under a premise `PropTwoSixBoxHypothesis` on the
host. The code derives `PropTwoSixThinScales` from three statements that it bundles as
`LitThin` and that `litThin` in
[`LitThin.lean`](../../src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LitThin.lean)
proves. The first, `adm6`, holds a bound of a constant times Q^(1/4) on the number of zeros with
real part at least 1 − 1/400 and the classical zero-free region with one possible exceptional
real zero. The second, `adm7`, is a truncated explicit formula. The third, `adm11`, bounds the
number of zeros in each window of height 2 by a constant times a logarithm. `litThin` rests on
319 declarations. This session read the three statements, and it read neither their proofs nor
the derivation of `ThinScales` from them.

### The pair of primes

`pair_share` in
[`PairShare.lean`](../../src/Development/AutomorphicArithmetic/MeanSquareBounds/PairShare.lean)
rests on 1,239 declarations. It is the source of the bound of square-root size for the other
characters of the host. Its files lie in the folder
[`MeanSquareBounds`](../../src/Development/AutomorphicArithmetic/MeanSquareBounds), and the
definitions that it uses lie in
[`PrimeSetTwoBounds.lean`](../../src/Development/AutomorphicArithmetic/MeanSquareBounds/PrimeSetTwoBounds.lean)
and
[`SecondEstimateOfIntervalHypothesis.lean`](../../src/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean).

The statement names two sets of primes and three conditions. Write (n/q) for the Jacobi symbol
of n and q, and Λ(n) for the von Mangoldt function as before.

- `primePairSetFirst` of a number z is the set of the primes q with q ≡ 3 mod 8 and
  exp(z/2) < q ≤ exp(z). The theorem takes z = Y^(ε/5).
- `primeSetTwoBounds` of z, z′ and q is the set of the primes d with d ≡ 7 mod 16 and
  exp(z′/2) < d ≤ exp(z′) for which q and every odd prime up to z divide d + 1. The theorem lets
  z′ lie between Y^(ε/5)·(log Y)² and K² times that number. `pairEx` takes
  z′ = Y^(ε/5)·(log Y)², which gives the range of d in `WinPair`.
- `Box` is a condition on a character ψ with parameters Q, C, τ, Y and X, and it has three
  parts. The first part, `GoodC`, says that ψ is nontrivial, that its modulus is at most Q
  and that L(ψ, s) has no zero with real part above 1 − 1/400 and imaginary part between −Q and
  Q. The code calls the last property `ZeroFreeBox`. The second part says that the logarithmic
  derivative of L(ψ, s) at s = 1 is at most C·log Y in absolute value. The third part is the
  bound of square-root size, `‖Gchi ψ y‖ ≤ y^(1/2 + τ)` for every y from Y to X.
- `GoodQ` says about a prime q that `Box` holds with Q = N₀·exp(z) for every primitive character
  that agrees with ξ(n)·(n/q) at every n coprime to N₀·q, for every character ξ of a fixed
  modulus N₀.
- `GoodD` says about two primes q and d that `Box` holds with Q = N₀·exp(z + z′) for every
  primitive character that agrees with ξ(n)·(n/d) or with ξ(n)·(n/q)·(n/d) at every n coprime
  to N₀·q·d, for every such ξ.

`Gchi` has the formula that the section on the prime sum gives for `gChi` of a nontrivial
character, and a lemma in the file of `pairEx` proves that the two are equal.

`pair_share` states that a constant C exists for which the following holds for every ε below
1/52, every τ > 0, every K ≥ 1, every η > 0, every modulus N₀, every large Y, every X up to
Y^K and every z′ of the range above. The first set of primes is nonempty, and at least the
share 1 − η of its primes q meet `GoodQ`. For each of those q the second set is nonempty, and
at least the share 1 − η of its primes d meet `GoodD`. `pair_exists`, which rests on 1,242
declarations, applies the theorem with η = 1/2 and takes one q and one d. `pairEx` applies
`pair_exists` with τ = ε/2, K = A and N₀ = 8·M, and it turns the result into the fields of
`PairGood`. It takes the bound 4·log y on the logarithmic derivative from a further theorem,
`kappa4`.

The proof of `pair_share` calls two theorems, `stage1` for q and `stage2` for d, which rest on
1,225 and 1,231 declarations. Each of them states that the primes of its set that fail the
condition form at most the share η of the set. Both are cases of one theorem, `stage`, which
rests on 1,219 declarations.

`stage` treats the set `PPset` of the primes p with p ≡ a₀ mod m₀ and √U < p ≤ U. Its
condition `admitted` asks that 8 divides m₀, that a₀ is coprime to m₀, that log U lies between
Y^(ε/6) and Y^(ε/5)·(log Y)², and that (log Y)²·log m₀ is at most 4·log U. A further premise
asks that every prime factor of m₀ is at most Y^(ε/5) or above Y^(400K). `stage1` takes m₀ = 8,
a₀ = 3 and U = exp(Y^(ε/5)). `stage2` takes U = exp(z′) and m₀ = 16·`oddM`, where `oddM` is q
times the product of the odd primes up to z, and a lemma supplies a class a₀ for which
`primeSetTwoBounds` equals `PPset`. `stage2` applies `stage` with 6ε/5 in place of ε, so that
the upper limit of log U covers every admitted z′.

`stage` takes a finite set of at most R primitive characters ξ whose moduli are at most a number
F ≤ √U. It calls a prime p of `PPset` bad when, for one of those ξ, the primitive character that
agrees with ξ(n)·(n/p) fails `Box` with Q = F·U and X = Y^K. It concludes that the bad primes
form at most the share η of `PPset`. The proof sorts the bad primes into two kinds and bounds
each kind by the share η/2.

- A bad prime of the first kind has a primitive character of modulus f·p, with f ≤ F, that fails
  `ZeroFreeBox`. `count_bad`, which rests on 89 declarations, bounds the number of such primes
  by a constant times (F·U)^(1/4), which is at most U^(3/8). Its proof calls `count_bad_core`,
  which takes the bound from `zero_density_box`. That theorem rests on 85 declarations and
  states that at most a constant times Q^(1/4) primitive characters of modulus up to Q have an
  L-function with a zero in that box. `count_a`, which rests on 19 declarations, concludes from
  the condition `admitted` that `PPset` holds at least U^(9/10) primes, and `stage` passes the
  prime number theorem in progressions and the bound `excBound` of the next list to it. The
  share of the first kind is therefore at most a constant times U^(−21/40), which falls below
  η/2 once Y is large, because log U is at least Y^(ε/6).
- A bad prime of the second kind has a truncated sum that is too large. The code's sum `S` is
  the sum of Λ(n)·min(1, y/n)·ξ(n)·(n/p) over the n up to Z = Y^(400K), and the prime is of the
  second kind when the absolute value of `S` exceeds y^(1/2 + τ)/2 for some y from Y to Y^K.
  `bad_share`, which rests on 18 declarations, bounds the share of such primes for one ξ by
  η/(2(R + 1)). The at most R characters together give at most R·η/(2(R + 1)), which is below
  η/2.
- For a prime of neither kind `box_of_S`, which rests on 174 declarations, proves `Box`, so the
  prime is not bad.

`box_of_S` passes from the truncated sum to `Gchi`. The identity `finite_splitting_of_group`,
which rests on 7 declarations, writes `Gchi ψ y` as minus the truncated sum minus y times a tail
`tailL`. The tail is minus the logarithmic derivative of L(ψ, s) at s = 1 minus the sum of
Λ(n)·ψ(n)/n over the n up to Z. `tailK`, which rests on 160 declarations, bounds Y^K times the
tail by Y^ε for a character that meets `GoodC`. Since y is at most Y^K, y times the tail is at
most Y^ε, which is at most y^(1/2 + τ)/2 for ε ≤ 1/4 and Y ≥ 16. With the truncated sum at most
y^(1/2 + τ)/2 in absolute value the identity gives the third part of `Box`. `kappaC`, which
rests on 164 declarations, gives the second part. The number 400 appears twice, as the width
1/400 of the zero-free box and as the exponent of the truncation point Z = Y^(400K). This
session read `tailK` by statement. It is this session's guess that the tail is small because a
zero-free box of width 1/400 gives a saving of Z^(−1/400), which equals Y^(−K).

`bad_share` takes a mean square bound as its premise, the code's `MeanSq`. That premise says
that the sum of |`S`|² over the primes p of the set is at most a constant C₂ times y·log y times
the number of those primes, for every y of the interval and every sequence of coefficients of
absolute value at most 1 in place of ξ. A prime of the second kind has |`S`|² above
y^(1 + 2τ)/4 at some y. The proof cuts the interval into blocks from 2^i·Y to 2^(i+1)·Y. Write
V for the left end of a block. Inside the block the proof bounds |`S`|² at any y by twice
|`S`|² at V plus 2V times the integral of the square of the derivative of `S` in y. The
derivative times y is the sum `S` with the coefficients of the n ≤ y set to 0, so the premise
bounds both terms, and their sum over p is at most 4·C₂·V·log(2V) times the number of primes.
Each prime of the second kind adds at least V^(1 + 2τ)/4, and log(2V) is at most 2·V^τ/τ, so
the share of the block is at most (32·C₂/τ)·V^(−τ). The sum over the blocks is at most the
geometric series (32·C₂/τ)·Y^(−τ)/(1 − 2^(−τ)), which falls below every positive share as Y
grows.

`meanSqK`, which rests on 1,100 declarations, proves `MeanSq` for `PPset` on the interval from
Y to Y^K. It combines two theorems.

- `meanSq_abs`, which rests on 51 declarations, multiplies the square out. The sum of |`S`|²
  over p becomes a sum over pairs n, n′ of the coefficients times the sum of (n/p)·(n′/p) over
  p. The proof rewrites the absolute value of that inner sum as the absolute value of the sum
  of (p/r) over p, where r is the product of the primes outside m₀ that divide n·n′ to an odd
  power. For the pairs with r = 1, which are the pairs for which n·n′ is a square up to primes
  of m₀, it uses the trivial bound by the number of primes. Those pairs include the diagonal
  n = n′, and their part is at most a constant times y·log y. For every other
  r but one it takes as a premise that the sum of (p/r) over p is at most a factor η′ times the
  number of primes. The pairs of the one excepted r get the trivial bound as well, and their
  part is also at most a constant times y·log y.
- `twistK`, which rests on 1,021 declarations, supplies that premise. It states for all
  exponents A′ and B′ and every large Y that each odd squarefree r > 1 that is coprime to m₀
  and at most Y^(A′), with one possible exception, has a sum of (p/r) over the primes p of
  `PPset` of at most Y^(−B′) times their number. `meanSqK` uses it with A′ = 800K, because r
  is at most n·n′ ≤ Z², and with B′ = K + 1, so the factor η′ is Y^(−(K + 1)). Its proof
  starts from four statements. `pnt_progressions_relative_weak_holds`, which rests on 982
  declarations, is the prime number theorem in arithmetic progressions with a relative error
  and one possible exceptional real zero. `zFRDirichlet`, which rests on 201 declarations, is
  the zero-free region of the L-functions of one modulus with at most one real zero in it.
  `excBound`, which rests on 136 declarations, says for every δ > 0 that a real zero of the
  L-function of a real nontrivial character of modulus N is at most 1 minus a constant times
  N^(−δ). `page_across`, which rests on 6 declarations, says that two real characters of
  moduli up to a bound W that each have a real zero close to 1 agree wherever both are
  defined, which is why one exception is enough.

This paragraph is this session's interpretation of the mechanism, except for the sentence on
`abs_pair_sum_eq`, which reports a statement. A prime p of `PPset` exceeds √U, and the
logarithm of U is at least Y^(ε/6), so p exceeds Z², the largest value of n·n′, once Y is
large. The lemma `abs_pair_sum_eq` shows that the sum of (n/p)·(n′/p) over the primes p of a
fixed residue class equals the sum of (p/r) over them up to one sign, and (p/r) is a real
character of p. That character is nontrivial unless n·n′ is a square up to primes of m₀, and
the prime number theorem in progressions makes the sum of a nontrivial character over the
primes small. On average over p the values (n/p) for different n therefore cancel as
independent signs do. The sum `S` has about y/log y terms up to y that are not zero, one for
each prime power, and each has size about log y. With independent signs its square is about
(y/log y)·(log y)², which is y·log y. The truncated sums have square-root size for most primes
p of the set for that reason, and the proof then fixes one prime q and one prime d for which
they have it. The third part of `Box` speaks about the y from Y to Y^K only, a range far below
the modulus. This session found no statement about zeros in `Box` other than the zero-free box
of `GoodC`.

This session read in full the proofs of `pair_share`, `stage1`, `stage2`, `stage`, `box_of_S`,
`count_bad`, `count_bad_core`, `meanSq_abs`, `meanSqK` and `bad_share` with the five lemmas
that precede it in its file and carry the blocks. It read by statement `zero_density_box`,
`count_a`, `tailK`, `kappaC`, `finite_splitting_of_group`, `abs_pair_sum_eq` and the four
statements that the proof of `twistK` starts from, and it read the first sixty lines of the
proof of `twistK`.

## From the two bounds on the slope to the exponent 1/2

Two theorems carry the main inequality. This session read both proofs in full, without all the
lemmas that they call. Neither proof contains a theta lift or a lattice. The lifts appear as m
copies of one term and as real numbers in a record.

### `ch_core`

`ch_core` in
[`ChCore.lean`](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean)
rests on 177 declarations. It works with the characters of a finite abelian group `E0 × H` that
stands for the Galois group of the host. `ASK` is a weighted sum of 2·log p over the primes p
that lie below a bound and whose Frobenius class lies outside a set of classes, the code's
`PhiSet`, plus a term for the prime d. The code calls those primes inert. `MAIN` is the term
that `ASK` is compared with, of the order a·log a. Here a is a number `a t` for each element t
of a finite set `TT`, and a condition `SizesA` keeps every `a t / b` within 1 of x, for a scale
b of the record. The theorem assumes the bound that `ch_top` proves for `ASK − MAIN`, summed
over `TT` and over the m lifts. It concludes that the weighted prime sum of the kept characters
is at most x^(1/2 + (C + 3)ε) plus a sum `SigA` of the absolute values of the prime sums of the
other characters, where C is a constant that the caller chooses. `core_gm` bounds `SigA` with
`sigA_le` of the section on the wanted characters.

| Row | Lemma | What it does | Rests on |
|---:|---|---|---:|
| 1 | `ch_balance` | proves the exact identity `ASK − MAIN = De` by orthogonality of characters | 67 |
| 2 | `th_le` | moves every prime sum inside `De` to one common argument | 55 |
| 3 | `core` | sums over a subgroup `A0`, which removes every character that is nontrivial on it | 134 |
| 4 | `one_char` | replaces the sum over `TT` by the value at x | 16 |
| 5 | `proposition_size_bound` | divides by the size of the sum and reads off the exponent | 9 |

This session read the lemmas of rows 2 to 4 in full and those of rows 1 and 5 by statement, and
it read the lines of the proof of row 5 that carry the exponents.
`De` is an average of twisted von Mangoldt sums over the characters of `E0 × H`, so row 1 is
finite Fourier inversion between primes in classes and character sums. The summand of row 3
does not depend on the lift index j, so the sum over the m lifts multiplies it by m. Row 4 uses
a premise on the set `TT`. The sum of a nontrivial kept character over `TT` differs from its
expected value by at most a constant times x^(−1 + ε) times the size of `TT`.

Row 5 divides the error by nT·m·b times half of the ratio nT2/n. Here nT is the size of `TT`, n
is the size of the group `H` and nT2 is the size of a second set `T2`. The error is x^(Cε)
times the expression `errorBracketSizeWindows`, which is the sum
nT·aE·(1 + m²/k) + m·(B + N), where B stands for 2·n·m·b·x^ε and N for nT2·k·b·x^(2ε)/n². The
condition `BNBounds`
in [`SChain.lean`](../../src/Formalism/SizeWindowBrackets/SChain.lean) says that B and N bound
two numbers `B0` and `Nc` of the record of the next subsection, and the error terms of the
condition `DIV` of that subsection contain `nT * a * La` and `m * (B0 + Nc)`. The condition
`RestSize` bounds aE by 2·x·b, n/nT by 2·x^(ε/8) and k by n²·x^(1/2 − ε), and it gives
x^(1/2 − ε) ≤ m and x^(−ε) ≤ nT2/n. Here aE is the scale `a` of the record and k is the number
k of the ranks of the datum, which this subsection uses in that one meaning. The theorem
assumes m ≤ x^(1/2 + ε/2) and x·m ≤ k, and nT2 ≤ n holds because `T2` is a subset of `H`. The
list below divides the bracket by nT·m·b alone, and by this session's own arithmetic that
division leaves four terms.

- The part nT·aE gives aE/(m·b), which is at most 2x/m. The premise x^(1/2 − ε) ≤ m of
  `RestSize` keeps it below 2·x^(1/2 + ε).
- The part nT·aE·m²/k gives aE·m/(k·b), which is at most 2 because x·m ≤ k.
- The part m·B gives 2·n·m·x^ε/nT, which is at most 4·m·x^(9ε/8). The premise
  m ≤ x^(1/2 + ε/2) keeps it below 4·x^(1/2 + 13ε/8), the exponent that appears in the proof.
- The part m·N gives nT2·k·x^(2ε)/(n²·nT), which is at most 2·x^(1/2 + 9ε/8) because nT2 ≤ n,
  n/nT ≤ 2·x^(ε/8) and k ≤ n²·x^(1/2 − ε).

The four terms add up to at most 10·x^(1/2 + 13ε/8). The ratio nT2/n is at least x^(−ε) by
`RestSize`, so the division by half of it costs a further factor of at most 2·x^ε. With the
factor x^(Cε) of the error and a last factor x^(3ε/8) that absorbs the constants, the exponent
is 1/2 + (C + 13/8 + 1 + 3/8)·ε, which is 1/2 + (C + 3)·ε.

The first term falls as m grows, and the third term grows with m. Without the factors x^(cε)
they are x/m and m, which are equal at m = √x, the chain length that the note gives. The proof
does not choose m. It takes x^(1/2 − ε) ≤ m ≤ x^(1/2 + ε/2) as premises, and the fourth term
has the size of about √x for every m, because k is at most n²·x^(1/2 − ε). The first term comes
from the part of the error that carries no factor m, so the m lifts share it. The third comes
from the number `B0`, which enters once for each of the m lifts and which is itself a multiple
of m. `core_gm` calls `ch_core` with the constant C = `eD` + `eL` + 3, for which `ch_core`
gives the exponent 1/2 + (C + 3)·ε, and its own conclusion has one ε more.

`B0` and `Nc` are budgets that the code defines by formulas, in
[`DataArith.lean`](../../src/Formalism/LocalRingCardinality/DataArith.lean) and
[`DataParams₂.lean`](../../src/Formalism/LocalRingCardinality/DataParams₂.lean). For a datum,
`B0` is the number `sizeBudget`, the product f·m·b·x^ε, where b is exp(x^ε) and f is twice a
number of the datum, written n′ in this paragraph. The product has the form of the B of this
subsection, and `budgetNc`, which is `Nc`, has the form of the N, each with n′ in place of n.
The condition `BNBounds` bounds `B0` and `Nc` by the B and the N of this subsection. The conditions of the next subsection then require that errors of one lift stay
within a constant
times `B0`. The condition `EComp5` is one of them. `B0` contains the factor m by its formula,
so the factor m of the third term is part of the definition of the budget. The reason why the errors of one lift fit a budget that
grows with m lies in the proofs of those conditions, which this session did not read. One
premise of `stepE_num` points to it. The field `NumFacts.sw` of its bundle of premises says that
the shift w of lift j is at least the number s of the section on one lift, which is
(k + (2j − 1)(t + 1))/2. The lower bound for the shift grows with j, and the error term of that
section grows with w.

### `ch_top`

`ch_top` in
[`ChTop.lean`](../../src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean)
proves the assumption of `ch_core`. It bounds `ASK − MAIN`, summed over `TT` and the lifts, by
x^(Cε) times the expression `errorBracketSizeWindows` that the subsection on `ch_core` writes
out. Here C is the code's `CErr`, which is `eD` + `eL` + 3. `ch_top` rests on 90
declarations. Its premise `SizeData₂`, defined in
[`SChain.lean`](../../src/Formalism/SizeWindowBrackets/SChain.lean), is a conjunction of eleven
conditions on a record `Data` of 39 real numbers and real-valued functions from
[`MeanBoundSecondForm.lean`](../../src/Formalism/RankGapBounds/MeanBoundSecondForm.lean). The
record has three indices. An index u0 runs over a finite set, which for a family is the set of
the elements of the group `H`. For each u0 an index u runs over a finite set that depends on
u0. An index t runs over a set in bijection with
`TT`, and a field `aT t` equals the `a t` of `ch_core`. The numbers `muCC` and `Fo` depend on
u0 alone, and the numbers `muN`, `h` and `T` depend on u0 and u. The bullets below fix one u0
and leave it out of the notation. The number `Main` of the record stands for the sum of `MAIN`
over `TT` and the lifts. The code writes `ph y` for y log y − y. Two of the eleven conditions
hold the idea.

- `DIV` bounds a number `muCC` from above. For every u it says that `muCC + h u − Fo` is at most
  the sum over t of `m * (ph (aT t) − aT t * logOm) − aT t * log (T u)`, plus error terms. Here
  `logOm` is a constant that the section on one lift describes. Among the eleven conditions this
  is the one in which the number m of lifts multiplies the main term.
- `SlopeIneq` bounds `muCC` from below. It says that the mean over u of `muN u − h u` with
  weights `d u`, minus the logarithm of the number of indices u and minus correction terms, is
  at most `muCC`. The statement holds when three small parameters of the record lie in stated
  ranges and a number `HH` is a positive upper bound for that mean minus a number `muMinCC`.
  The condition `HHBound` supplies the bound by `HH`.

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
it for a family. A map `pt` assigns a datum of the family to each element u0 of the group `H`,
and the index u of the record runs over the words of that datum. The bullets give four of the
ties of `TieLocal`, for the datum of one u0. The condition ties further numbers of the record,
among them `Fo`, `T u` and `Ga`, to numbers of the datum that this document did not open.

- `muCC` is the slope of the dual of a Hermitian lattice `div.RR` of the datum.
- `muN u` is the slope of a lattice `div.Nu u`, one for each word, and the weight `d u` is the
  rank of that lattice.
- `h u` is the number `div.h u` of the datum. The datum has a linear map `div.Bk u` from `Nu u`
  into the dual of `RR`, and the condition `WordFacts` in
  [`RecBridge.lean`](../../src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean) requires
  that the height `htMap` of a nonzero `Bk u` is at most `h u`.
- The number of lifts is the field `R.m` of the datum. The definition `lifts` sets the set of
  lifts to `Finset.Icc 1 D.R.m`.

The slope inequality of step 5 is therefore about the maps `Bk u` of the words of one datum
into one lattice. The next subsection shows that the bound `h u` for the height of each map is
a sum over the m lifts, which is how m enters.

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
`VWin` over the host. By the form of that bound, which the section on `VWin` gives, this is
where entry 17 of the note enters the divisibility, and that reading is an interpretation. The
form of
`LinkDIV` at one datum, `LinkDIV_at`, also includes `BesselId`, which says that a pairing `Bu`
of the datum equals a nonzero constant times a pairing `besS` after two isometries. The names
match the Bessel period of entry 12.

## The chain of lifts

The chain is a concrete object in the code. A record `ColChain` holds matrices `Kj` between
spaces with metrics, a field `fact` says that the pairing of the datum factors through their
product, and a field `lf` places each lift on a matrix.

- The structure `ChainTie` in
  [`DivisionHeightBoundStatement.lean`](../../src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean)
  links a `ColChain` to a chain of kernels, the code's `KerChain`, which has a number n of
  steps and one coupling. Its field `kerF` says that the matrix `Kj j` for j below n, read in
  coordinates, is the kernel operator number j. Its field `kerC` says that the last matrix
  `Kj n` is the coupling `cpl`. Its field `metF` says that the metric of a space is the inner
  product on the forms of that space.
- `chainOf` builds the `ColChain` from a chain of kernels by choosing bases. It rests on 54
  declarations.
- [`FiniteSumNonzeroLargeDepth.lean`](../../src/Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean)
  defines the family `chF u j` of spaces for a word u and a number j. The group that acts on
  those spaces is `UF E (N j)` times two further groups, where E is a field of the host.
  `UF E r` is the isometry group of the standard Hermitian form on E^r, the sum of
  `star (x i) * y i`, so it is a unitary group.
- The rank is `N j = k + j * (t + 1)` for natural numbers k and t of the datum, so the rank
  grows by t + 1 from each j to the next. Entry 8 of the note writes a lift as π ↦ π ⊞ μ_j[t].
  That the letter t of the note is this t is an interpretation.
- The condition `ChIdx.Ok` requires `R.m = m2 + 2` for a natural number `m2`, so m is at least
  2. The chain of a word has n = `m2` steps, so it has n + 1 = m − 1 matrices. Its ranks run
  from `N 0` to `N m`, because the last matrix covers the two lifts from `N (m − 2)` to `N m`.
- The record `ChTh` holds distributions of type `ThDist`. The distribution `th i` goes from
  rank `N i` to rank `N (i + 1)`, and the distribution `top` goes from rank `N (m − 1)` to rank
  `N m`. The chain uses `th i` for i from 0 to m − 2 and `top`, which are m distributions.
  `ThDist.Ok` requires equivariance under both unitary groups. `XiEntry` writes a kernel entry
  as a product of local functions over primes.
- The first m − 2 matrices are the kernel operators of `th 0` to `th (m − 3)`. The last matrix
  is the coupling. The definition `CplKer.comp` builds it as a weighted sum, over classes and
  over a finite set, of products of two kernels, and the definitions `cp1K` and `cp2K` take
  those two kernels from `th (m − 2)` and from `top`.
- After the matrices comes a final linear map. `chainOf` takes it as an argument g into a
  dual space and sets the field `PtL` of the chain to g in coordinates. The field `lf` places
  lift number l on the matrix with the smaller of n and a number `no l` that the caller gives.
  The m lifts sit on m − 1 matrices, so some matrix holds more than one lift.

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
numbers of a lift from one record for each place, `HCParam`. A place is a pair of a truth value
and an element of the group `H`, and the top places are the pairs of the value false and an
element of the set `TT`. This session read the definitions and the statement of each theorem of this
section.

- A place carries k numbers `u`, k − 1 numbers `v`, m numbers `e` and m numbers `b`. The fields
  `u_gt_v` and `v_gt_u` say that the numbers u and v interlace, so u₀ > v₀ > u₁ > … > u_{k−1}.
  These letters u and v are unrelated to the words u and to the v of the bullet on `kerPlace`.
- The top weight `aT t` at a top place t is `u 0` − (k − 1)/2. The code uses the letter t both
  for a top place and for the number t of the rank `N j`, and the two are unrelated.
- The weights `nu` of lift j have one entry for each index below `N (j − 1)`. The first k
  entries come from k numbers that the code calls `uW`. The first and the last of them are the
  numbers u₀ and u_{k−1}. The k − 2 between them are the numbers v₀ to v_{k−3}, each lowered by
  1/2 and, where a bit of a code is set, by a further number `Del`. The rest of the entries
  come in blocks of t + 1 consecutive values, one block for each earlier lift, centred at minus
  the number `e` of that lift. Every entry then gets the number `e` of lift j added and a shift
  subtracted that depends on its index.
- `kerPlace` is the sum of `ph` over the weights minus the sum of the weights times `logOm`.
  Here `logOm` is γ + log(π/v) minus the real part of the logarithmic derivative at 1 of the
  L-function of the quadratic character modulo the prime d of the host. The number v is half of
  a number `rd` of the host.
- `logHook` is the logarithm of the hook product of a Young diagram with k + j − 1 rows. The
  rows are built from the k − 1 numbers v and from j of the numbers b, each shifted by the
  number `e` of lift j.
- The number `hU` adds `kerPlace` and subtracts `logHook`, summed over places and over the m
  lifts. This document does not record how `hU` is tied to the number `hu` of the record of the
  path, which stands for the number h of a word.

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
- `young_diagram_step_origin`, which rests on 55 declarations, takes k rows built from k
  numbers and k − 1 rows built from k − 1 numbers that interlace with them. In the use for a
  lift the k numbers are the numbers `uW` of the list above and the k − 1 numbers are the
  numbers v, and the premise `inter` of `stepE_num` states the interlacing for them. It
  concludes the two facts in the form of an inequality and an equation with a remainder, and it
  bounds the error term and the remainder. The reading of six proofs read its proof in full.
  The proof pairs each of the k − 1 lower rows of the lift with a row under the hook product,
  bounds the difference of each pair through the interlacing, and leaves the top row without a
  partner. By the definition `originRow` the top row at a top place has the length `aT` + w − s,
  where s is (k + (2j − 1)(t + 1))/2. By the reading the weights of the blocks are bounded
  separately and go into the error term. The error term of the statement grows with w, and this
  document does not record how the proof moves the shift w of the top row into it.

By the first fact each lift contributes at most `ph (aT t)` plus the error term at a top place
t. By the second fact the sum of the weights at that place is `aT t` + k·w up to a bounded
error, and `kerPlace` multiplies that sum by `logOm`. The main term of `DIV` holds
m·(`ph (aT t)` − `aT t * logOm`), summed over `TT`. This document does not record where the
proof puts the terms that contain w and s.

`numFacts_rec`, which rests on 266 declarations, proves the premises of `stepE_num` for the data
of a family from size conditions and a choice of parameters. Four interpretations in this
section are guesses from the names and the note. They are `logOm` as the Chowla-Selberg period
and the hook product as the Weyl dimension formula, both of entry 9, the interlacing as the
interlacing weights of entry 7, and the number of lifts as the multiplicity of the note.

## The lower bound for the lattices of a datum

`Frame_at` in
[`QuadraticLogDerivCongr.lean`](../../src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean)
is the slope inequality for the lattices of a datum. Write s for the mean of `mu` − h over the
words of the datum, with the ranks of the lattices `Nu u` as weights, which the code calls
`sFrame`. Call the largest value of `muMax` − h over the words, minus s, the excess. The code
calls it `uFrame`. `Frame_at` takes two bounds as parameters. It says that a number η below the
first and a number e below the second exist for which the following holds for every positive
number HH that is at least s minus `muMinDual`, the smallest slope of the dual of `RR`. The
number s, minus the logarithm of the number of words, minus a correction, is at most the dual
slope of `RR`. The correction is (1 − `delp`)⁻¹ times the sum of 4·excess·log(1 + HH/excess) and
(η + 4·√e)·HH, where `delp` is a number of the datum. `TieLocal` ties one of the three small
numbers of the condition `SlopeIneq` of the record to `delp`.

This session read in full the proofs of `frame_at_of`, `joint_a_ramified_holds`,
`ramification_condition_holds`, `ramification_linear_case_holds`, `flat_lattice_theorem_holds`
and `word_count_bound_holds`. It read the definitions that this section names, except those of
`Dstar` and `Dall`, and the statements of the other theorems of the table.

| Theorem | What it does | Rests on |
|---|---|---:|
| `frame_at_of` | derives `Frame_at` from a general statement about several maps into one lattice | 441 |
| `joint_a_ramified_holds` | proves that general statement from the two theorems of the next two rows | 400 |
| `ramification_linear_case_holds` | turns the three bounds of `InputSG` into two conditions on the whole family of maps | 100 |
| `theoremF` | the frame theorem, which derives the inequality from those two conditions | 294 |
| `word_count_bound_holds` | bounds the sum `RsG` of the numbers of columns from below when the words are many | 3 |
| `blockReal_at_of` | shows that the matrix of the map of a word is the matrix of a second map times an isometry, from `BesselId` | 59 |
| `matK_at_of` | carries two bounds of the link over to the matrices of the maps of a datum | 64 |
| `matKF_of` | does the same for a family | 178 |
| `data_SlopeIneq` | turns `Frame_at` into the condition `SlopeIneq` of the record `Data` | 137 |
| `link_alt_alt_bis` | supplies the link `LinkS` | 11,188 |

Of the 400 declarations behind `joint_a_ramified_holds`, 190 lie in the folder
[`HarderNarasimhan`](../../src/Formalism/HarderNarasimhan) and 74 in the folder LatticeSlopes.

### The general statement

`JointARam` in
[`FrameTraceRatioFinEquiv.lean`](../../src/Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean)
is a statement about a totally complex number field, a target space with a lattice, and a finite
family of spaces, each with a lattice and a linear map into the target. It has no datum in it.
Its premises are these.

- `LatGeom` holds the geometry. Each map sends its lattice into the lattice of the target. The
  height of each map that is not zero is at most a number h of that map. At one infinite place
  a matrix is given for each map. On the rows of the target it is the matrix of the map in
  chosen frames, and it may have further rows, which number at most δ times all its rows.
- `LatNum` holds the numbers. A number s is at most the mean of `mu` − h over the family with
  the ranks as weights, the sum of s and an excess bounds `muMax` − h for every member, and HH
  is at least s minus the smallest slope of the target.
- Each matrix is the product of a first factor and an isometry. A first factor may have more
  columns than its map, and the surplus over all members is at most a share of the columns of
  the first factors. This section calls that share the lost share.
- `InputSG` holds three bounds on the first factors, with a positive weight for each member.
  For two different members the squared Hilbert-Schmidt norm of the adjoint of one first factor
  times the other, times the two weights, is at most (1 + η0) times the product of their
  numbers of columns divided by a number `Dstar`. For one member the squared Hilbert-Schmidt
  norm of the weight times its Gram matrix, minus the identity, is at most e0 times its number
  of columns. The number of rows is at most (1 + η1)·`Dstar`.
- Sizes are bounded by a number σ between 0 and 1/20. The numbers η0, η1 and the square root of
  e0 are at most σ/2, the lost share is at most 1/4, and the sum `RsG` of the numbers of
  columns of the first factors is at least `Dstar`/σ.

The conclusion is the inequality of `Frame_at` for the target lattice, with the number of
members in the logarithm, δ in place of `delp`, 2·e0 in place of e, and 5σ plus three times the
square root of the lost share in place of η.

The proof has two parts, and the proofs that join them are a few lines each.

- `ramification_linear_case_holds`, the code's statement `RamLin`, derives two conditions on
  the whole family from the three bounds of `InputSG`. Write Q for the sum over the members of
  the weight times the matrix times its adjoint, and n for the number of rows. The first
  condition says that the trace of Q² is at most (1 + η) times the square of the trace of Q
  divided by n. The second says that the squared Hilbert-Schmidt distances of the weighted Gram
  matrices from the identity add up to at most e times the sum of the numbers of columns. Its
  proof calls `compressTraceSquareBound` and `compressDiagDefectBound`, which rest on 55 and 22
  declarations and whose proofs are unread.
- `theoremF`, which the code also calls the frame theorem, derives the inequality from the two
  conditions with `LatGeom` and `LatNum`. Its proof is one line that names the theorem
  `frame_theorem_log_ideal` of the folder HarderNarasimhan, which in turn is derived from
  `frame_theorem_sharp`, and the proof of that theorem is unread. The file that names `theoremF`
  lists the parts of a theory of Harder-Narasimhan polygons by name. One of them,
  `slope_inequality_mean`, is the slope inequality for one map. For a linear map and a lattice
  with a nonzero image it says that the smallest slope of the lattice minus the height of the
  map is at most the smallest slope of the image, and that the smallest slope of the lattice is
  at most the largest slope of any lattice that contains the image plus the height.

### How the statement is applied to a datum

`frame_at_of` applies the general statement with these choices. The number field is the field
`LL` of the datum, and the target is the dual of `RR` with its dual lattice. The members are the
words, with the lattices `Nu u` and the maps `Bk u`. The number h of a member is the number h of
the word, s and the excess are `sFrame` and `uFrame`, δ is `delp`, and σ is x^(−CH) for a
constant CH. The matrices, the isometries, the weights and the three bounds come from a
condition `FrameReal_at`, in which the first factor of the matrix of a word u has `duS u`
columns. For a family the condition `FrameRealF` asks that three times the square root of the
lost share is at most σ, so the number that takes the place of η is at most 6σ.

The premise on the sum `RsG` comes from `word_count_bound_holds` and from two conditions on the
datum. `ChProviso_at` says that `duS u`·Γ²/`Dstar` lies between 1/C0 and C0 for every word u,
where Γ is the exponential of a constant times m⁵·f·L for numbers f and L of the datum.
`ChCode_at` says that the number of words is at least C0·Γ²·x^CH. Each word then has at least
`Dstar`/(C0·Γ²) columns, and the words together have at least `Dstar`·x^CH, which is
`Dstar`/σ. The two conditions are parts of the condition `Chosen` on a family, which has seven
parts. The statement `DesignExists`, a premise of `topDesWin`, says that families with `Chosen`
exist. `designExists_of_choices` is one of two theorems that mention it besides `topDesWin` and
the shape theorem, and this session did not read where `DesignExists` is proved.

### How the bounds of the link reach the maps

The link `LinkS` gives bounds through the condition `LinkS_at`, for a second set of maps. Each
word u has a space `Cu u` and a map `Pu u` from it into one Hilbert space of the datum. The
block `KD u u′` is the adjoint of `Pu u` composed with `Pu u′`, times the power −1/2 of the
product of two numbers `c0 u` and `c0 u′`. `hsSq u u′` is the squared Hilbert-Schmidt norm of
`KD u u′`, and `hsDiagFull u` is the squared Hilbert-Schmidt norm of `KD u u` minus the
identity. `duS u` is the complex dimension of a further space of the word.

`LinkS_at` is an implication. Its premise is the condition `ChProviso_at` of the previous
subsection, and its conclusion has three parts.

- For two different words u and u′ the number `hsSq u u′` is at most
  (1 + η0)·`duS u`·`duS u′`/`Dstar`.
- For every word u the number `hsDiagFull u` is at most e0·`duS u`.
- A number `Dall` of the datum is at most (1 + η1)·`Dstar`.

The link gives η0, η1 and the square root of e0 at most exp(−x^(ε/8)). For large x that number
is below x^(−CH)/2, the σ/2 of the general statement, by this session's own arithmetic.

The maps `Pu u` and the maps `Bk u` of the slope inequality are different maps, and the
condition `BlockReal_at` ties them. It says that at one infinite place, in chosen frames, the
matrix of `Bk u` equals the matrix of `Pu u` in an orthonormal basis, up to a complex
conjugation, times an isometry. `blockReal_at_of` proves it from `BesselId`. `matK_at_of` and
`matKF_of` then state the first two bounds for the first factors of the matrices of the maps
`Bk u`, in a condition `MatK_at`. In that condition the matrices have the rows of the target and
`Dall` − `Drows` further rows, for a second number `Drows` of the datum, so `Dall` stands where
the general statement has the number of rows when the target has `Drows` rows. By the form of
the block `KD` the weight of a word u is 1/`c0 u`. This session did not open what `Dstar` and
`Dall` are.

The rest of this section is this session's interpretation. The second bound says that each map
is an isometry up to a small relative error after scaling. For one pair of words the first
bound is (1 + η0) times the mean of the squared Hilbert-Schmidt norm of the product of the
projections onto two random subspaces of dimensions `duS u` and `duS u′` in a space of
dimension `Dstar`. By the upper side of `ChProviso_at` it is at most (1 + η0)·C0·`duS u`/Γ² for
that pair. The columns of all words outnumber the rows at least 19 times, since their sum is at
least `Dstar`/σ with σ at most 1/20 and the rows number at most (1 + η1)·`Dstar`. The images of
the maps therefore overlap, and the first bound says that they overlap as random subspaces do.
The condition on the trace of Q² is close to an equality that holds only when Q is a multiple
of the identity, since the square of the trace of Q is at most n times the trace of Q² for
every positive semidefinite Q. In that sense the images fill the target evenly. The logarithm
of the number of words is what the inequality pays for the mean over many words. The note's
entry 16 calls its statement the approximate orthogonality of the columns, and entry 13 names
the Bost slope inequality.

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
as premises. It concludes the statement `FamilyClassConnected` for a class of families, which is
the conclusion that the premise of `zeroFreeAll_of_topG` asks for. The proof of the shape
theorem supplies the links by these theorems.

| Link | What it states, by the reading | Supplied by | Rests on |
|---|---|---|---:|
| `LinkG` | local length bounds and a bound on von Mangoldt sums | `closed_linkG_of_duty` | 19,922 |
| `LinkS` | the bounds of the section on the lower bound | `link_alt_alt_bis` | 11,188 |
| `LinkEta` | a covering condition on places | `closed_linkEta_of_duty` | 1,008 |
| `LinkIRR` | 0 ≤ `delp` ≤ exp(−x^(c/7)) for a number `delp` of the datum and a constant c | `closed_linkIRR_of_join_count` | 1,840 |
| `LinkDIV` | the divisibility inequality | `closed_linkDIVt_of_closed_bridge_kernel` | 2,704 |
| `LinkMu` | a bound on the difference of two slopes | `linkMu_of_linkDIV`, from `LinkDIV` | 219 |
| `LinkGLOBAL` | the statement that the links give `ChainTied` | `link_gl`, whose proof reaches `linkCore`, the builder of the witnesses | 15,442 |

The proof of the shape theorem passes `Green` to one call, the supplier of `LinkIRR`. By the
reading `Green` is Green's parametrisation of the cuspidal characters of GL_d over a prime field.
`green_of_regular`, of whose proof the wiring reading read about two thirds, derives it from a
statement about regular characters that `greenCuspidalCharsByRegularChars_proof` proves, resting
on 1,170 declarations.

The shape theorem takes `Green` and 53 further hypotheses, which
[`TopShapeAlt.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShapeAlt.lean)
lists. The theorem `goal_of_shape_of_hyps` in
[`ShapeOf.lean`](../../src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ShapeOf.lean)
fills 51 of the 53 from the 46 fields of the record. It passes 45 fields to one hypothesis each, three
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
- The proof of `pair_share` reaches Siegel's theorem. The proof of `excBound` is one line that
  applies a theorem to `siegelLower`, which rests on 127 declarations. `siegelLower` states for
  every δ > 0 that a constant c(δ) > 0 exists with |L(χ, 1)| ≥ c(δ)·N^(−δ) for every real
  nontrivial character χ of modulus N. For δ below 1/2 the textbook proofs of that bound yield
  no value of c(δ). `stage` and `twistK` pass `excBound` to `count_a`, so if the size of Y from
  which `count_a` holds depends on c(δ), the proof yields no value of that size either. This
  session read neither the proof of `siegelLower` nor the proof of `count_a`. The five theorems
  contain neither a threshold nor a constant, so this point leaves their statements as they are.
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
- The proofs of the theorems beneath `pair_share` that were read by statement. They are
  `zero_density_box`, `count_a`, `tailK`, `kappaC`, `finite_splitting_of_group`,
  `abs_pair_sum_eq` and the four statements that the proof of `twistK` starts from. The proof
  of `twistK` after its first sixty lines is unread as well.
- The proofs of the three statements behind `litThin`, and the derivation of `ThinScales` from
  them.
- The proofs of `ch_balance`, `proposition_size_bound` and `sigA_le`, and most of the proof of
  `core_ineq`.
- The proofs of `linkDIVt_of_bridge_kernel`, of `slope_bounds` and of the four other
  propositions that `boundsMu` uses.
- The proof of `rowsU_of_colPins_alt` below its top, the conditions `ThHyp`, `AnaStep` and
  `FamilyLaws`, which say that each lift is a theta lift, the statement `LastSide`, the field
  `nprimeDef` and the field `selJ` behind `BesselId`.
- The proofs of `stepE_num` and `numFacts_rec`.
- The proofs that carry the lower bound below the general statement, which are those of
  `frame_theorem_sharp`, `compressTraceSquareBound`, `compressDiagDefectBound`,
  `blockReal_at_of`, `matK_at_of`, `matKF_of`, `data_SlopeIneq` and `link_alt_alt_bis`, the
  theorems that supply `DesignExists`, and what the numbers `Dstar` and `Dall` of the datum
  are.
- The suppliers of the links other than `linkCore`.
- The proofs below the first call in the supply branches, for example `ferreroWashington`,
  `count_i_of_printed_bound_k_kato_automorphy`, `tLift_holds_k` and the fifteen suppliers of the
  covolume bound.
- The eight statements of `GlobalTheory.Published` behind `Row` for which the reading found no
  closed theorem.
- Most of the 463,949 declarations behind the record.
- Why the errors of one lift fit the budget `B0`, and the formula `hExpl6` for the number `h`
  of a word.
- Whether the definitions of the project are the objects of the literature that their names
  suggest. This document compares a definition with the literature only where it says so, and
  the comparison of the others is work still to do.

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
| `CLAIMS.md` | the claims that carry the route, step by step, each with its declarations, how much was read and the form for an explainer |
| `cone.py` | counts what a constant rests on, and lists the constants that mention a constant |
| `check.py` | checks the names, the counts and the links of this document, and the names and the links of `CLAIMS.md` when that file is named |
| `cones.json` | the full name and the count of every theorem whose count this document gives |
| `briefs/route-check.txt` | the brief for a second model that tests the route of this document against the Lean text |
