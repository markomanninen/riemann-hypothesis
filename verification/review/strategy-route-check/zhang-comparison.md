# The list of claims compared with Robin Zhang's note

This report compares two readings of the same Lean proof. The first is the list of claims in
[`CLAIMS.md`](../../strategy/CLAIMS.md), 40 table rows in ten tables. The second is Robin Zhang's
"A preliminary note on Alpöge's proposed proof of the generalized Riemann hypothesis", dated
22 November 2026, 75 pages, at <https://www.ihes.fr/~rzhang/files/GRH%20note.pdf>.

A run of the model Claude made the comparison on 24 November 2026. It read all pages of the note
and the whole list, and for the rows where the two readings differ or where one says more it
opened the Lean declarations. The session that wrote the list then looked up the differences
below in the Lean text and wrote this report from the run's findings.

The note says of itself that a model of another maker digested the Lean code, that most of its
text from Section 2 on was written by that model, and that its author cannot claim that it is a
faithful translation. It also cites the announcement of the proof throughout. Agreement between
the two readings is therefore weaker evidence than agreement with the Lean text.

## Verdict for each row

The pages are the printed pages of the note.

| Row | Verdict | Pages of the note |
|---|---|---|
| 1.1 | agrees | 3, 15, 19 to 20 |
| 1.2 | not covered | |
| 1.3 | agrees | 19 to 20 |
| 1.4 | not covered | |
| 2.1 | agrees | 4, 16 |
| 2.2 | the note says more | 15, 17 to 19 |
| 2.3 | agrees | 5, 68 to 70 |
| 3.1 | agrees | 23 to 24 |
| 3.2 | the note says more | 58 |
| 3.3 | agrees, the note gives the outcome only | 24, 69 |
| 3.4 | not covered | |
| 3.5 | not covered | |
| 3.6 | not covered | |
| 3.7 | not covered | |
| 3.8 | not covered | |
| 4.1 | agrees, the note says more | 21 to 22, 51 |
| 4.2 | agrees | 22 |
| 4.3 | agrees | 24, 27 |
| 4.4 | agrees | 68 to 70 |
| 5.1 | the note says more | 51 to 52 |
| 5.2 | agrees, the note says more | 51 |
| 5.3 | differs | 44 to 45 |
| 5.4 | agrees | 52 |
| 6.1 | agrees, the note says more | 7, 30, 45 |
| 6.2 | agrees | 40 |
| 6.3 | agrees | 40, 44 |
| 6.4 | agrees on the ranks and on m | 26 to 28 |
| 6.5 | not covered | |
| 7.1 | not covered | |
| 7.2 | not covered | |
| 7.3 | not covered | |
| 7.4 | agrees, the note says more | 48 to 49 |
| 8.1 | agrees, the note says more | 42 to 45 |
| 8.2 | agrees | 46 to 47 |
| 9.1 | agrees, the note says more | 53 |
| 9.2 | agrees in part | 57 |
| 9.3 | agrees | 68 to 69 |
| 9.4 | agrees | 68 to 70 |
| 10.1 | not covered | |
| 10.2 | agrees for `VWin` and `Row`, the rest not covered | 31 to 34, 56 to 59 |

## The one difference

Row 5.3 says that the weighted mean of the slopes, minus the logarithm of the number of indices
and minus corrections, is at most `muCC`. Proposition 4.3 of the note, on page 45, states the
inequality without the logarithm of the number of indices. The Lean definition `SlopeIneq` in
[`MeanBoundSecondForm.lean`](../../../src/Formalism/RankGapBounds/MeanBoundSecondForm.lean) has
that term, `Real.log (Fintype.card (W u0) : ℝ)`, so the Lean text supports the row.

## Rows that said less than the Lean text

- Row 3.2 left out that q ≡ 3 mod 8 and d ≡ 7 mod 16. The note has both on page 58, and the Lean
  structure `WinPair` has them as the fields `q_mod` and `d_mod`. The row now states them.
- Row 5.2 left out that the main term of `DIV` is a sum over the top places and that it holds
  the top weight times the logarithm of a further number with a minus sign. The note has that
  term in its inequality (4.6) on page 51, and the Lean definition `DIV` has it. The row now
  states it.
- Row 2.2 states the bound `Gm x ≤ x^θ`. The note and the Lean theorem
  `zeroFree_of_rpow_window` allow a constant C in front of x^θ, and the proof uses the theorem
  with C = 1. The row is right for that use and is left as it is.

## What the note says where the list marks an interpretation or a gap

- The note calls the kernels theta kernels of a Weil representation and the chain two sequences
  of m theta lifts, on pages 6 and 25 to 26. It takes this from the announcement and from the
  digest of its model. Neither reading shows that the Lean conditions on the kernels are those
  of theta kernels.
- The note has period maps indexed by highest weights and numbers that bound the heights of
  those maps, on pages 44 to 45, in the form of row 6.3.
- For the lower bound the note gives a route. A lemma on restricting domains, on page 43, is
  followed by Harder-Narasimhan filtrations and Bost's slope inequality, on pages 40 to 45. Its
  three bounds on page 46 are the three bounds of row 8.2, and it says on page 47 that each
  normalised operator nearly preserves lengths.
- The note states on page 49 that the constant of row 7.4 comes from the Chowla-Selberg formula.
- The note gives the four terms of step 9 on pages 68 to 69 with the same bounds, and it says on
  pages 10 and 67 that the two principal errors have the sizes x/m and m.
- The note gives no reason why the errors of one lift fit a budget that grows with m.
- The note has no Young diagrams, no hook product and no interlacing of weights, so it says
  nothing on rows 7.1 to 7.3.

## What the note has and the list lacks

Each entry would matter for an explainer of the strategy. None of them was compared with the
Lean text.

1. The reason why periods enter, on pages 5 to 6. An upper bound for the sizes of automorphic
   periods at the infinite places bounds their valuations at the primes, through the product
   formula.
2. A proof that a bound from one side suffices, on pages 15 to 19, with positive coefficients, a
   density that puts its mass inside the window, and Cauchy estimates.
3. Why a family of characters appears, on pages 4 to 5 and 20 to 21.
4. The identity that turns a condition on Frobenius classes into sums over characters, on pages
   20 to 22, and the remark that only the logarithmic derivative at 1 occurs.
5. The choice of scales and of the set of places, on pages 8 to 9, 23 to 24 and 52 to 53.
6. The first pairing, a Bessel or Fourier-Jacobi period that is carried through m theta lifts by
   seesaw identities, on pages 6 and 27 to 28.
7. The analogy with Stepanov's method, in which m plays the part of the order of vanishing, on
   page 27.
8. The cancellation of the main term, on pages 47 to 49.
9. The geometry that bounds covolumes of lattices of automorphic forms, on pages 7 to 8 and 34
   to 42.
10. The proof of the slope inequality, on pages 42 to 45.
11. The role of denominators that projections onto Hecke eigenspaces bring in, on pages 54 to
    55.
12. The definition of the quantity that `VWin` bounds and an outline of the proof of the bound,
    on pages 58 to 65.
13. Why the interval of the bound cannot be chosen freely, on pages 65 to 66.
14. The order of the quantifiers at the end, on pages 69 to 70.
15. The final calculation, on pages 68 to 70.

## How the sections of the note map onto the nine steps

| Section of the note | Pages | Steps of the commentary |
|---|---|---|
| 2, detecting zeros from sums over prime powers | 15 to 20 | step 2 and row 1.3 |
| 3, recovering the sums from divisibility of periods | 20 to 24 | steps 3 and 4 |
| 4.1, repeated theta lifts | 25 to 31 | step 6 |
| 4.2, Hecke eigenvalues and Galois representations | 31 to 34 | the premise `Row` |
| 4.3, lattices of automorphic forms | 34 to 42 | no counterpart |
| 4.4, how the period maps control the mean slope | 42 to 47 | step 8 and row 5.3 |
| 4.5 and 4.6, the main term and the bound | 47 to 53 | steps 5 and 7 and row 9.1 |
| 5 and 6, denominators and the parameters | 53 to 70 | the premise `VWin` and step 9 |

Step 1 of the commentary and its step 7, the bound for one lift through Young diagrams, have no
section in the note.

## The eight parts of the overview and the nine steps

Section 1 of the note, its mathematical overview, runs in eight parts. Three are numbered
subsections and five are headed paragraphs. Figure 1 on page 11 draws the same ingredients as a
tree below GRH for Dirichlet L-functions, with historical references, and Figures 2 to 4 draw
three of its branches in more detail. The table places each part on the nine steps of the
commentary in [`README.md`](../../strategy/README.md). The pages are the printed pages of the
note.

| Part of the overview | Pages | Steps of the commentary |
|---|---|---|
| 1.1, zeros of L-functions and the restriction to primitive characters | 3 | part of step 1 |
| 1.2, the logarithmic derivative and the sums over prime powers | 3 to 5 | step 2 |
| 1.3, why automorphic periods bound the sums | 5 to 6 | no step, see the next section |
| Automorphic periods and theta lifts | 6 to 7 | step 6 |
| Lattices of automorphic forms | 7 to 8 | steps 5 and 8, and the covolume bound of the supply branches |
| Complex places that avoid three-term arithmetic progressions | 8 to 9 | steps 3 and 4, and the blocks of weights in step 7 |
| Hecke eigenvalue congruences and Galois cohomology | 9 | no step, the premise `VWin` on lengths of Galois cohomology groups, see the next section |
| The number of theta lifts and the exponent 1/2 | 10 | step 9 |

The two sequences answer different questions. The parts of the note say why an ingredient is
needed and which earlier work it comes from. The steps of the commentary say what the Lean
theorems at each point of the route state.

Two steps have only a partial counterpart in the note. Step 1 reduces the five theorems of
`Main.lean` to zero-freeness to the right of the line with real part 1/2. Part 1.1 of the note
gives one piece of that reduction, the remark that passing from a character to its primitive
character adds no zeros with positive real part. Step 7 bounds one lift through interlacing
weights and the hook product of a Young diagram, and the overview of the note has neither. Its
part on complex places says on page 8 that the j-th lift adds a block of parameters centred at
minus a weight, and step 7 finds blocks of that form in the weights of a lift.

Two parts of the note have no step, part 1.3 and the part on Galois cohomology. The next section
reads the Lean text behind both.

## Two explanations of the note read in the Lean text

The Lean files are those of this checkout, which come from the upstream commit `611ce0b6301` of
22 November 2026. The session that wrote this section read them on 25 November 2026. A cold
reader read a first draft of the section, and the draft was corrected after its findings.

### Valuations at the primes and sizes at the infinite places

The note says on pages 5 and 6 that the normalised periods are algebraic numbers in a number
field K. For a nonzero element z of K the product formula says that the sum of log|σ(z)| over
the embeddings σ of K into ℂ equals the sum of ord𝔭(z)·log N𝔭 over the nonzero prime ideals 𝔭
of the ring of integers. An upper bound for the sizes of a nonzero period at the infinite places
therefore bounds the sum of its valuations at the primes, each weighted by log N𝔭. The note adds
that the lower bounds for these valuations are sums over prime powers with conditions on their
Frobenius classes, and that orthogonality of characters turns them into the sums of part 1.2.

The route makes the same comparison with the lattices of a datum, which the commentary
describes under steps 5 and 8. The finite places enter it in two ways, through integrality and
through the slope of a lattice. The heights of maps hold only the infinite places.

- The first way is integrality. The condition `WordFacts` in
  [`RecBridge.lean`](../../../src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean) asks
  that the map `Bk u` of a word u sends the lattice `Nu u` into the lattice `cc` of the datum.
  [`DataArith.lean`](../../../src/Formalism/LocalRingCardinality/DataArith.lean) defines `cc`
  as the dual lattice of a lattice `RR`. The lemma `oneMap_of_coord`, which the proof of
  `WordFacts` uses, derives the inclusion from the condition that each functional `Bk u φ`, for
  φ in `Nu u`, takes values in the ring of integers on `RR`.
- The height `htMap` that `WordFacts` bounds by a number `h u` is defined in
  [`StatementPl.lean`](../../../src/Formalism/HarderNarasimhan/StatementPl.lean) as the mean,
  over the infinite places, of the logarithm of the squared operator norm. It has no term at the
  primes.
- The second way is the slope of a lattice. At the level of the theorem `ch_top` the information
  at the primes is the number `ASK`. It is a sum over the inert primes p of 2·log p times the
  sum, over the powers p^i, of the positive parts max(a/p^i − w, 0), where a is a number of the
  record and w is a weight of the lift. The condition `QuotientSlopeBoundsWith` says that the
  slope `muN u` of `Nu u` is at least a number `Ga` plus a number `Fo`, minus a number `Ee u`
  and plus further numbers of the record. The condition `LossBounds` says that `ASK` is at most
  `Ga` plus a loss. Together they bound `ASK` from above by `muN u − Fo + Ee u` plus the loss,
  minus the further numbers.
- Two further conditions give bounds from the other side. The slope inequality `SlopeIneq`
  bounds the weighted mean of `muN u − h u` from above by the dual slope `muCC` of `RR`, plus a
  logarithm and corrections. The condition `DIV` bounds `muCC + h u − Fo` from above by a main
  term plus errors. The lemmas `s_lower5` and `Ga_bound5` combine these two bounds with
  `QuotientSlopeBoundsWith`. That cancels `muCC` and `Fo` and bounds `Ga` by the main term plus
  errors, and `LossBounds` then bounds `ASK` in the same way.
- The main term holds only sizes at the infinite places. It comes from the bound `h u` for the
  height of the maps, which by the second bullet has no term at the primes. It is built from the
  function ph(y) = y·log y − y, which by Stirling's formula is the leading part of log Γ(y), and
  from a constant `logOm`. The commentary describes `logOm` as γ + log(π/v) minus the real part
  of the logarithmic derivative at 1 of the L-function of the quadratic character modulo a prime
  d of the host, for a number v of the host, and it reads `logOm` as the logarithm of a
  Chowla-Selberg period.
- [`StatementPl.lean`](../../../src/Formalism/HarderNarasimhan/StatementPl.lean) also states,
  for a totally complex field, a proposition `HtGram`. It says that the normalised covolume `ht`
  of the lattice spanned by linearly independent vectors equals the product over the infinite
  places of their Gram determinants. It also says that a larger lattice of the same rank has
  that covolume divided by the index. The index holds information at the primes and the Gram
  determinants hold information at the infinite places, so `HtGram` plays the part of the
  product formula for lattices. This section did not check whether the route uses `HtGram`.

The route therefore has the shape of the note's explanation. A sum over the primes bounds the
slopes of the lattices `Nu u` from below, sizes at the infinite places bound the same slopes from
above through the slope inequality, and the two bounds together bound `ASK` by the main term.
The orthogonality of characters that turns `ASK` into the sums of part 1.2 is the lemma
`ch_balance` of step 4. No condition that this section read names the product formula for
numbers. This section did not read the sources of `QuotientSlopeBoundsWith` and `LossBounds`,
the two conditions in which the sum over the primes becomes a bound on a slope. It therefore
cannot say whether those sources rest on the product formula for lattices.

### What the bound of `VWin` absorbs

The note says on page 9 and in its Lemma 5.1 that a projection onto a sum of Hecke eigenspaces
need not split an integral lattice. The projection can then bring denominators that cancel part
of the divisibility of the periods, and bounds for Galois cohomology groups bound those
denominators. The commentary has `VWin` only as a bound on lengths of Galois cohomology groups
that absorbs a term of the divisibility inequality. The Lean text says what that term measures.

- `HypV` in
  [`DivinNOfHypV.lean`](../../../src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean)
  says that, for every large x, the host field E of every datum of a family satisfies `VVle`
  with the bound √b, where b is the scale of the datum. `VVle` in
  [`ExistsPageN.lean`](../../../src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean)
  is the form of the bound of `VWin`. For every finite set of primes it bounds by √b the sum,
  over the primes l of the set, of log l times the lengths `shaLen` for the twists e with
  1 ≤ e < t, where t is a number of the datum. By the commentary `shaLen` is the length over
  ℤ_l of a group of classes in the first Galois cohomology of E, unramified outside l, with
  coefficients ℚ_l/ℤ_l twisted by the power −e of the cyclotomic character.
- `divinN_of_hypV` proves `DIVinN`, which bounds a number `etaSum` for each lift. Its premise
  `LinkN`, defined in
  [`GlobalTheoremInputs.lean`](../../../src/Formalism/SharpRestriction/GlobalTheoremInputs.lean),
  bounds the same `etaSum` by a rank `dZ0 j` times the sum of a term of sizes and the sum over l
  of `vvTerm`, and `vvTerm` is log l times the sum of the lengths `shaLen`. `LinkN` is
  therefore the premise that ties the lengths of Galois cohomology to `etaSum`.
- `etaSum` is a sum of the numbers `etaJ j w` over the places w at which a number `muAt w` of the
  datum differs from a number `mu0`, with coefficients that include the ramification index of
  w. By [`RowSideTie.lean`](../../../src/Formalism/LocalToGlobal/Divisibility/RowSideTie.lean)
  the number `etaJ j w` of the datum equals the number of the family at w when w is a twisted
  place and 0 otherwise.
  [`LiftLat.lean`](../../../src/Formalism/LocalToGlobal/Divisibility/LiftLat.lean) defines the
  number of the family as `etaU`. At a prime w, `etaU` is the length at w of the quotient of a
  lattice `Tl` by its intersection with a lattice `cutZ`, divided by the ramification index.
- [`RowLat.lean`](../../../src/Formalism/LocalToGlobal/Divisibility/RowLat.lean) defines both
  lattices in the coordinates of a subspace Z of the forms. `Tl` is the image of a lattice
  `lvlNab` of a level under a matrix `lPr`. That matrix is the product of `Pq`, the orthogonal
  projection onto Z for a Hermitian form, with `vPr`, a projection onto a good part, and `lvlE`,
  which carries the coordinates of the level into those of the forms. `Pq` acts last. `cutZ` is
  the set of points of Z whose image lies in the lattice `nabLat`, by the definition `cutLat` as
  a preimage. So `etaU` is nonzero at w exactly when the projection onto Z of the lattice of the
  level has points whose image lies outside `nabLat` at w. This is the kind of denominator that
  the note describes.
- The same file defines the subspaces `ZH` and `partF` as sums of simultaneous eigenspaces of
  the operators `op` of a block, through the definition `eigSum` of
  [`HeckeSp.lean`](../../../src/Formalism/LocalToGlobal/Columns/HeckeSp.lean). It also defines a
  condition `ZStable`, which says that a subspace is stable under these operators and under the
  group. The family of
  [`LiftLat.lean`](../../../src/Formalism/LocalToGlobal/Divisibility/LiftLat.lean) gives its
  blocks the operators `heckeR` and `heckeL` as `op`, which are Hecke operators by their names.

The Lean text that this section read is consistent with the note's explanation. The term that
the bound of `VWin` absorbs is a weighted sum of local lengths, and each length measures the
points that a projection onto a subspace Z brings outside a lattice. The file that defines the
two lattices also builds sums of simultaneous eigenspaces of the operators that the family names
`heckeR` and `heckeL`. This section did not trace whether the subspace Z of `etaJ` on the route
is one of these sums. The step from the local lengths to the lengths of Galois cohomology is the
premise `LinkN`, and this section did not read its proof. The note gives that step on pages 53
to 67 through congruences between Hecke eigenvalues, Galois representations and the duality of
Tate and Poitou.
