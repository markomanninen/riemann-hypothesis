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
