# The route in claims

This file lists the claims that carry the route of the proof, step by step. Each claim says what
the Lean text states, and it names the declarations that state it. The scripts of the explainer
videos take their statements of fact from this list and cite a claim by its number. The
[commentary](README.md) of this folder gives the detail behind every claim and the number of
declarations that each theorem rests on.

The list has two layers, and it keeps them apart.

- A table row is a claim about the Lean text. It says neither more nor less than the named
  declarations state.
- The list under a table holds what the readings and the comparisons with the Lean text added.
  An entry there is an explanation, an interpretation or a finding about the code, and a script
  that uses one says so.

The columns of a table are these. The column on reading says how much of the proof behind the
claim was read, in the three degrees that the commentary defines, which are in full, at its top
and by statement. The entry definitions marks a claim that definitions carry, and it means that
those definitions were read. The last column says in which form an explainer shows the claim and
why.

A model, Claude, wrote this list on 24 November 2026 from the commentary. Two further runs of the
same model had compared the nine steps of the commentary with the Lean text before that, and a
third compared this list with the commentary. A fourth compared the list with an independent
note on the same proof, and the last section gives the result. A model of another maker has not
yet checked this list against the Lean text.

A few words recur. A host is an auxiliary abelian number field. A datum is a record of the code
that holds a host, lattices, maps and a number m of lifts, and it has a finite set of words. A
family holds a datum for every large x. A lift is one step of a chain between unitary groups.
The candidate primes are the primes of the range from which the prime q or the prime d of a host
is taken, and U is the upper end of that range. The symbol (n/p) is the Jacobi symbol, and γ is
Euler's constant. The note is the four-page note of the author of the Lean source. The
commentary explains every other word and letter of a row in the section that the row belongs to.

## Step 1, from the five theorems to one statement

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 1.1 | The first theorem of `Main.lean` says that a Dirichlet L-function has no zero with real part above 1/2, with the trivial character at s = 1 set aside. | `LFunction_ne_zero_of_half_lt_re`, `Statements.lean` | in full | As stated, since the statement is written in Mathlib terms. |
| 1.2 | Of the five theorems two are about the zeta function and three are about Dirichlet L-functions. The four after the first follow from the first. | `Claim.zeta`, `Claim.strip` | the calls in `Main.lean` read, the two named theorems unread | As stated. |
| 1.3 | The first theorem follows from `ZeroFreeAll`, which says for every primitive Dirichlet character that its L-function has no zero with real part above 1/2. The theorem `imprimitive` extends that to all characters through the Euler factors. | `ZeroFreeAll`, `imprimitive` | definitions, `imprimitive` by statement | As stated. |
| 1.4 | `ZeroFreeAll` is proved from three premises, which the code calls `Green`, `VWin` and the existence of a record `HypsAlt`. | `zero_free_all_of_green_v_win` | in full | Simplified to one route and three supply branches. The branches belong to deepening parts. |

## Step 2, from a bound on intervals to zero-freeness

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 2.1 | `Gm x` is a weighted sum over the prime powers up to x for a finite set of characters, with its main terms subtracted. | `Gm`, `Gz`, `gChi` | definitions | Textbook form, a weighted prime sum minus its main term. |
| 2.2 | Let 0 < θ < 1 and la > 1. If for every bound there is a Y above it with `Gm x ≤ x^θ` for all x from Y to Y^la, then the L-functions of the characters of `Gm` have no zero with real part above θ. The proof applies this to every primitive character separately, with a set of characters that holds the powers of that character. | `formB`, `zeroFree_of_rpow_window`, `zeroFreeAll_of_topG`, `Level.cyc` | in full, ten lemmas by statement | As stated. The point for a viewer is that an upper bound on some intervals is enough. |
| 2.3 | The proof of `zero_free_all_of_green_v_win` uses la = 3/2. The two other named theorems prove the bound with the exponent 1/2 + c·ε for every small ε, where the constant c depends on neither ε nor Y. | `zero_free_all_of_green_v_win`, `level_gm_le_on_family_scales`, `core_gm` | in full | As stated. |

Added by the readings:

- The mechanism of 2.2 is a Landau argument. The Laplace transform of the sum has a pole at every
  zero, the residues of a real zero have one sign, and a Taylor coefficient of high order sees
  the nearest pole. The commentary gives it in four stages.
- That the weight of the Taylor coefficient peaks inside the interval when a number σ of the
  proof is above 4(1 + δ)/δ, with δ = la − 1, and the interval lies far enough out is a
  calculation of the session that wrote the commentary.

## Step 3, the wanted characters inside an auxiliary field

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 3.1 | The characters of `Gm`, which the code calls kept, are placed among the characters of a host. | `EAtH`, `kept` | definitions | As stated. |
| 3.2 | The host depends on two primes q and d with q ≡ 3 mod 8 and d ≡ 7 mod 16. The logarithm of q lies between Y^(ε/5)/2 and Y^(ε/5), the logarithm of d lies between Y^(ε/5)·(log Y)²/2 and Y^(ε/5)·(log Y)², and q and every odd prime up to Y^(ε/5) divide d + 1. | `WinPair` | definitions | Simplified to two very large primes with d + 1 divisible by q. |
| 3.3 | The characters of the host that are trivial on a subgroup and are not kept, the other characters, must each have a prime sum of absolute value at most x^(1/2 + ε). One theorem fills this condition, and one theorem uses it. | `bdG`, `Bounded`, `supplyOfAdmOf`, `sigA_le` | `supplyOfAdmOf` in full, `sigA_le` by statement | As stated. |
| 3.4 | For every large Y at least half of the candidate primes q, and for each of those at least half of the candidate primes d, give the other characters a prime sum of at most y^(1/2 + ε/2) for every y from Y to Y^A, with an exponent A ≥ 1 that the caller chooses. The proof takes one such pair. | `pair_share`, `pair_exists`, `pairEx`, `PairGood`, `boundedTw` | in full | As stated. |
| 3.5 | A candidate prime fails in one of two ways. The L-function of one of its characters has a zero with real part above 1 − 1/400 and bounded height, or a truncated prime sum is too large. | `stage`, `Box`, `box_of_S` | in full | As stated, with the box of zeros simplified to a zero close to the line of real part 1. |
| 3.6 | At most a constant times Q^(1/4) primitive characters of modulus up to Q have a zero of the kind of 3.5. Under a condition on the range and the modulus, the set of candidates holds at least U^(9/10) primes. | `count_bad`, `zero_density_box`, `count_a`, `admitted` | `count_bad` in full, the others by statement | As stated. |
| 3.7 | The squares of the truncated sums, added over the candidate primes, are at most a constant times y·log y times the number of primes. Few primes can then have a sum above y^(1/2 + τ)/2, for a fixed τ > 0. | `meanSqK`, `meanSq_abs`, `bad_share` | in full | As stated. |
| 3.8 | The sum of (n/p)·(n′/p) over the candidate primes p of one residue class equals, up to a sign, the sum of a real character (p/r) of p. For every odd squarefree r > 1 that is coprime to the modulus of the class and at most a fixed power of Y, with one possible exception, that sum is at most a negative power of Y times the number of primes. | `abs_pair_sum_eq`, `twistK` | by statement | Simplified to the cancellation of a character over primes. |

Added by the readings:

- The reading of 3.7 and 3.8 as independent signs is an interpretation. On average over the
  prime p the values (n/p) cancel as independent signs do, and a sum with independent signs has
  square-root size.
- The bound of 3.4 concerns y far below the modulus. The reading found no statement about zeros
  in the condition `Box` other than its zero-free box.
- The proof reaches Siegel's lower bound for L(χ, 1), so it may give no value for the size of Y
  from which 3.4 holds.

## Step 4, from the characters to an arithmetic quantity

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 4.1 | `ASK` is a weighted sum of 2·log p over the primes below a bound whose Frobenius class lies outside a set of classes, plus a term for the prime d. `MAIN` is a term of the order a·log a, for a number a of the record. | `ASK`, `MAIN`, `PhiSet` | definitions | Simplified to a count of primes in certain classes, with its main term. |
| 4.2 | `ASK − MAIN` equals an average `De` of prime sums over the characters of a finite abelian group. | `ch_balance` | by statement | Textbook form, finite Fourier inversion between classes and characters. |
| 4.3 | A sum over a subgroup removes every character that is nontrivial on it. The summand is the same for each of m lifts, so the sum over the lifts multiplies it by m. | `core` | in full | As stated. |
| 4.4 | If `ASK − MAIN`, summed over a set and the m lifts, is at most the error of 9.1, then the prime sum of the kept characters is at most x^(1/2 + (C + 3)ε) plus the sum of the absolute values of the prime sums of the other characters. Here C is the constant of 9.1. | `ch_core`, `SigA` | in full | As stated. |

## Step 5, two bounds on one slope

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 5.1 | The bound on `ASK − MAIN` follows from eleven conditions on a record of real numbers. | `ch_top`, `SizeData₂` | in full | Simplified to two of the eleven conditions. |
| 5.2 | The condition `DIV` says for every index u of the record that a number `muCC` plus a number h of u, minus a third number, is at most a main term plus errors. The main term is a sum over the top places. For each top place it holds m times the term of 7.4, minus the top weight a times the logarithm of a number T of u. | `DIV` | definitions | As stated, with h called a bound for a height, as in 6.3. The term with T is left to a deepening part. |
| 5.3 | The condition `SlopeIneq` says that a weighted mean of `muN` − h over the indices u, minus the logarithm of the number of indices and minus corrections, is at most `muCC`. It holds when three small numbers lie in stated ranges and a number `HH` is a positive upper bound for that mean minus a number `muMinCC`. | `SlopeIneq`, `HHBound` | definitions | As stated. |
| 5.4 | The two conditions together bound the weighted mean of `muN` from above, and `ASK` is bounded through that mean. | `each_unit_bound_statement` | by statement | As stated, as a squeeze of one number from two sides. |

Added by the readings:

- In the deduction of 5.4 the number `muCC` and the mean of h cancel. The session that wrote the
  commentary checked by hand that the terms left over add up to the main term, and a second
  reading found the same cancellation of `muCC` in the proof `Ga_bound5`.
- The report of one reading names no source for the eleventh of the eleven conditions,
  `HidaSetting`, which is a list of sign conditions.

## Step 6, the lattices and the chain of lifts

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 6.1 | For a family there is one datum for each element of a group, and the index u of the record runs over the words of that datum. `muCC` is the slope of the dual of a Hermitian lattice of the datum, and `muN` is the slope of a further lattice, one for each word. | `TieLocal` | definitions | As stated. |
| 6.2 | The slope of a lattice in a Euclidean space is minus the logarithm of its covolume, divided by its rank. For a Hermitian lattice over a number field K the code's number is twice that slope, minus log 2, plus log \|d_K\| divided by the degree of K. | `covol`, `muDef` | definitions | Textbook form, minus the logarithm of the covolume divided by the rank. The factor two and the two constants are left to a deepening part. |
| 6.3 | Each word has a linear map from its lattice into the dual of the lattice of `muCC`. When the map is not zero, the number h of the word is at least the height of the map. The height is the mean over the infinite places of the logarithm of the squared operator norm. | `WordFacts`, `htMap` | definitions | The Lean form, a bound for the height. |
| 6.4 | A pairing of each word factors through a chain between spaces on which unitary groups of ranks k + j(t + 1) act, for j from 0 to m, each together with two further groups. Here k and t are two natural numbers of the datum. The chain uses m kernels. | `ChainTie`, `KerChain`, `ChTh`, `ThDist`, `rowsU_of_colPins_alt` | definitions, `rowsU_of_colPins_alt` by statement | In the first part a chain of m kernels for each word. In a deepening part the form of 6.5. |
| 6.5 | The chain has m − 1 matrices. The first m − 2 are kernels composed one after the other. The last matrix composes the last two kernels inside a finite weighted sum. A final linear map follows the matrices. | `ChIdx.Ok`, `CplKer.comp`, `chainOf` | definitions | The Lean form, in a deepening part. |

Added by the readings:

- That the kernels are theta kernels for pairs of unitary groups is an interpretation. The names
  of the code say theta and Weil, and the definition asks for equivariance under both groups.
- The conditions that say each lift is a theta lift were not traced.
- The commentary does not record how the pairing of 6.4 is tied to the map of 6.3.

## Step 7, the bound for one lift

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 7.1 | For every lift and every place, the sum of y·log y − y over the weights of the lift, minus the logarithm of a hook product, is at most a·log a − a at a top place and at most 0 elsewhere, plus an error term. Here a is the top weight of the place. | `stepE_num`, `logHook` | by statement | As stated, as an inequality. |
| 7.2 | For every Young diagram the sum of the logarithms of the factorials of the row lengths is at most the logarithm of the hook product. | `young_diagram_hook` | in full | As stated. |
| 7.3 | The bound of 7.1 takes as a premise that two sets of numbers of the place interlace. | `young_diagram_step_origin`, `inter`, `uW` | in full, by a reading | Simplified to interlacing weights. |
| 7.4 | The main term of 5.2 holds, for each lift and each top place, the term a·log a − a − a·`logOm`. `logOm` is γ + log(π/v) minus the real part of the logarithmic derivative at 1 of the L-function of the quadratic character modulo d, where v is a number of the host. | `DIV`, `logOm` | definitions | As stated, with `logOm` called a constant of the host. |

Added by the readings:

- The proof of 7.3 pairs each lower row of the lift with a row under the hook product and leaves
  the top row without a partner. This comes from one reading of the proof.
- That `logOm` is the Chowla-Selberg period, that the hook product is the Weyl dimension
  formula, that the interlacing of 7.3 is the interlacing weights of the note, and that the
  number of lifts is the multiplicity of the note are guesses from the names and the note.
- The commentary does not record where the proof puts the terms that contain the shift of a
  lift.

## Step 8, the lower bound

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 8.1 | The slope inequality for the lattices of a datum follows from a general statement about a finite family of lattices with linear maps into one lattice. The proof applies it with the words of the datum as the family and the maps of 6.3 as the maps. | `Frame_at`, `frame_at_of`, `JointARam`, `joint_a_ramified_holds` | in full | As stated. |
| 8.2 | The general statement takes that each map sends its lattice into the target lattice with a height of at most h, and it takes three bounds on matrices of the maps at one infinite place, with a positive weight for each map and a number `Dstar`. For two different maps the squared Hilbert-Schmidt norm of the adjoint of one matrix times the other, times the two weights, is at most (1 + η0) times the product of their numbers of columns divided by `Dstar`. For one map the squared Hilbert-Schmidt distance of its weighted Gram matrix from the identity is at most e0 times its number of columns. The number of rows is at most (1 + η1)·`Dstar`. The numbers η0, η1 and the square root of e0 are at most σ/2, for a number σ of at most 1/20. | `InputSG`, `LatGeom`, `LatNum` | definitions | As stated in a deepening part. In the first part a script may say that each map nearly keeps lengths, and it marks that sentence as the reading's own. |
| 8.3 | The proof of the general statement has two parts. The first turns the three bounds into two conditions on the whole family. One is on the trace of the square of the sum of the weighted products of each matrix with its adjoint, and one is on the distances of the Gram matrices from the identity. The second part, which the code calls the frame theorem, derives the inequality from those two conditions and the premises of 8.2 on the lattices. | `ramification_linear_case_holds`, `theoremF` | the first part in full, the frame theorem at its top | In a deepening part. |
| 8.4 | The general statement also needs the numbers of columns to add up to at least `Dstar`/σ. The proof gets this from two conditions on the datum. The number of columns of every word lies between `Dstar`/(C0·Γ²) and C0·`Dstar`/Γ², and the words number at least C0·Γ²·x^CH, for constants C0 and CH and a number Γ of the datum. A premise says that families with these conditions exist. | `word_count_bound_holds`, `ChProviso_at`, `ChCode_at`, `DesignExists` | the statements read and `word_count_bound_holds` in full, the theorems that mention `DesignExists` unread | As stated, as many words of small dimension. |
| 8.5 | Under the first condition of 8.4 a link gives the bounds of 8.2 for a second set of maps, one for each word, with η0, η1 and the square root of e0 at most exp(−x^(ε/8)). A condition says that at one infinite place the matrix of the map of a word equals the matrix of its second map times an isometry, up to a complex conjugation, and a theorem proves that condition from a condition named `BesselId`. Two further theorems state the first two bounds for the matrices of the maps of 6.3. | `LinkS`, `LinkS_at`, `hsSq`, `hsDiagFull`, `KD`, `BlockReal_at`, `blockReal_at_of`, `matK_at_of`, `matKF_of` | definitions and statements | In a deepening part. |

Added by the readings:

- The reading of 8.2 is an interpretation. The second bound says that each map is an isometry
  up to a small relative error after scaling. For one pair of words the first bound is 1 + η0
  times the mean value for two random subspaces of the dimensions of the two words in a space
  of dimension `Dstar`, and by the upper side of the first condition of 8.4 it is a small share
  of the dimension of a word when Γ is large.
- The columns of all words outnumber the rows at least 19 times, so the images of the maps
  overlap, and by the reading the first bound says that they overlap as random subspaces do.
- The first condition of 8.3 is close to an equality that holds only for a multiple of the
  identity, so by the reading the images of the maps fill the target evenly. The logarithm of
  the number of words in 5.3 is what the inequality pays for the mean over many words.
- The frame theorem lies in a folder on Harder-Narasimhan polygons, next to a statement of the
  slope inequality for one map. Its proof was not read.

## Step 9, the exponent 1/2

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 9.1 | The error is x^(Cε) times the bracket nT·aE·(1 + m²/k) + m·(B + N), for a constant C and numbers nT, aE and k of the record. The summand nT·aE carries no factor m. B and N are bounds for two budgets of the record. | `ch_top`, `errorBracketSizeWindows`, `BNBounds` | in full | Simplified to the summand without a factor m and the summand m·B. The other two summands give terms that do not change the exponent. |
| 9.2 | The first budget is defined as a multiple of m, the product f·m·b·x^ε for a number f of the datum and b = exp(x^ε). | `B0`, `sizeBudget` | definitions | As stated. Each lift gets an allowance that grows with the number of lifts. |
| 9.3 | The proof divides the error by a multiple of m. The premises put m between x^(1/2 − ε) and x^(1/2 + ε/2) and bound the other numbers of the bracket. | `proposition_size_bound`, `RestSize` | by statement, the lines on the exponents read | As stated. The proof assumes the window for m and does not choose m. |
| 9.4 | The conclusion is the exponent 1/2 + (C + 3)ε for the kept characters. | `ch_core`, `proposition_size_bound` | in full and by statement | As stated. |

Added by the readings:

- By the commentary's own arithmetic the division of the bracket by the product nT·m·b of three
  numbers of the record leaves four terms. They are at most 2x/m, 2, 4·m·x^(9ε/8) and
  2·x^(1/2 + 9ε/8). The proof also divides by half of a ratio that is at least x^(−ε), which
  costs a further factor of at most 2·x^ε.
- That the terms x/m and m balance at m = √x is that arithmetic and the note. The Lean text
  states the window for m as a premise.
- Why the errors of one lift fit the budget of 9.2 was not read.

## The supply of the premises

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 10.1 | The families of data and the hosts that the route needs are supplied by two theorems, from the premises of 1.4. | `shape_closed_link_n_of_green`, `supplyChi` | in full, without the theorems they call | Named only. |
| 10.2 | The premises of 1.4 are these. `Green` is a parametrisation of characters of finite general linear groups. `VWin` is a bound on lengths of Galois cohomology groups, and it is derived from the existence of Galois representations, which the code calls `Row`. `HypsAlt` is a record of 46 fields that holds the chains of lifts. | `Green`, `VWin`, `Row`, `vwin_of_row`, `HypsAlt` | the statements of `VWin` and `Row` with their definitions, the proofs above them at their tops | Named only in the first part. Each branch is the subject of a deepening part. |

Added by the readings:

- Two notions of the branch on Galois representations are weaker than their names, a notion of
  a local Langlands map and a comparison at the places away from a prime l. The commentary
  describes both.
- Two hypotheses of the first theorem of 10.1 and one field of a bundle are the proposition
  `True`.
- The report of the declaration graph says that the five theorems rest on the three standard
  axioms of Lean and on no other axiom.

## Compared with an independent note

Robin Zhang's "A preliminary note on Alpöge's proposed proof of the generalized Riemann
hypothesis", dated 22 November 2026, is a second reading of the same Lean code, at
<https://www.ihes.fr/~rzhang/files/GRH%20note.pdf>. Its author writes that a model of another
maker digested the code and wrote most of the text, and that he cannot claim that it is a
faithful translation. A run of the model that wrote this list read the 75 pages of the note on
24 November 2026 and compared every row with it. The list had 40 rows then, with two rows for
step 8 in place of the five above.
[`zhang-comparison.md`](../review/strategy-route-check/zhang-comparison.md) holds the result row
by row.

- The note speaks about 28 of those 40 rows. On 27 of them it agrees with the row or says more,
  and on one it differs.
- The two readings differ on row 5.3. The note states the slope inequality without the logarithm
  of the number of indices, and the Lean definition `SlopeIneq` has that term, as the row says.
- The comparison found two rows that left out part of a statement, 3.2 and 5.2, and both are
  completed above from the Lean text.
- The note does not speak about rows 1.2, 1.4, 3.4 to 3.8, 6.5, 7.1 to 7.3 and 10.1.
- The note gives the same four terms as the list under step 9 and the same exponent.

Agreement between the two readings is weaker evidence than agreement with the Lean text, since
models wrote both from the same code.

## How a script uses this list

A script states a fact about the proof only when a row of this list carries it, and it marks a
sentence that comes from a list under a table as the reading's own. When a comparison with the
Lean text changes the commentary, the row changes here first and the script after it.

`check.py` of this folder looks up the names of this file among the compiled constants and tests
its links.

```bash
python3 -I verification/strategy/check.py CLAIMS.md
```
