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
note on the same proof. A model of another maker, Gemini, then checked every row against the
Lean text, and four runs of the first model compared its findings with the Lean text. The rows
and the lists below carry the findings that held, and the two sections before the last one give both results.

A few words recur. A host is an auxiliary abelian number field. A datum is a record of the code
that holds a host, lattices, maps and a number m of lifts, and it has a finite set of words. A
family holds a datum for every large x. A lift is one step of a chain between unitary groups. A link is one of the conditions on a
family whose names begin with `Link`.
The candidate primes are the primes of the range from which the prime q or the prime d of a host
is taken, and U is the upper end of that range. The symbol (n/p) is the Jacobi symbol, and γ is
Euler's constant. A prime sum of a character χ at y is the code's `gChi χ y`, the sum of row 2.1
for that one character. The note is the four-page note of the author of the Lean source. The
commentary explains every other word and letter of a row in the section that the row belongs to.

## Step 1, from the five theorems to one statement

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 1.1 | The first theorem of `Main.lean` says that a Dirichlet L-function has no zero with real part above 1/2, with the trivial character at s = 1 set aside. | `LFunction_ne_zero_of_half_lt_re`, `Statements.lean` | in full | As stated, since the statement is written in Mathlib terms. |
| 1.2 | Of the five theorems two are about the zeta function and three are about Dirichlet L-functions. The four after the first follow from the first. | `Claim.zeta`, `Claim.strip` | the calls in `Main.lean` read, the two named theorems unread | As stated. |
| 1.3 | The first theorem follows from `ZeroFreeAll`, which says for every primitive Dirichlet character that its L-function has no zero with real part above 1/2. The theorem `imprimitive` carries that to every Dirichlet character through the Euler factors, with the trivial character at s = 1 set aside. | `ZeroFreeAll`, `imprimitive` | definitions, `imprimitive` in full | As stated. |
| 1.4 | `ZeroFreeAll` is proved from three premises, which the code calls `Green`, `VWin` and the existence of a record `HypsAlt`. | `zero_free_all_of_green_v_win` | in full | Simplified to one route and three supply branches. The branches belong to deepening parts. |

## Step 2, from a bound on intervals to zero-freeness

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 2.1 | `Gm x` is a weighted sum over the prime powers up to x for a finite set of characters, with its main terms subtracted. | `Gm`, `Gz`, `gChi` | definitions | Textbook form, a weighted prime sum minus its main term. |
| 2.2 | Let 0 < θ < 1 and la > 1. If for every bound there is a Y above it with `Gm x ≤ x^θ` for all x from Y to Y^la, then the L-functions of the characters of `Gm` have no zero with real part above θ. The proof applies this to every primitive character separately, with a set of characters that holds the powers of that character. | `formB`, `zeroFree_of_rpow_window`, `zeroFreeAll_of_topG`, `Level.cyc` | in full, ten lemmas by statement | As stated. The point for a viewer is that an upper bound on some intervals is enough. |
| 2.3 | The proof of `zero_free_all_of_green_v_win` uses la = 3/2. `core_gm` and `level_gm_le_on_family_scales` are implications with the conclusion `Gm x ≤ x^(1/2 + (eD + eL + 7)·ε)`, for every ε > 0. `core_gm` takes two conditions on a host and concludes it for all large x. `level_gm_le_on_family_scales` takes two conditions on a family and concludes it for the large x of a set of intervals that the family carries. `eD` and `eL` are two constants of the conditions. The statement `ChebyshevInequalityAtWindowScale` asks for them before ε, so the same two constants serve every small ε. | `zero_free_all_of_green_v_win`, `level_gm_le_on_family_scales`, `core_gm`, `ChebyshevInequalityAtWindowScale` | in full | As the exponent 1/2 plus a constant times ε, with the sentence that the bound holds under the conditions that the later steps supply. |

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
| 3.1 | The condition `EAtH` on a host, one of the two conditions of `core_gm` in 2.3, has a field `kept`. It says that every character of `Gm`, the trivial one included, is the primitive character that induces some character of the host that is trivial on a subgroup `A0` and takes the value 1 at one element `iod` of the group. The code calls the characters of `Gm` kept, and it calls a character of the host kept when a character of `Gm` induces it. | `EAtH`, `kept`, `Xp`, `Kept` | definitions | Simplified to the kept characters lying among the characters of the host. |
| 3.2 | The record of a host holds two primes q and d. The condition `WinPair` is a condition on two primes and the parameters Y and ε, and it does not mention a host. The proof applies it to the two primes of the host. It says that q ≡ 3 mod 8 and d ≡ 7 mod 16, that the logarithm of q lies between Y^(ε/5)/2 and Y^(ε/5), that the logarithm of d lies between Y^(ε/5)·(log Y)²/2 and Y^(ε/5)·(log Y)², and that q and every odd prime up to Y^(ε/5) divide d + 1. | `WinPair`, `HostRaw` | definitions | Simplified to two very large primes with d + 1 divisible by q. |
| 3.3 | `Bounded` is the set of the characters of the host that are trivial on `A0` and that either take the value 1 at `iod` and are not kept, or take the value −1 at `iod`. The condition `bdG` asks that every primitive character χ that induces one of them satisfies `‖gChi χ x‖ ≤ x^(1/2 + ε)`. `supplyOfAdmOf` supplies the condition under three premises, for the set of the powers of one primitive character, and `sigA_le` uses it. | `bdG`, `Bounded`, `Xp`, `Xm`, `supplyOfAdmOf`, `sigA_le` | `supplyOfAdmOf` in full, `sigA_le` by statement | Simplified to the other characters, each with a prime sum of at most square-root size. |
| 3.4 | Let 0 < ε < 1/52, let M be a modulus and let A ≥ 1 be an exponent that the caller chooses. For every large Y at least half of the candidate primes q, and for each of those at least half of the candidate primes d, give the following. Every character of modulus M, multiplied by the quadratic character of q, of d or of both, has a prime sum of at most y^(1/2 + ε/2) for every y from Y to Y^A. The same products with a real character whose modulus divides 8·M in place of the character of modulus M have no zero with real part above 1 − 1/400 up to a bounded height. `pair_exists` takes one such pair. `boundedTw` carries the bound to the set `Bounded` of 3.3 at the one point x, with the exponent 1/2 + ε, under a condition `TwistForm`. That condition says that every character of the host that is trivial on `A0` agrees with a power of one primitive character times the quadratic characters of q and of d, each to the exponent 0 or 1, and that its value at `iod` is −1 exactly when the exponent of d is 1. | `pair_share`, `pair_exists`, `pairEx`, `PairGood`, `boundedTw`, `TwistForm` | in full | As stated, without the passage through `boundedTw`. |
| 3.5 | `stage` says that the candidate primes that fail a condition form at most the share η of all candidates, for every η > 0 and every large Y, and that the set of candidates is not empty. The condition on a prime p is `Box` for the primitive character that induces ξ(n)·(n/p), for every ξ of a finite set of characters. In the proof a failing prime p is of one of two kinds. A primitive character of modulus f·p, with f at most a bound F, has a zero with real part above 1 − 1/400 and height at most F·U, or a truncated prime sum exceeds y^(1/2 + τ)/2 in absolute value for some y from Y to Y^K, for two parameters τ > 0 and K ≥ 1 of the statement. | `stage`, `Box`, `box_of_S` | in full | As stated, with the box of zeros simplified to a zero close to the line of real part 1. |
| 3.6 | For Q ≥ 3 at most a constant times Q^(1/4) primitive characters of modulus up to Q have a zero with real part above 1 − 1/400 and height up to Q, and with Q = F·U the same bound counts the candidate primes of the first kind of 3.5. For every large Y and every range that the condition `admitted` allows, the set of candidates holds at least U^(9/10) primes. The count of candidates takes the prime number theorem in progressions and a bound on real zeros as premises, and theorems of the project prove both. | `count_bad`, `zero_density_box`, `count_a`, `admitted`, `excBound` | `count_bad` in full, the others by statement | As stated. |
| 3.7 | For every large Y and every range that `admitted` allows, for every y from Y to Y^K and every sequence of coefficients of absolute value at most 1, the squares of the truncated sums, added over the candidate primes, are at most a constant times y·log y times the number of primes. For every η > 0, every τ > 0 and every large Y, at most the share η of the primes then has a sum above y^(1/2 + τ)/2 at some y of that range. | `meanSqK`, `meanSq_abs`, `bad_share` | in full | As stated. |
| 3.8 | Let n and n′ have a product below every candidate prime. The absolute value of the sum of (n/p)·(n′/p) over the candidate primes p of one residue class equals the absolute value of the sum of a real character (p/r) of p. Here r is the product of the primes outside the modulus of the class that divide n·n′ to an odd power, and r may be 1. Let A′ and B′ be any two exponents. For every odd squarefree r > 1 that is coprime to the modulus and at most Y^(A′), with one possible exception, the absolute value of that sum is at most Y^(−B′) times the number of primes, for every large Y and every range that `admitted` allows. | `abs_pair_sum_eq`, `twistK` | by statement | Simplified to the cancellation of a character over primes. |

Added by the readings:

- The reading of 3.7 and 3.8 as independent signs is an interpretation. On average over the
  prime p the values (n/p) cancel as independent signs do, and a sum with independent signs has
  square-root size.
- The bound of 3.4 concerns y of at most (2·log q)^(5A/ε), a fixed power of the logarithm of
  the modulus. The reading found no statement about zeros in the condition `Box` other than its
  zero-free box.
- The proof of 3.4 reaches Siegel's lower bound for L(χ, 1). The textbook proofs of that bound
  give no value for its constant, so the proof of 3.4 may give no value for the size of Y from
  which 3.4 holds.
- The commentary calls the characters of the set `Bounded` of 3.3 the other characters.

## Step 4, from the characters to an arithmetic quantity

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 4.1 | `ASK` is a sum over the odd primes p up to a bound P, other than two primes `q1` and d of the host, whose Frobenius class lies outside a set `PhiSet` of classes. Each such prime adds 2·log p times a sum, over powers p^i, of the positive parts max(a/p^i − w, 0). Here a is a positive real number and w is a positive weight that depends on the class of p^i and, in the use of step 5, on an element of the group `H` and on a lift. A similar term with log d is added for the prime d. `MAIN` is the expression a·(log a − 1 − γ + L − W), where L is the value at one character of a function that the definition takes as data, and W is the mean of log w over `PhiSet`. | `ASK`, `MAIN`, `PhiSet`, `askP` | definitions | Simplified to a weighted sum over the primes of certain classes, with its main term. |
| 4.2 | Let a > 0, let the weights w be positive on `PhiSet` and let P be at least a/w. Then `ASK − MAIN` equals `De`. `De` is one over the size of `PhiSet` times a double sum, over the classes g outside `PhiSet` and over all characters ψ of a finite abelian group `E0 × H`, of the conjugate of ψ(g) times a weight w times `GPsi` of ψ at a/w. `GPsi` has the form of the prime sum of one character, with the function of 4.1 in place of the logarithmic derivative, and the rows of this step call it the prime sum of ψ. | `ch_balance`, `De`, `GPsi` | by statement | Textbook form, finite Fourier inversion between classes and characters. |
| 4.3 | `core` takes a bound Err for `ASK − MAIN`, summed over a set `TT` and the m lifts, at every element of the subgroup `A0` of the group `H`. It takes a number g that is at most the mean over `TT` of the real part of a sum of prime sums, with values of the characters as coefficients, over the characters that are trivial on `A0`. It concludes nT·m·b·(δ2/2)·g ≤ Err + 2·nT·m·b/x. Here nT is the size of `TT`, b is a scale and δ2 is the ratio nT2/n, where nT2 is the size of a subset `T2` of `A0` and n is the size of `H`. In the proof one quantity, which holds no weight w and is the same for every lift, is at most `ASK − MAIN` of each lift plus 2·b/x, so the sum over the m lifts multiplies that quantity by m. A sum over the translates by `A0` then removes every character that is nontrivial on `A0`. | `core`, `gapA`, `delta2` | in full | Simplified to the two moves of the proof, a sum over a subgroup and m equal summands. |
| 4.4 | Let 0 ≤ C and 0 < ε. For every x beyond a threshold `ch_core` takes twelve conditions on sizes, windows and characters, and it takes the bound x^(Cε) times the bracket of 9.1 for `ASK − MAIN`, summed over `TT` and the m lifts, at every element of `A0`. It concludes that `GmA` is at most x^(1/2 + (C + 3)ε) plus `SigA`. `GmA` is a sum of the real parts of the prime sums of the kept characters, with weights of absolute value at most 1. `SigA` is the sum of the absolute values of the prime sums of the characters that are trivial on `A0` and not kept. | `ch_core`, `GmA`, `SigA` | in full | As stated. |

## Step 5, two bounds on one slope

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 5.1 | `ch_top` works with a record of real numbers and real-valued functions whose first index u0 stands for an element of the group `H`. For every u0 it bounds `ASK − MAIN`, summed over `TT` and the m lifts, by x^(Cε) times the bracket of 9.1. It takes the eleven conditions `SizeData₂` on the record and four further premises. `IdentU` ties numbers of the record to the arithmetic data of step 4, `ErrWindows` and `LargeX` are conditions on sizes, and `BNBoundsU` bounds the two numbers `B0` and `Nc` of 9.1. | `ch_top`, `SizeData₂`, `IdentU`, `ErrWindows`, `BNBoundsU`, `LargeX` | in full | Simplified to two of the eleven conditions. |
| 5.2 | The condition `DIV` says for every index u0 of the record and every index u under it that a number `muCC` of u0 plus a number h of u, minus a third number of u0, is at most a main term plus errors. The main term is a sum over the top places. For each top place it holds m times the term of 7.4, minus the top weight a times the logarithm of a number T of u. | `DIV` | definitions | As stated, with h called a bound for a height, as in 6.3. The term with T is left to a deepening part. |
| 5.3 | The condition `SlopeIneq` says for every u0 that a mean s of `muN` − h over the indices u, with positive weights, minus the logarithm of the number of indices and minus corrections, is at most `muCC`. It holds when three numbers of the record lie in stated ranges and a number `HH` is positive and at least s minus a number `muMinCC`. The condition `HHBound` gives `HH` those two properties and bounds it from above by a power of x times the scale b. | `SlopeIneq`, `HHBound` | definitions | As stated. |
| 5.4 | `each_unit_bound_statement` takes all eleven conditions of `SizeData₂` and concludes for every u0 that `ASK` is at most `Main` plus an explicit error. Two of the conditions bring in `ASK`. `QuotientSlopeBoundsWith` says that every `muN` is at least a quantity `Ga` of u0 plus further numbers of the record, and `LossBounds` says that `ASK` is at most `Ga` plus a loss. In the proof `s_lower5` derives from `DIV`, `QuotientSlopeBoundsWith`, `Count5`, `EComp5` and two further conditions that s is at least `Ga` + `muCC` minus two numbers. The identity of 5.5 turns one of the two into `Main` plus errors, and the other is an error. `Ga_bound5` adds `SlopeIneq`, by which s is at most `muCC` plus the logarithm of the number of indices and the corrections. The two bounds for s cancel `muCC`, and `Ga` is at most `Main` plus that logarithm and errors. By `LossBounds`, `ASK` is then at most `Main` plus errors. | `each_unit_bound_statement`, `QuotientSlopeBoundsWith`, `LossBounds`, `s_lower5`, `Ga_bound5` | `s_lower5` in full, `Ga_bound5` in full by a reading, the theorem by statement | As a chain of three bounds. `Ga` lies below the slopes `muN`, the mean of `muN` − h lies below `muCC`, and `muCC` + h lies below the main term of 5.2, which holds the factor m. |
| 5.5 | Under the condition `HidaSetting` the record has a positive number w for each u0, each lift and each place. The condition `Count5` gives the logarithm of the number T of 5.2 three bounds. It is at least the sum over the lifts of the mean over the places of log(w·v/π), plus m times a further number, minus an error. It is at most a constant times m times a number of the record, and it varies between the indices u by at most a constant times log k. The number `Main` holds, for each lift and each top place, the expression a·(log a − 1 − `gam` + `LpL` − ℓ), where a is the top weight and ℓ is the mean over the places of log w. `gam` and `LpL` are fields of the record, and `IdentU` of 5.1 sets them to γ and to the real part of the value L of 4.1. `key_identity5` proves for positive v and w that the main term of 5.2, with the first of the three bounds in place of log T and with m times the further number times the sum of the top weights added back, equals `Main` plus an error. | `Count5`, `Main`, `HidaSetting`, `key_identity5` | definitions and the statement of the identity | In a deepening part. |

Added by the readings:

- The two conditions of 5.2 and 5.3 bound `muCC` from two sides, and the proof of 5.4 arranges
  the same inequalities as a lower and an upper bound for the mean s. The session that wrote
  the commentary checked by hand that the terms left over add up to `Main`, which is what
  `key_identity5` proves.
- The report of one reading names no source for the eleventh of the eleven conditions,
  `HidaSetting`. It has 17 parts, fourteen sign conditions and three upper bounds.
- `IdentU` ties the number w of the record to a function w of the arithmetic data, and a tie
  `TieArith` gives that function as a number of the lift at the place. The shift of a lift in
  step 7 has the same definition.
- What the quantity `Ga` of 5.4 is for a family was not opened.

## Step 6, the lattices and the chain of lifts

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 6.1 | For a family a map assigns a datum to each element of a group, and the index u of the record runs over the words of that datum. `muCC` is the slope number of the dual of a lattice `RR` of the datum, and `muN` is the slope number of a further lattice, one for each word. `TieLocal` ties thirteen further numbers of the record to numbers of the datum. | `TieLocal` | definitions | As stated. |
| 6.2 | The slope of a discrete lattice in a Euclidean space is minus the logarithm of its covolume, divided by its rank. For a lattice over a number field K the code's slope number is twice the slope of the lattice in a real inner product space, minus log 2, plus log \|d_K\| divided by the degree of K. | `covol`, `muDef` | definitions | Textbook form, minus the logarithm of the covolume divided by the rank. The factor two and the two constants are left to a deepening part. |
| 6.3 | Each word has a linear map between two spaces that sends the lattice of the word into the dual of `RR`. The condition `WordFacts` requires that, when the map is not zero, the number h of the word is at least the height of the map. The height is the mean over the infinite places of the logarithm of the squared operator norm in chosen frames. | `WordFacts`, `htMap` | definitions | The Lean form, a bound for the height. |
| 6.4 | A pairing of each word factors through a chain of spaces. The spaces number 0 to m − 1 carry a unitary group of rank k + j(t + 1), for the number j of the space, together with two further groups. The last space carries a unitary group of rank k + m(t + 1) − 1, which the code extends to rank k + m(t + 1), with one further group. Here k and t are two natural numbers of the datum. Equalities of metrics and of operators tie the chain to m kernels. `rowsU_of_colPins_alt` proves for one word, under conditions on sizes and ties, that such a chain exists. | `ChainTie`, `KerChain`, `ChTh`, `ThDist`, `FrmG`, `FormG`, `rowsU_of_colPins_alt` | definitions, `rowsU_of_colPins_alt` by statement | In the first part a chain of m kernels for each word. In a deepening part the form of 6.5. |
| 6.5 | The chain has m − 1 matrices, under a condition that sets m to a natural number plus 2. The first m − 2 are kernels composed one after the other. The last matrix composes the last two kernels inside a finite weighted sum. A final linear map follows the matrices. | `ChIdx.Ok`, `CplKer.comp`, `chainOf` | definitions | The Lean form, in a deepening part. |

Added by the readings:

- That the kernels are theta kernels for pairs of unitary groups is an interpretation. The names
  of the code say theta and Weil, and the definition asks for equivariance under both groups.
- The commentary calls the lattices of 6.1 Hermitian lattices. That is a reading of the record
  `HLat`, which holds a basis, frame matrices and a submodule.
- The conditions that say each lift is a theta lift were not traced.
- The commentary does not record how the pairing of 6.4 is tied to the map of 6.3.

## Step 7, the bound for one lift

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 7.1 | For every lift and every place, under a bundle `NumFacts` of 32 conditions, the sum of y·log y − y over the weights of the lift, minus the logarithm of a hook product, is at most a·log a − a at a top place and at most 0 elsewhere, plus an explicit error term. Here a is the top weight of the place. The same theorem bounds the absolute value of the sum of the weights minus k·w, and minus a at a top place, by a constant times w plus further terms. Here w is a number of the lift at the place, which the commentary calls the shift of the lift. | `stepE_num`, `logHook`, `NumFacts` | by statement | As stated, as an inequality that holds under size conditions. |
| 7.2 | For every Young diagram the sum of the logarithms of the factorials of the row lengths is at most the logarithm of the hook product. | `young_diagram_hook` | in full | As stated. |
| 7.3 | One of the 32 conditions of 7.1 says that the k numbers `uW` of a place and k − 1 numbers of the same place, the first k − 1 values of `sigPar`, interlace strictly. | `young_diagram_step_origin`, `inter`, `uW`, `sigPar` | in full, by a reading | Simplified to interlacing weights, as one premise among others. |
| 7.4 | The main term of 5.2 holds, for each lift and each top place, the term a·log a − a − a·`logOm`. `logOm` is γ + log(π/v) minus the real part of the logarithmic derivative at 1 of the L-function of the quadratic character modulo d, where v is a number of the host. | `DIV`, `logOm` | definitions | As stated, with `logOm` called a constant of the host. |

Added by the readings:

- The proof of `young_diagram_step_origin`, the theorem of 7.3, reaches a lemma
  `young_diagram_factorial`, which carries the pairing of rows and treats two kinds of places
  differently. At a
  place that is not a top place it pairs the first k − 1 rows of the lift with the k − 1 rows
  under the hook product and bounds the last row alone. At a top place it pairs only the k − 2
  middle rows, and it bounds the top row, the last row and one row under the hook product
  together. The top row gives the term a·log a − a.
- That `logOm` is the Chowla-Selberg period, that the hook product is the Weyl dimension
  formula, that the interlacing of 7.3 is the interlacing weights of the note, and that the
  number of lifts is the multiplicity of the note are guesses from the names and the note.
- The terms that are linear in the shift w of 7.1 and hold `logOm` cancel inside the theorem
  `divisor_inequality_assembly`, before the condition of 5.2 is formed, and they leave a
  remainder that is a multiple of the absolute value of w. The terms with log w
  go into the number T of 5.2, as row 5.5 says. The commentary does not record where the proof
  puts the terms that contain a second number of the lift, which is (k + (2j − 1)(t + 1))/2 for
  lift j.

## Step 8, the lower bound

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 8.1 | The slope inequality for the lattices of a datum follows from a general statement about a finite family of lattices with linear maps into one lattice. The proof applies it with the words of the datum as the family and the maps of 6.3 as the maps. | `Frame_at`, `frame_at_of`, `JointARam`, `joint_a_ramified_holds` | in full | As stated. |
| 8.2 | The general statement takes that each map sends its lattice into the target lattice with a height of at most a number h of that map. At one infinite place it takes for each map a matrix that is the product of a first factor and an isometry. On the rows of the target the product is the matrix of the map, and it may have further rows. A first factor may have more columns than its map, and the surplus over all maps is at most a quarter of the columns of the first factors. The statement takes three bounds on the first factors, with a positive weight for each map and a number `Dstar`. For two different maps the squared Hilbert-Schmidt norm of the adjoint of one first factor times the other, times the two weights, is at most (1 + η0) times the product of their numbers of columns divided by `Dstar`. For one map the squared Hilbert-Schmidt distance of the weighted Gram matrix of its first factor from the identity is at most e0 times its number of columns. The number of rows is at most (1 + η1)·`Dstar`. The numbers η0, η1 and the square root of e0 are at most σ/2, for a number σ of at most 1/20. A bundle `LatNum` holds a number s that is at most the mean of the slope numbers minus the numbers h, and bounds for the largest and the smallest slopes. The statement concludes that s, minus the logarithm of the number of maps and minus a correction, is at most the slope number of the target lattice. | `InputSG`, `LatGeom`, `LatNum` | definitions | As stated in a deepening part. In the first part a script may say that the maps nearly keep lengths in the mean, and it marks that sentence as the reading's own. |
| 8.3 | The proof of the general statement has two parts. The first turns the three bounds into two conditions on the products of the first factors with their isometries, for the whole family. One is on the trace of the square of the sum of the weighted products of each matrix with its adjoint, and one is on the sum of the distances of the Gram matrices from the identity. The second part, which the code calls the frame theorem, derives the inequality from those two conditions and the premises of 8.2 on the lattices. | `ramification_linear_case_holds`, `theoremF` | the first part in full, the frame theorem at its top | In a deepening part. |
| 8.4 | The general statement also needs the numbers of columns of the first factors to add up to at least `Dstar`/σ. The proof of 8.1 applies the statement with σ = x^(−CH) and gets this from two conditions on the datum. The number of columns of the first factor of every word lies between `Dstar`/(C0·Γ²) and C0·`Dstar`/Γ², and the words number at least C0·Γ²·x^CH, for constants C0 and CH and a number Γ of the datum. A premise `DesignExists` says that families with these two conditions and further conditions exist. | `word_count_bound_holds`, `ChProviso_at`, `ChCode_at`, `DesignExists` | the statements read and `word_count_bound_holds` in full, the theorems that prove `DesignExists` unread | As stated, as many words of small dimension. |
| 8.5 | Under the first condition of 8.4 and for large x a link gives the bounds of 8.2 for a second set of maps, one for each word, with η0, η1 and the square root of e0 at most exp(−x^(ε/8)). A condition `BlockReal_at` says that at one infinite place the matrix of the map of a word is the block on the rows of the target of the matrix of its second map times an isometry, up to a complex conjugation. A theorem proves that condition from a condition named `BesselId`. Two further theorems state the first two bounds for the matrices of the second maps, which are the first factors of 8.2. | `LinkS`, `LinkS_at`, `hsSq`, `hsDiagFull`, `KD`, `BlockReal_at`, `blockReal_at_of`, `matK_at_of`, `matKF_of`, `MatK_at` | definitions and statements | In a deepening part. |

Added by the readings:

- The reading of 8.2 is an interpretation. The second bound says that the first factor of each
  word is an isometry up to a small relative error after scaling, in the mean over its columns.
  For the matrices of the maps themselves the proof has that bound in the sum over the family
  only, which is the second condition of 8.3.
- For one pair of words the first bound of 8.2 is 1 + η0 times the mean of the squared
  Hilbert-Schmidt norm of the product of the projections onto two random subspaces, of the
  dimensions of the two first factors, in a space of dimension `Dstar`. By the upper side of
  the first condition of 8.4 it is at most the share (1 + η0)·C0/Γ² of the number of columns of
  one of the two first factors.
- The first factors of the words have together at least 19 times as many columns as there are
  rows. The surplus of their columns over the columns of the maps is at most a quarter, so the
  maps have together at least 14 times as many columns as there are rows. Images of nearly
  full dimension therefore overlap, and by the reading the first bound says that they overlap
  as random subspaces do.
- By the commentary's own arithmetic the bound exp(−x^(ε/8)) of 8.5 is below x^(−CH)/2, the
  σ/2 of 8.2, for large x.
- The first condition of 8.3 is close to an equality that holds only for a multiple of the
  identity, so by the reading the images of the maps fill the target evenly. The logarithm of
  the number of words in 5.3 is what the inequality pays for the mean over many words.
- The frame theorem lies in a folder on Harder-Narasimhan polygons, next to a statement of the
  slope inequality for one map. The proof of the frame theorem was read at its top, and the
  proof of the theorem that it rests on, `frame_theorem_sharp`, is unread.

## Step 9, the exponent 1/2

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 9.1 | The bound of 5.1 is x^(Cε) times the bracket nT·aE·(1 + m²/k) + m·(B + N), for a constant C and numbers nT, aE and k. The summand nT·aE carries no factor m. B stands for 2·n·m·b·x^ε and N stands for nT2·k·b·x^(2ε)/n², with nT2 and n as in 4.3, and a premise says that they bound two numbers `B0` and `Nc` of the record. | `ch_top`, `errorBracketSizeWindows`, `BNBounds`, `BNBoundsU` | in full | Simplified to the summand without a factor m and the summand m·B. The other two summands give terms that do not change the exponent. |
| 9.2 | For a datum the number `B0` is a multiple of m, the product f·m·b·x^ε for a number f of the datum and b = exp(x^ε). The code calls it a budget. | `B0`, `sizeBudget` | definitions | As stated. Each lift gets an allowance that grows with the number of lifts. |
| 9.3 | `proposition_size_bound` proves the statement `GrowthSizeBound`, which is about a real number G. Its premise is nT·m·b·((nT2/n)/2)·(G − 4·x^(1/2 + ε)) ≤ Err + 2·nT·m·b/x, the conclusion of 4.3 with G − 4·x^(1/2 + ε) in the place of g, with Err at most x^(Cε) times the bracket of 9.1. Further premises put m between x^(1/2 − ε) and x^(1/2 + ε/2), bound the other numbers of the bracket, and ask that 3 ≤ x and 26 ≤ x^(3ε/8). The conclusion is G ≤ x^(1/2 + (C + 3)ε). The proof bounds the error by a multiple of nT·m·b and cancels that factor on both sides, which divides the error by a multiple of m. | `proposition_size_bound`, `GrowthSizeBound`, `SizeWindows`, `RestSize` | by statement, the lines on the exponents read | As stated. The proof assumes the window for m and does not choose m. |
| 9.4 | `ch_core` applies 9.3 to the number G = `GmA` − `SigA` of 4.4. The conclusion of 4.4 follows, the exponent 1/2 + (C + 3)ε for the kept characters with the sum `SigA` of the other characters added. | `ch_core`, `proposition_size_bound` | in full and by statement | As stated. |

Added by the readings:

- By the commentary's own arithmetic the division of the bracket by the product nT·m·b of three
  numbers of the record leaves four terms. They are at most 2x/m, 2, 4·m·x^(9ε/8) and
  2·x^(1/2 + 9ε/8). The proof also divides by half of a ratio that is at least x^(−ε), which
  costs a further factor of at most 2·x^ε. The check by Gemini, which the section on a model of
  another maker describes, redid this arithmetic and found the same four terms.
- The premise of 9.3 has two further terms, the term 2·nT·m·b/x on the side of the error and
  the lowering of G by 4·x^(1/2 + ε). After the division they are at most 4·x^(ε − 1) and
  4·x^(1/2 + ε), and the exponent of the conclusion absorbs both for large x.
- Without the constants and the factors with ε the first and the third of the four terms are
  x/m and m, which are equal at m = √x. This comes from the arithmetic of the first entry and
  from the note. The Lean text states the window for m as a premise.
- Why the errors of the lifts fit m times the budget of 9.2 was not read.

## The supply of the premises

| No. | What the Lean text states | Declarations | Read | In an explainer |
|---|---|---|---|---|
| 10.1 | `shape_closed_link_n_of_green` takes `Green` and concludes a statement `TopShapeAlt`, which has 53 binders of data and hypotheses before its conclusion. `goal_of_shape_of_hyps` fills 51 of them from the record `HypsAlt`, and `zero_free_all_of_green_v_win` fills the other two with `trivial`. The result is, for every small ε, a family that satisfies the condition `ChainTied`, under the premise that hosts exist. `supplyChi` gets the hosts from the bound of `VWin` for one primitive character. | `shape_closed_link_n_of_green`, `TopShapeAlt`, `goal_of_shape_of_hyps`, `ChainTied`, `supplyChi` | in full, without the theorems they call | Named only. |
| 10.2 | The premises of 1.4 are these. `Green` parametrises the cuspidal irreducible characters of the general linear groups over prime fields by irreducible polynomials. `VWin` bounds sums of lengths of Galois cohomology groups, weighted by the logarithms of primes, and it is derived from a statement that the code calls `Row`. `Row` says that Galois representations exist for the regular algebraic polarized cuspidal automorphic representations over CM fields. `HypsAlt` is a record of 46 fields, five of data and 41 conditions on the families. One of the conditions says that the chain of 6.4 exists for every word. | `Green`, `VWin`, `Row`, `vwin_of_row`, `HypsAlt`, `DefiniteSideCondition` | the statements of `VWin` and `Row` with their definitions, the proofs above them at their tops | Named only in the first part. Each branch is the subject of a deepening part. |

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
step 8 in place of the five above and without row 5.5, and the rows had the wording of that
day.
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

## Checked by a model of another maker

Gemini, a model of another maker, compared the 44 rows of this list and four parts of the
commentary with the Lean text on 24 November 2026, in a conversation of the Antigravity editor.
[`gemini.md`](../review/strategy-route-check/gemini.md) holds its report, with the Lean lines
that each verdict quotes. The brief is
[`route-check.txt`](briefs/route-check.txt).

- The report supports 8 rows and marks 36. It says of 5 that the row says more than the Lean
  text, of 9 that it says less, and of 22 that it differs. It also marks 5 entries of the lists
  under the tables and 20 passages of the commentary, which makes 61 findings.
- Four runs of the model that wrote this list compared every finding with the Lean text. They
  found every quoted Lean line in its place. 60 of the 61 findings held in whole or in part,
  and one, on the last sentence of the Landau argument, did not.
- The four runs sorted the 60 by their effect on the text, which is a separate count from the
  three labels of the report. 22 of the 60 changed what a claim means, 18 of them on rows and
  4 on the lists and the commentary. The other 38 added a hypothesis, a quantifier or an exact form that the text had
  left out. Two points are counted twice among the 61, once on a list and once in the
  commentary.
- The four runs named eleven rows whose earlier wording stated something that the Lean text
  does not state. They are 2.3, 3.3, 3.4, 3.5, 4.1, 4.4, 5.1, 5.4, 8.2, 8.5 and 10.2. Two examples show the kind. Row 5.1 said that eleven
  conditions give the bound, and the theorem takes four further premises. Row 4.1 called `ASK`
  a count of primes with a main term of the order a·log a, and the Lean text has a sum of
  positive parts and an exact expression.
- The comparison also found about ten points where the outside report errs, most of them in
  its own corrected rows. It counts 31 conditions where the Lean text has 32, and its corrected
  row 3.5 gives the two kinds of failing primes as the statement of `stage`, which states the
  share η.
- The outside check redid the arithmetic of the four terms of step 9 and found the same terms
  and the same exponent.

The rows above are the wording after this check. A row that the check changed says what the
four runs found in the Lean text, which is in some rows more than the outside report asked for
and more than the commentary says. The Lean text is the reference for both documents.

## How a script uses this list

A script states a fact about the proof only when a row of this list carries it, and it marks a
sentence that comes from a list under a table as the reading's own. When a comparison with the
Lean text changes the commentary, the row changes here first and the script after it.

`check.py` of this folder looks up the names of this file among the compiled constants and tests
its links.

```bash
python3 -I verification/strategy/check.py CLAIMS.md
```
