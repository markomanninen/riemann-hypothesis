# The nine steps of the strategy compared with Robin Zhang's video overview

This report compares the nine steps of the strategy commentary in
[`README.md`](../../strategy/README.md) with a recorded talk. The talk is "A preliminary
overview of Alpöge/Claude's proof of GRH", by Robin Zhang (IHES), on the YouTube channel of
Alvaro Lozano-Robledo at <https://youtu.be/bDtAO5fRuGE>. It was published on 27 November 2026
and runs 59 minutes. The description of the video calls it part 2 of a conversation. Part 1, at
<https://youtu.be/tS8Ro66Zu1I>, is a less technical discussion, and this report has not read it.
The speaker's written note, which [`zhang-comparison.md`](zhang-comparison.md) compares with the
list of claims, is linked from the video, and the talk calls itself a summary of that note.

The text of the talk is YouTube's automatic English transcript, which is stored unchanged in
[`zhang-video-transcript.txt`](zhang-video-transcript.txt). It has no timestamps and no speaker
marks, and the lines that begin with `>>` are a change of speaker. The automatic transcript
garbles names. It writes "fatal lifts" and "vessel periods" for theta lifts and Bessel periods,
"Eric Kelloway theory" for Arakelov theory, "Chalo Selberg" for Chowla–Selberg, and
"Lavandsee" or "Levant" for Alpöge. This report cites the talk by line numbers of that file.
The slides of the talk are not part of the transcript, so a formula that the speaker only
points at on a slide is missing here.

A run of the model Claude made the comparison on 28 November 2026. It read the whole transcript
and the sections of the commentary named below, and it did not open the Lean text again. Every
statement about the Lean text in this report comes from the commentary. The commentary reads the
old text, upstream commit 611ce0b6301 of 22 November, and the talk describes the proof as
released "five days" earlier (lines 39 and 2663), which is the same old text.
[`new-edition-comparison.md`](new-edition-comparison.md) says how the steps changed in the
condensed edition of 25 November. No mathematician has checked this comparison.

The speaker says several times that his account is preliminary and incomplete, and that parts
of it lie outside his own field (lines 11 to 21, 2629 to 2643, 3165 to 3177). His note says that
a model of another maker digested the Lean code. Agreement between the talk and the commentary
is therefore weaker evidence than agreement with the Lean text.

## Verdict for each step

| Step | Short name | Verdict | Lines of the transcript |
|---:|---|---|---|
| 1 | Reduction of the five theorems to zero-freeness above 1/2 | agrees on the target, the reduction not covered | 387 to 567, 1037 to 1045 |
| 2 | Landau argument from a bound x^θ on the prime sum `Gm` | agrees | 583 to 1109 |
| 3 | Host field that holds the kept characters, and a bound for the other characters | the talk gives the outcome only | 921 to 985, 1313 to 1325 |
| 4 | Fourier inversion from the sum over characters to `ASK` | partly covered, by another route | 1167 to 1305 |
| 5 | Upper and lower bound on the slope of one lattice | another description of the same balance | 1215 to 1305, 2107 to 2149, 3199 to 3203 |
| 6 | Chain of m kernels for the pairing of each word | agrees on the shape, ranks not covered | 1937 to 2093 |
| 7 | Upper bound for one lift from interlacing weights and a hook product | agrees on two points, the method not covered | 2203 to 2431 |
| 8 | Lower bound from many maps into one lattice | names only | 2441 to 2697, 3199 to 3203 |
| 9 | Window for m that keeps the error terms x/m and m near √x | agrees, the commentary says more | 1353 to 1533 |

## The steps one by one

### Step 1

The talk defines the Riemann hypothesis for ζ (lines 387 to 421) and the generalized Riemann
hypothesis for Dirichlet L-functions (lines 479 to 541). It says that the bound of Step 2 gives
the zeros "to the right of 1/2" (lines 1037 to 1045), which is the target of Step 1. It does not
name the five theorems of `Main.lean`, the passage from primitive to all characters, or the
trivial character at s = 1. The commentary says that `zero_free_all_of_green_v_win` concludes
zero-freeness for primitive characters and that `imprimitive` extends it.

### Step 2

The talk and the commentary agree on every point that the talk states.

- The sum. The talk defines S_χ(x) as the sum of Λ(n)·χ(n)·(x/n − 1) over n ≤ x (lines 599 to
  635). The commentary's `gChi χ y` has the same sum.
- The correction term. For a nontrivial χ the talk adds x times L′(1, χ)/L(1, χ) to remove the
  pole at s = 1, and for the trivial character "a slightly different correction term" with
  Euler's constant γ (lines 809 to 843). The commentary's `gChi` adds y times the logarithmic
  derivative of L(χ, s) at s = 1, and `Gz x` is `Sz x` − x log x + (1 + γ)x. The talk does not
  give the terms −x log x + (1 + γ)x, which may be on a slide.
- The transform. The talk takes the Mellin transform of S_χ, which gives L′/L divided by
  s(s − 1), so that a zero of the L-function becomes a pole (lines 683 to 767). Stage 1 of the
  commentary takes the Laplace transform of g(u) = `Gm`(e^u), which is the same transform in the
  variable u = log x, with a pole at every zero and the residue −S/(ρ(ρ − 1)).
- The combined sum. The talk forms "some combination of … the real parts of" the G_χ (lines
  929 to 933). The commentary's `Gm` is `Gz` plus the real parts of `gChi ψ` over the kept
  characters with positive weights.
- The bound. The talk's key estimate is a bound x^(1/2 + ε) for every x in an interval from Y to
  Y^(3/2), for arbitrarily large Y (lines 989 to 1015), and it stresses that only an upper bound
  is needed (lines 1071 to 1077). That is the hypothesis of `formB` with la = 3/2, which the
  commentary says asks only for an upper bound and only on such intervals.
- The history. The talk traces the sum to the 1890s and the treatment of the pole, and the
  one-sided criterion, to Landau and Turán (lines 647 to 681, 885 to 905, 1055 to 1109). The
  commentary calls the step a Landau argument and gives no history.

The commentary says more than the talk on the proof itself. It gives the four stages of
`zeroFree_of_rpow_window`, the choice of the order k in `landau_tails` and the two cases of
stage 4, and the talk gives none of these.

One naming point needs care. The talk writes G_ψ (lines 925 to 999) for the combined sum whose
bound it calls the key estimate, and says that the proof "extracts" the G_χ from a bound on G_ψ.
In the commentary `Gm` is the combined sum over the kept characters, and `GPsi` is the prime sum
of one character ψ of the group `E0 × H` of the host in `ch_core`. The talk's G_ψ is therefore
the commentary's `Gm`, or the `GmA` of `ch_core`, and not its `GPsi`.

### Step 3

The talk says that the passage from the combined sum to the single G_χ uses "orthogonality of
characters and quite a bit of algebraic number theory" and "a lot of technical manipulation"
(lines 957 to 985), and that the number m of lifts enters where one is extracted from the other
(lines 1313 to 1325). It names no auxiliary field, no primes q and d, no subgroup `A0` and no
bound for the other characters. The commentary has all of these, and the talk gives the outcome
only.

### Step 4

The talk says that a large sum of the G_χ, a sum over all prime ideals of a number field, is
bounded from above by the automorphic periods P_m, nonzero algebraic numbers in a number field
K, one for each number m of theta lifts (lines 1139 to 1213). In the commentary the step is
`ch_balance`, an exact identity `ASK − MAIN = De` by finite Fourier inversion, and `ASK` is a sum
over the inert primes up to a bound P. The talk does not state the identity, and its sum over
prime ideals may be the commentary's `ASK` under another name. The verdict is partly covered.

### Step 5

The talk and the commentary describe the same balance in different terms.

- The talk works with one algebraic number. By the product formula, which it attributes to a
  joint paper that the transcript garbles, the product of the finite absolute values of P_m
  equals the inverse of the product of its archimedean absolute values (lines 1215 to 1305). A
  bound on the archimedean size therefore bounds the finite part, which bounds the sum of G_χ.
- It then asks three questions about the periods: their divisibility at the finite primes,
  their size at the archimedean places, and denominators that tie the periods to the estimate
  (lines 2107 to 2149).
- The commentary works with a Hermitian lattice `RR` and maps `Bk u` into it. Its slope is
  minus the logarithm of the covolume divided by the rank, `DIV` bounds the slope from above by
  m times a main term, and `SlopeIneq` bounds it from below.

The product formula for one number is the rank-one case of the Arakelov degree on which the
slope of the commentary rests. The talk names the Bost slope inequality, slopes and the lattices
of Harder and Narasimhan (lines 2681 to 2689, 3199 to 3203), but it does not say that the proof
bounds the slope of one lattice from two sides. The commentary notes that `ch_core` and
`ch_top`, which carry Steps 4, 5 and 9, contain neither a theta lift nor a lattice. That the
talk's period P_m corresponds to the pairing `Bu` of a datum, or to the lattice `RR`, is this
report's interpretation.

### Step 6

The talk describes layers of unitary groups U(X_i) inside U(Y_i), theta lifts that move an
automorphic form from one layer to the next, and a Bessel period on each layer. After m lifts
there is a period on the m-th layer (lines 1937 to 2011). It defines the Bessel period as a
generalized Fourier coefficient that integrates a form on a larger unitary group against a form
on a smaller one (lines 1745 to 1919). In the commentary the record `ColChain` holds the
matrices `Kj` of the chain, the pairing of each word factors through their product, and
`BesselId` says that the pairing `Bu` equals a constant times a pairing `besS` after two
isometries. The names match, and the commentary already ties `BesselId` to the Bessel period of
entry 12 of the author's note. The talk gives no ranks, no numbers k and t, and nothing on how
the last two kernels are composed.

### Step 7

The talk supports two points of the commentary.

- It says that the power of a finite prime that divides the period grows linearly with the
  number of lifts (lines 2203 to 2247). In the commentary each lift adds the same main term to
  the height, so the main term of `DIV` holds m times the term of one lift.
- It says that the archimedean size of the periods comes from the theory of complex
  multiplication, with formulas of Chowla–Selberg and of Anderson (lines 2259 to 2431). The
  commentary guesses from the names that `logOm` is the Chowla–Selberg period of entry 9, and a
  theorem named `meanLogPeriod_chowlaSelberg` lies behind the half of `HtNums` for the kernels.
  The talk agrees with the guess and does not make it a fact about the Lean text.

The talk does not mention interlacing weights, the hook product or the main term
a·log a − a − a·`logOm`.

### Step 8

The talk says that Arakelov theory bounds the archimedean norms of the periods (lines 2441 to
2625), with the lattices of Harder and Narasimhan and the works of Faltings, Chai and Nori and
Seshadri (lines 2681 to 2697, 3239 to 3243), and that it is "quite far from my expertise". It
names the Bost slope inequality without stating it. The commentary's `Frame_at` and `JointARam`,
the many words of a datum, and the two bounds that say that the images fill the target evenly
are not in the talk. The verdict is names only.

### Step 9

The talk states the bound m·G_ψ ≤ C_ε·x^ε·(x + m²), divides by m to get x/m + m, and takes m
about √x so that both terms are about √x (lines 1353 to 1533). It says that it takes the first
line for granted (lines 1453 to 1481). The commentary agrees on the two terms and their balance
and says more.

- The bracket of `errorBracketSizeWindows` holds four terms after the division. Besides x/m and
  m it holds a term of at most 2 from the part with m²/k and a term of about √x from the budget
  N that does not depend on m. The talk's x + m² is m times the first and third terms.
- The proof does not choose m. It takes x^(1/2 − ε) ≤ m ≤ x^(1/2 + ε/2) as premises.
- The final exponent is 1/2 + (C + 3)·ε with the constants of `ch_core`, and not 1/2 + ε.

## What the talk covers outside the nine steps

The talk spends its last third on parts that the commentary places in the supply branches.

- Denominators and Galois representations. The talk says that the denominators are differences
  a − b of Hecke eigenvalues, that a congruence between a and b changes the divisibility of the
  periods, and that the proof uses ℓ-adic Galois representations, Galois cohomology and the
  Langlands correspondence to control them (lines 2719 to 3019, 3085 to 3161). The commentary's
  branch `Row` proves the existence of Galois representations for regular algebraic polarized
  representations over CM fields, and `VWin` bounds lengths of Galois cohomology groups.
  `divinN_of_hypV` uses the bound of `VWin` to absorb a term of the divisibility inequality, and
  the commentary calls the tie to entry 17 of the note an interpretation. The talk's point 1
  of three, the divisibility, is where the commentary places the use of `VWin`, so the two agree
  on where the Galois side enters. That the denominators of the talk are the lengths of `VWin`
  is this report's interpretation.
- Further theories. The talk names integral p-adic Hodge theory, prismatic cohomology, the work
  of Bhatt, Scholze and Fargues and of Anschütz and Le Bras, deformation theory and R = T
  theorems, Selmer groups, Iwasawa theory and Kisin's work on congruences (lines 3199 to 3293).
  The commentary names none of these, except Hodge–Tate weights in `Row`, statements named after
  Greenberg and Wiles and after Bloch and Kato inside `VWin`, and the theorem `ferreroWashington`
  on class groups in a cyclotomic tower. The talk does not say which of its theories the Lean
  text uses where, and the commentary has not looked for them.
- Size of the code. The talk speaks of "17 million lines of lean code" (line 2663). The
  commentary counts 149,098 Lean files in the old text and does not count lines.

## What this means for the commentary

The talk confirms no statement of the commentary about the Lean text, because it does not cite
Lean declarations. Where it agrees with the commentary, it agrees on the analytic frame of Steps
2 and 9 in full and on the names of Steps 6 and 7. It adds three things that the commentary does
not state.

- The product formula as the reason why an archimedean bound controls the finite divisibility.
  A reader of Step 5 may find this a useful bridge to the slope of a lattice.
- The Mellin transform as the classical form of the Laplace transform of stage 1, and the names
  of Landau and Turán for the one-sided criterion.
- A description of the denominators as differences of Hecke eigenvalues, which suggests where
  the branches `Row` and `VWin` enter.

The talk gives nothing for Steps 3, 4 and 8 that the commentary lacks. None of the three
additions is a claim about the Lean text. A sentence of the commentary that took one of them up
would have to say that it comes from the talk.
