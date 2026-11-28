# The nine steps of the strategy compared with the condensed edition

The upstream repository holds a Lean formalisation of a proof of the Riemann hypothesis and of the
generalized Riemann hypothesis for Dirichlet L-functions. The strategy commentary in
[`README.md`](../../strategy/README.md) describes that proof in nine steps, and this report places
each of the nine steps on the Lean text that upstream main now holds. The commentary, the list of
claims in [`CLAIMS.md`](../../strategy/CLAIMS.md) and the route data in `route.json` read the
source in [`src`](../../../src) of this fork. That source is upstream commit 611ce0b6301 of 22
November 2026, with 149,098 Lean files, and this report calls it the old text. Upstream main was
rewritten on 25 November into a condensed edition, which this report calls the new edition. This
report reads the new edition at commit 7c4ccbd64d0, the head of upstream main on 27 November, which
has 802 Lean files in `src`. The two versions share no history. Upstream keeps the older line on the
git branch `alpoge`, which has 9,235 commits after 611ce0b6301 and ends at the commit 0ca81d6329f.
The commentary has read none of those later commits.

In the new edition the main theorem `riemannHypothesis` is the term
`New.zeta_zeros_on_line New.grh`, and `New.grh` takes no hypotheses. Elsewhere this report writes
Lean names of the new edition without their prefix `New.`. The letter `P` stands for the parameters
`Parameters` of the new edition, a multiple q₀ of 18480 and a prime d ≡ q₀/2 − 1 mod q₀. The letter
`D` stands for one term of the record `Data` for these parameters, which the section on the parts
that supply the premises describes. Upstream's reading guide `GUIDE.md` names three theorems A, B
and C, which Step 5 uses and which the main inequality `star_inequality` combines. Their names in
`GUIDE.md` and their Lean names are these:

- Theorem A, short forms, with part (a) `D.span_short_integralRamified_eq_top` and part (b)
  `D.indexLe_normalizedPoincare`
- Theorem B, enough forms (`D.enough_forms`)
- Theorem C, integral forms are long (`D.integral_forms_long`)

A language model, Claude, made the comparison on 27 and 28 November 2026. It read `GUIDE.md`, the
first table of `INDEX.md`, the opening comments and the statements of the files named below, and
the proofs of `star_inequality`, `LFunction_ne_zero_of_primeRemainder_le`,
`Data.primeRemainder_le`, `eventually_primeRemainder_natCast_le`,
`eventually_primeRemainder_le_mul_rpow`, `mul_jetSize_sub_mainPrimeSum_sub_le`, `chainSize_sub_le`,
`sum_aPlaces_primeSum`, `integral_forms_long`, `integral_forms_long_with_completion_cost` and
`exists_hasSmallRatios_heightLe_liftDeterminant_div`. For the old text it used the commentary. Lean was not run, the new
edition was not built, and no mathematician has checked the comparison.

## Verdict for each step

| Step | Short name | Verdict | Where in the new edition |
|---:|---|---|---|
| 1 | Reduction of the five theorems to zero-freeness above 1/2 | the same | `Main.lean`, `New/Main` |
| 2 | Landau argument from a bound x^θ on the prime sum `Gm` | changed | `New/Reduction/Zeros/Criterion` |
| 3 | Host field that holds the wanted characters, and a bound for the unwanted characters | changed | `New/Reduction/Zeros/Criterion`, `Lib/Analytic/QuadraticTwist` |
| 4 | Fourier inversion from the sum over characters to `ASK` | the same role, by a count of places | `New/Reduction/PrimeSums` |
| 5 | Upper and lower bound on the slope of one lattice | the same idea, with covolume and index | `New/Reduction/MainInequality`, `New/Reduction/ShortAndEnough` |
| 6 | Chain of m kernels for the pairing of each word | the same spaces and ranks, glued in pairs | `New/UpperBound/Objects/Columns`, `New/UpperBound/Seesaw` |
| 7 | Upper bound for one lift from interlacing weights and a hook product | the same main term once the level N of Step 7 is subtracted, the old term m·`lg` unchecked, another method | `New/Reduction/PrimeSums`, `New/UpperBound/Size` |
| 8 | Lower bound from many maps into one lattice | the same role, the proof of the premise located | `New/Determinant/Twist/LongForms`, `New/Congruences/FitTwistsExist` |
| 9 | Window for m that keeps the error terms x/m and m near √x | changed | `New/Reduction/OneSidedBound` |

## The steps one by one

### Step 1

The new `Main.lean` states five theorems with the names of the old text. They are
`riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`,
`LFunction_eq_zero_re` and `LFunction_eq_zero_re_of_isPrimitive`. The theorem
`LFunction_ne_zero_of_half_lt_re` is `grh` itself, the statement that no Dirichlet L-function
vanishes for re s > 1/2, with the pole of the principal character at s = 1 set aside. The other
four follow from it. The two lemmas `zeros_on_line` and `zeta_zeros_on_line` of `New/Main` pass from
the half-plane to the critical line by the functional equation, which pairs a zero ρ of L(s, χ) in
the strip 0 < re s < 1 with a zero 1 − ρ of L(s, χ̄). A zero with real part below 1/2 would
therefore give a zero with real part above 1/2.

### Step 2

The old step bounds a weighted prime sum `Gm y` by y^θ on the intervals from Y to Y^(3/2), for
arbitrarily large Y. The old sum weights Λ(n)χ(n) by y/n − 1, for the characters χ of a finite set.

The new criterion `LFunction_ne_zero_of_primeRemainder_le` concerns the characters ψ modulo a
multiple q₀ of 8 and a point ρ ≠ 1 with re ρ > β, where β > 1/2. For a prime d and a modulus Q it
uses the remainder R_Q(x) = `primeRemainder d Q x`. This is the sum of Λ(n)(1 − (n/d))(1/n − 1/x)
over the n ≤ x with n ≡ 1 mod Q, less log x/φ(Q) and less the constant for which the remainder
tends to 0. Here (n/d) is the Legendre symbol of n modulo d. Step 4 also uses R_Q for Q = 1 and
writes it R₁. The criterion fixes a class d₀ ≡ 7 mod 8 prime to q₀. It asks for an eventual bound
R_{q₀}(x) ≤ A·x^(β − 1) for every prime d ≡ d₀ mod q₀, with a number A that may depend on d, and it
concludes that L(ρ, ψ) ≠ 0 for every ψ modulo q₀. For such a d the Legendre symbol modulo d is the
quadratic character χ_K of the field K = ℚ(√−d) of Step 4, because d ≡ 3 mod 4. The theorem `grh` applies
the criterion to the character modulo q₀ = 18480·q that a character modulo q induces, with
d₀ = q₀/2 − 1.

The new weight 1/n − 1/x is the old weight y/n − 1 at y = x divided by x. A bound x^θ for a sum
with the old weights therefore corresponds to a bound x^(θ − 1) for the new remainder. This shift
by 1 is why the new bound of Step 9 has the exponent −1/2 plus a multiple of a small ε > 0, where
the old bound had 1/2 plus a multiple of ε.

The proof applies Landau's lemma (`IsPolar.landau`) to the transform

    ∫₀^∞ R_{q₀}(e^v)·e^((1 − s)v) dv.

By `isPolar_primeRemainder` the transform continues meromorphically, with at most simple poles in
re s > 0 and no pole at s = 1. Its residue at a point s ≠ 1 is a sum over the characters ψ modulo
q₀. Each term is the order of L(·, ψ) at s less the order at s of the quadratic twist
L(·, ψ·(·/d)), and the sum is divided by φ(q₀)·s·(1 − s). The criterion first chooses d so that no
quadratic twist vanishes in the box β ≤ re s, |im s| ≤ |im ρ| (Step 3). In that box the residue is
ord(s)/(φ(q₀)·s·(1 − s)), where ord(s) is the sum of the orders of the L(·, ψ) at s. For a real σ
with β < σ < 1 the residue is nonnegative, because σ(1 − σ) > 0. For a real σ > 1 it is 0, because
no L(·, ψ) vanishes there. Landau's lemma takes the one-sided bound together with these nonnegative
residues on the real axis and concludes that the residue at ρ is 0, so ord(ρ) = 0 and no L(·, ψ)
vanishes at ρ.

The standard argument behind such a lemma runs as follows, and this comparison did not read its
Lean proof. The difference A·e^((β − 1)v) − R_{q₀}(e^v) is eventually nonnegative, so its transform
converges up to its first real singularity σ₀ and tends to +∞ as s decreases to σ₀. The transform
of A·e^((β − 1)v) is A/(s − β). If σ₀ were above β, the transform of R_{q₀} would therefore have a
pole with a negative residue at σ₀, which the nonnegative residues exclude. So the transform of
R_{q₀} converges in re s > β and has no pole at ρ.

### Step 3

The old step places the wanted characters in a host field that depends on two primes q′ and d′, and
it chooses q′ and d′ so that every unwanted character has a small prime sum. The new edition has no
split into wanted and unwanted characters. By the residue formula of Step 2 the remainder R_{q₀}
sees the zeros of every L(s, ψ) modulo q₀ with one sign and the zeros of every quadratic twist
L(s, ψ·(·/d)) with the other sign. The criterion therefore needs a prime d ≡ d₀ mod q₀, in the
class of Step 2, for which no quadratic twist vanishes in the box β ≤ re s, |im s| ≤ |im ρ|.
`exists_entireL_quadTwist_ne_zero` in `Lib/Analytic/QuadraticTwist` supplies one. That file calls a
prime d of the class bad when some quadratic twist has a zero in the box. Writing β = 1/2 + 9η, it
shows that at most O(X^(1 − η/2)) primes up to X are bad, so the sum of log p/p over the bad primes
converges. The sum of log p/p over all primes of the class diverges, so the class contains a prime
that is not bad. Only d is chosen, and q₀ is fixed by the modulus q of the character. The one-sided
bound of Step 9 is proved for every prime d of the class, and the choice of d enters only in the
criterion.

### Step 4

The old step turns the sum over the characters of the host into an arithmetic quantity `ASK` by
finite Fourier inversion. In the new edition the field is E = K(ζ), where K = ℚ(√−d) and ζ is a
primitive q₁-th root of unity. Here q₁ = 3·l₀·m²²·q₀ is a multiple of q₀, l₀ is a power of 3 that
depends on m, and m is the number of lifts of Step 6, a power of 2. Every prime factor of q₁ is
therefore 2, 3 or a prime factor of q₀, and 2 and 3 divide q₀ because q₀ is a multiple of
18480 = 2⁴·3·5·7·11. The cyclotomic polynomial of order
q₁ stays irreducible over K (`irreducible_cyclotomic`), so Gal(E/K) is (ℤ/q₁)ˣ, and its f = φ(q₁)
elements index the infinite places of E.

The data hold three integer scales x, x₁ and b, with x^(10⁶) ≤ x₁ and x₁^(10⁶) ≤ b, and a = x·b. The
set Φ_a of a-places holds the places ≡ 1 mod q₀, the kernel of the reduction from (ℤ/q₁)ˣ onto
(ℤ/q₀)ˣ. Because q₁ and q₀ have the same prime factors, φ(q₁) = (q₁/q₀)·φ(q₀), and
#Φ_a = q₁/q₀ (`card_aPlaces`), so f = φ(q₀)·#Φ_a. The set Φ_b of b-places is a set of places
≡ −1 mod q₀ with #Φ_a ≤ #Φ_b·log b. The data also put a sparseness condition on Φ_b, which this
report does not use. The weight κ(τ) of a place τ is b on Φ_b and a/x₁ elsewhere. The data make
q₁·x₁ divide b (`dvd_natB`), so every weight is a natural number. For a number
y > 0 the prime sum of a place τ is

    s_fin(y, τ) = Σ_{1 ≤ n ≤ a} Λ(n)(1 − (n/d))·max(y/n − κ(−nτ), 0).

Here −nτ is the place of the class −n times τ when n is prime to q₁, and −nτ is τ itself
otherwise. When −nτ is a b-place, its weight is b = a/x, and the term of s_fin(a, τ) is
a·Λ(n)(1 − (n/d))(1/n − 1/x) for n ≤ x, which is a times a term of the sum in R_{q₀} of Step 2. An
n ≡ 1 mod q₀ is prime to q₀ and so prime to q₁. For each n, `card_filter_mem_bPlaces` counts the
a-places τ for which −nτ is a b-place, and there are #Φ_b of them when n ≡ 1 mod q₀ and none
otherwise. The proof writes each term as its value at the weight a/x₁ plus a correction at the
b-places. The values at a/x₁ form the sum of R₁ up to x₁, and by the count the corrections form
#Φ_b times the sum of R_{q₀} up to x less the same sum up to x₁. The result is
`sum_aPlaces_primeSum`, which gives the sum of s_fin(a, τ) over the a-places as

    a·( #Φ_b·(R_{q₀}(x) − R_{q₀}(x₁)) + #Φ_a·R₁(x₁) ) + a·( #Φ_a·(log x₁ + c₁) + #Φ_b·(log x − log x₁)/φ(q₀) ).

Here c₁ = Re L′/L(1, χ_K) − γ − 1 is the constant that R₁ subtracts. The second bracket holds the
main terms that the remainders subtract, and the constant of R_{q₀} cancels between x and x₁.

Let s_main = a·(log(a/κ̄) + c₁) be the expected value of each s_fin(a, τ), where log κ̄ is the mean
of log κ over all f places. The weights are a/x on the #Φ_b b-places and a/x₁ on the other places,
so log(a/κ̄) = log x₁ + (#Φ_b/f)·(log x − log x₁). Since f = φ(q₀)·#Φ_a, the product #Φ_a·s_main
equals a times the second bracket (`card_aPlaces_mul_mainPrimeSum`). The total remainder rem is the
sum of s_fin(a, τ) − s_main over the a-places, so `totalRemainder_eq` gives

    rem = a·( #Φ_b·(R_{q₀}(x) − R_{q₀}(x₁)) + #Φ_a·R₁(x₁) ).

### Step 5

The old step bounds the slope of one lattice from above by the divisibility inequality `DIV` and
from below by the slope inequality `SlopeIneq`. The new main inequality bounds one covolume,
corrected by an index, from both sides. The target is the space `D.targetForms` of good forms on
the unitary group of a hermitian space Y₀ over E of rank r (Step 6), and dim is its dimension. A
fixed linear map 𝔭 sends the ramified source forms on the space X₀ of Step 6 to the target. By the
definition `normalizedPoincare` it is c_B·c⁻¹·#Ḡ·e₀∘𝒫. Here 𝒫 is the Poincaré map from forms on
X₀ to forms on Y₀, e₀ is the projection to the target forms, c is the constant of the seesaw
identity of Step 6 for a fixed linear form and point, #Ḡ is the order of a finite group that acts on
the forms on Y₀, and c_B is a rational factor that the last paragraph of this step describes.
Theorem B gives a finite set of translates g𝔭 whose images together have dimension at least
(1 − 4/b²)·dim. A source form h is short when it is integral and, for each translate g𝔭, the image
Θ₁(g𝔭h) has squared length at most exp(H) at every conjugate. Here Θ₁ is the chain of lifts
Y₀ → … → Y_m of Step 6 with the trivial twist, and

    H = main amount − m·rem + f·a·log⁴ b.

Here rem is the total remainder of Step 4, f is the number of infinite places of E, and Step 7
defines the main amount. Theorem A (a) says that the short forms span all ramified source forms.
Together the two theorems give u linearly independent images of short forms, with
dim ≥ u ≥ (1 − 4/b²)·dim ≥ dim/2. Hadamard's bound (`covolumeLe_of_normSqAt_le`) bounds the
logarithm of the squared covolume of their lifts by V = u·H. Their index measures how far the
lifts are from integral. It is a sum of e_ℓ·log ℓ over the primes ℓ, where e_ℓ bounds the valuation
of the determinant of an integral matrix that makes the lifts of the family integral at ℓ
(`TwistedLattice.IndexLe`). Theorem A (b) bounds the index by δ = dim·I, where
I = 10·log(1 + 2b²)·f·a·log³ b. Theorem C bounds (V + 2δ)/dim from
below by the main amount less 3·f·a·log⁴ b. Up to the errors the opening comment of
`New/Reduction/MainInequality` writes the two sides as

    main amount ≤ (V + 2δ)/dim ≤ main amount − (u/dim)·m·rem.

The proof of `star_inequality` cancels the main amount in four moves.

1. Theorem C gives dim·(main amount − 3·f·a·log⁴ b) ≤ u·H + 2·dim·I. With the value of H this
   rearranges to u·m·rem ≤ u·(main amount + f·a·log⁴ b) − dim·(main amount − 3·f·a·log⁴ b)
   + 2·dim·I.
2. Because u ≤ dim and the main amount is nonnegative (`mainAmount_nonneg`),
   u·(main amount + f·a·log⁴ b) is at most dim·(main amount + f·a·log⁴ b). Inserting this bound
   gives u·m·rem ≤ dim·(4·f·a·log⁴ b + 2I), and the main amount is gone.
3. The right side is nonnegative and dim ≤ 2u, so u·m·rem ≤ 2u·(4·f·a·log⁴ b + 2I). Theorem B
   also gives dim > 0, so u ≥ dim/2 > 0, and dividing by u gives m·rem ≤ 8·f·a·log⁴ b + 4I. Since log(1 + 2b²) is about 2·log b, the right side is
   about 88·f·a·log⁴ b.
4. The data take log b so large (the field `constantBound_le`) that the right side is at most
   f·a·log⁵ b (`le_of_hasLogBound`). The result m·rem ≤ f·a·log⁵ b is the statement of
   `star_inequality`.

The factor c_B (`invGainFactor`) carries the divisibility. It is the product of ℓ^(−g_ℓ) over the
primes ℓ < x₁ that do not split in K, times a power of the level N, the prime of the data that
Step 6 introduces. Here g_ℓ = ⌊gain_ℓ − err_ℓ⌋
(`gainExponent`), where gain_ℓ is the divisibility asked of the chain at ℓ and err_ℓ is an allowed
loss. The bound for the size of the chain in Step 7 contains the term 2·Σ gain_ℓ·log ℓ. Because 𝔭
carries the factor c_B, the squared lengths of the lifts carry c_B², and the opening comment of
`New/Reduction/MainInequality` lists the gain term as cancelled against log c_B in Theorem A (a).
This is why H holds no gain term. This comparison did not check which term of Step 7 the power
of N in c_B answers. The opening comment of `New/Reduction/ShortAndEnough` says that
c_B trades divisibility for archimedean size, and in this form the old divisibility inequality
`DIV` returns.

### Step 6

The ranks are the same in both versions. The spaces X_j have rank n_j = k + j(t + 1), where
k = r + 1 − m, t = 5r and r is the rank of the space Y₀ below. A second chain of hermitian spaces
Y₀ → Y₁ → … → Y_m runs beside the first, with Y_j of rank r + j·t. By `GUIDE.md` its first space Y₀
is X₀ plus ϱ hyperbolic planes and one line of norm −N, where m = 2ϱ + 2 and N is the prime of the
data that Step 7 calls the level. Its last space Y_m lies in X_m and has rank r + m·t = n_m − 1. The
commentary says that the first m − 2 kernels are composed one after the other and the last two
inside a finite sum. In the new definition `compositeLift` the chain X₀ → … → X_m is grouped into
m/2 double lifts X_{2i} → X_{2i+1} → X_{2i+2}, each double lift is glued (`doubleLiftGluing`), and
the result is restricted to Y_m. The data take m = 2^(e+1) for a natural number e
(`exists_m_eq_two_pow`), so m is even and the pairs fill the chain.

In the old text a datum carries a family of words, and each word gives one linear map into a
lattice. The commentary does not record how the pairing of a word is tied to the linear map of that
word. The new edition states the tie as the seesaw identity `seesaw_identity`. A twist in this
identity is an automorphic character of U(1) of weight 0, tamely ramified on a finite set of places
away from the levels, as `GUIDE.md` defines it. It differs from the quadratic twists of Step 3. The
identity takes a linear form on the values of forms on X₀ and an archimedean point of the unitary
group of Y₀, and the Poincaré map 𝒫 depends on both. The identity holds for each twist ξ on the
ramified source forms on X₀. It gives a chain datum Ψ for ξ,
a finite combination of translates that the gluing uses. It says that the Poincaré map 𝒫 followed
by the chain of lifts Y₀ → Y₁ → … → Y_m taken with ξ equals c times the composite lift taken with ξ
and Ψ, and one number c ≠ 0 serves all twists. `GUIDE.md` adds that the theorem does not say that
the right side is nonzero, so the identity alone does not show that the chain of lifts is nonzero
on any source form.

### Step 7

The old main term holds a_T·log a_T − a_T − a_T·`logOm` for each lift and each of the places that
the old record calls top places, where a_T is the top weight at that place. In the old record a
number `T u` plays the part of a level, and the main term subtracts a_T·log `T u` at each top place.
The condition `Count5` bounds log `T u` from below by the sum over the lifts of the mean over the
places of log(w·v/π), plus m times a number `lg`, less an error. Here w is the weight of the old
record at a lift and a place, and v is one positive number of the record. The lower bound for
log `T u` turns the main term into an upper bound. In it the logarithms of π/v from `logOm` and
from `Count5` cancel, as the commentary says, and the main term is at most `Main` less m times the
sum of the a_T·`lg`, plus an error. The number `Main` holds
a_T·(log a_T − 1 − γ + `LpL` − λ) for each lift and each top place. Here `LpL` is the real part of
L′/L(1) for the quadratic character, and λ is the mean of log w over the places, which the
commentary writes ℓ.

In the new edition `chainSize_sub_le` bounds the main term of the size of the chain of m lifts,
which is

    m·( #Φ_a·s_∞(a) + k·Σ_τ s_∞(κ(τ)) ).

Here s_∞(j) = log j! + j·log(M/Ω) is the size of a derivative of order j, k is the rank of X₀, and
the sum runs over all places. The principal level M = p₀·p₁ is the product of two primes of the
data, each between b¹⁰ and b¹¹, so log M ≤ 22·log b. The constant Ω is `P.bigOmega s`, where s
is the exponent with 2^s = m²² that fixes E, and it equals exp(γ − Re L′/L(1, χ_K))·2π/rd_E, where
rd_E is the root discriminant of E. The old `logOm` is
γ + log(π/v) − `LpL`, and log Ω has the same form with rd_E/2 in place of v. This comparison did not
check that the old v is half a root discriminant.

The second part of this main term pairs with the prime sums s_fin(κ(τ), τ) of Step 4, which measure
the guaranteed divisibility. The main amount is m·k·Σ_τ (s_∞(κ(τ)) − s_fin(κ(τ), τ)), and the sum
without the factor m·k is the direction amount. This report reads the first part as the counterpart
of the old main term, with the a-places in the role of the top places and the long order a = x·b in
the role of the top weight a_T.

At one a-place Stirling's formula gives s_∞(a) = a·log a − a + a·log M − a·log Ω + O(log a). If the
old v equals rd_E/2, so that log Ω = `logOm`, then before the level enters the new size exceeds the
old term at the same weight by a·log M, up to O(log a). The restriction of the chain to Y_m saves
a·log N at each a-place (`chainSize_sub_le`), where the level N is a prime of the data, as the old
main term subtracts a_T·log `T u`. The new proof bounds the excess of one lift over the expected
value s_main of Step 4 by

    s_∞(a) − s_main ≤ a·log(κ̄·M·rd_E/2π) + 1 + (log a)/2

(`jetSize_sub_mainPrimeSum_le`). The data take log N ≥ m·log κ̄ + (m − 1)·log(M·rd_E/2π) −
(15/2)·log b. In m·(s_∞(a) − s_main) − a·log N the term m·a·log κ̄ cancels, and m − 1 of the m
copies of a·log(M·rd_E/2π) cancel. The difference is therefore at most
m·(1 + (log a)/2) + a·(log(M·rd_E/2π) + (15/2)·log b). The data give m·(1 + (log a)/2) ≤ a·log b and
log(M·rd_E/2π) ≤ 23·log b, so the difference is at most 32·a·log b
(`mul_jetSize_sub_mainPrimeSum_sub_le`).

After the level, each a-place therefore leaves m·s_main up to 32·a·log b. With the value of c₁ from
Step 4,

    s_main = a·(log a − 1 − γ + Re L′/L(1, χ_K) − log κ̄).

This is the old expression a_T·(log a_T − 1 − γ + `LpL` − λ) term by term, with log κ̄, the mean of
the logarithms of the weights, in place of λ. The verdict reads the same main term after the level
for this reason, and it notes that this comparison did not check what the old term m·`lg`
corresponds to.

The bound of `chainSize_sub_le` follows from two facts. The identity
`mainAmount_sub_add_two_mul_sum_gain` states that

    main amount − m·rem + 2·Σ_ℓ gain_ℓ·log ℓ = m·#Φ_a·s_main + m·k·Σ_τ s_∞(κ(τ)),

where ℓ runs over the primes below x₁ that do not split in K. The bound on the excess, summed over
the #Φ_a a-places, gives at most 32·#Φ_a·a·log b ≤ 32·f·a·log b (`card_aPlaces_mul_excess_le`).
Together they give

    main term of the size − #Φ_a·a·log N ≤ main amount − m·rem + 2·Σ_ℓ gain_ℓ·log ℓ + 32·f·a·log b.

The gain term is the one that c_B removes in Step 5, and the rest has the form of the bound H of
Step 5. This comparison did not read how Theorem A (a) passes from this bound to H.

In the old text interlacing weights and a hook product bound a sum over the weights of one lift by
a_T·log a_T − a_T plus an error, and the new proof uses Stirling's formula for log a! in that place.
This comparison did not look at how the old sum relates to log a!. The size of the composite lift
comes from the bounds for the single lifts (`weylNormSq_restrictedChain_le` in
`New/UpperBound/Size/ArchimedeanSize`). `GUIDE.md` places `New/OneLift` and `New/Determinant` under
the lower bound. In
`New` the word hook occurs only in files of the lower bound, nine in `New/OneLift` and one in
`New/Determinant/AuxiliaryForms`. Interlacing occurs in files of the upper bound, two in
`New/UpperBound/ElementaryDivisors` and three in `New/UpperBound/Objects`, and in one file of
`New/Determinant/AuxiliaryForms`. The hook product of the old upper bound thus has no namesake in
the files of the new upper bound, which fits the verdict of another method.

### Step 8

The commentary calls a hypothesis of a theorem a premise, and a premise is supplied when a call of
the theorem passes a proof of it. The old step applies a general statement about several maps into
one lattice, with a family of many words, and a premise says that such families exist. The
commentary did not follow where the old text proves this premise. The new Theorem C,
`integral_forms_long`, bounds dim·(main amount − 3·f·a·log⁴ b) by V + 2δ, the covolume bound plus
twice the index bound of Step 5. It rests on `covolume_add_index_nonneg`, the product formula for a
Gram determinant, which takes one twist ξ_ι for each prime ℓ and each isomorphism ι : ℂ ≃ ℚ̄_ℓ. The
premises of `covolume_add_index_nonneg` include auxiliary forms z that complete the u forms of Step 5 to a basis,
the injectivity of the untwisted lift, and a bound for the height of Z(1)/Z(ξ_ι), a ratio of chain
determinants. The maps of the new twisted lattice are indexed by the twists of Step 6.
`exists_isRegularFamily` in `New/Congruences/FitTwistsExist` proves that a regular family of
twists exists, with one twist for each prime ℓ and each such ι. The opening comment of that file
calls the theorem the conclusion of the Selmer group argument, whose parts lie in the folders of
`New/Congruences`, among them `New/Congruences/Selmer`.

The proof of Theorem C passes this family to the product formula. `integral_forms_long` calls
`integral_forms_long_with_completion_cost`, which takes its twists from
`exists_hasSmallRatios_heightLe_liftDeterminant_div`. That theorem takes a regular family θ from
`exists_isRegularFamily` and derives from its regularity a bound for the heights of the single-lift
ratios Z_j(1)/Z_j(ξ_ι^j), where ξ_ι = θ(ι). The twists ξ_ι then enter `covolume_add_index_nonneg`,
together with the bound for the height of Z(1)/Z(ξ_ι) that follows from the single-lift bounds
(`heightLe_chainDeterminant_one_div`). This proved existence is the new counterpart of the old
premise. The commentary says that the old premise is proved and did not follow where, so the
verdict records only that this report located the proof in the new edition. This comparison did not compare the two
arguments and did not settle whether the words of the old datum correspond to the twists.

### Step 9

The old step leaves error terms of about x/m and about m and takes m between x^(1/2 − ε) and
x^(1/2 + ε/2). In the new edition `Data.primeRemainder_le` divides `star_inequality` by
m·a·#Φ_b. It inserts the formula for rem from Step 4 and uses f = φ(q₀)·#Φ_a and
#Φ_a ≤ #Φ_b·log b. The result is

    R_{q₀}(x) ≤ φ(q₀)·log⁶ b/m + |R_{q₀}(x₁)| + log b·|R₁(x₁)|.

Only the first term depends on m, and it falls as m grows. The data take m in [√x, 2√x]. For
0 < ε < 1/100 the lemma `eventually_primeRemainder_natCast_le` chooses data with log b ≤ 2x^ε and
log x₁ ≥ x^(ε/12). The prime number theorem in the form `eventually_abs_primeRemainder_le` gives
|R_Q(y)| ≤ (log y)^(−B) for every natural number B and all large y. With log x₁ ≥ x^(ε/12) and
B ≥ 24/ε the values |R_{q₀}(x₁)| and |R₁(x₁)| are then at most x^(−2)
(`eventually_abs_primeRemainder_exp_le`). Of the window for m the lemma uses only
√x ≤ m. The three terms add up to at most (64·φ(q₀) + 3)·x^(−1/2 + 6ε) for all large integers x.
These lemmas hold for every prime d ≡ q₀/2 − 1 mod q₀, which is the class of Step 3.

The theorem `eventually_primeRemainder_le_mul_rpow` passes to real numbers. For a given ε > 0 it
applies the integer bound with ε′ = min(ε/6, 1/200) in place of ε, so that 6ε′ ≤ ε, and it writes
θ′ = −1/2 + 6ε′. For y ≥ 2 it writes R_{q₀}(y) as R_{q₀}(⌊y⌋) plus the difference
R_{q₀}(y) − R_{q₀}(⌊y⌋), which is at most 26/y (`primeRemainder_sub_primeRemainder_floor_le`).
With ⌊y⌋^θ′ ≤ 2·y^θ′ and 26/y ≤ 26·y^θ′ the two parts add up to at most
(2·(64·φ(q₀) + 3) + 26)·y^θ′ = (128·φ(q₀) + 32)·y^θ′. This is at most
(128·φ(q₀) + 32)·y^(−1/2 + ε) for all large real y. With ε = β − 1/2 this is the hypothesis
R_{q₀}(x) ≤ A·x^(β − 1) of the criterion of Step 2. This comparison did not look for where the
upper end 2√x is used.

## The parts that supply the premises

In the old text further parts of the proof supply the premises of the route of the nine steps, in
the sense of Step 8. One part builds a record of 46 fields, five of data and 41 conditions on the
families of data, where a family holds a datum for every large x and every index of a set. One of
the conditions says that the chains of lifts exist. The new record `Data` has 42 fields, 15 of data
and 27 conditions. The data are numbers, a set of places, a weight on the places, primes and two
integers of the field. The 27 conditions relate these data to each other, for example as bounds,
congruences and primality, and the record holds no forms or lifts. `eventually_exists_data` in
`New/Reduction/Data/Existence` builds such data for every large x. The forms, the lifts and their
bounds are definitions and theorems in the folders that `GUIDE.md` lists. The old part `VWin` of
the proof bounds lengths of Galois cohomology groups, and the new parts on the same subject are the
Selmer bounds of `New/Congruences/Selmer` and the theorem `exists_length_shaOdd_le` of `Lib`. The
old part `Row` proves the existence of Galois representations, and the new part on the same subject
is `GaloisRep.sphericalCompat_std` of `Lib/GaloisRep`. This comparison did not compare the
statements of these parts.

## Names that change

A token search of the new edition gave these counts. A name counts as present when it occurs
anywhere in the text, comments included.

- The commentary names 347 code-like identifiers in backticks. Twenty of them occur in the new
  edition. The five theorem names and `RiemannHypothesis` keep their meaning, and `Quot.sound` and
  `Classical.choice` are names of Lean. `HCParam` names a Harish-Chandra parameter with another
  definition. The other eleven are common words or names of Lean, such as `Data`, `Main`, `Row`
  and `True`.
- `route.json` lists six stations, the points of the route that the route view shows, and each
  station names one module of the old text. The route view is a page of the explorer, the web view
  of the proof that this fork builds in `verification/explorer`, and it draws `route.json`. Four of
  the six modules lie in the folder `Development` and two in the folder `Formalism`. The new
  edition has neither folder, so no file of the new edition has the path of any of the six modules.
- Of the 109 Lean names in the 43 terms of `route.json`, only `LFunction_ne_zero_of_half_lt_re`
  occurs with the same meaning. The other nine matches are words in comments or names of other
  objects, such as `Gm`, which in the new edition is the multiplicative group as a functor.

The steps above pair the following old names of the commentary with new names by the role they
play. In the commentary `zero_free_all_of_green_v_win` is the old theorem that gives the
zero-freeness of step 1 from three premises. The commentary's `kerPlace` is the sum of y·log y − y
over the weights of a lift less the sum of the weights times `logOm`, and its `hU` sums `kerPlace` less a
hook term `logHook` over the places and the m lifts. The pairing of `logOm` assumes that the old v
is rd_E/2, which Step 7 left unchecked.

| Old name | New counterpart |
|---|---|
| `zero_free_all_of_green_v_win` | `grh` |
| `Gm` | `primeRemainder` (R_Q) |
| `ASK` | `D.primeSum`, `D.totalRemainder` |
| `DIV` | `D.gain`, `D.invGainFactor`, Theorem A |
| `SlopeIneq` | Theorem C, `TwistedLattice.covolume_add_index_nonneg` |
| `logOm` | log `P.bigOmega s` |
| `kerPlace`, `hU` | `D.jetSize`, `D.directionAmount`, `D.mainAmount` |
| the record of 46 fields | `Data` |

## What this means for the commentary and the route view

The commentary, the list of claims and `route.json` stay a reading of 611ce0b6301. As a reading of
the new edition, step 1 carries over. The five theorems keep their names, and the statement that
they rest on is now called `grh`. Step 2 keeps Landau's lemma and changes the prime sum and the form
of the bound, from a bound on intervals to an eventual bound. Steps 3 and 9 describe arguments that
the new edition replaces. The choice of q′ and d′ with wanted and unwanted characters becomes the
choice of one d with a zero-free box for the quadratic twists. The window of m with two error terms
becomes the window [√x, 2√x], of which the lemma `eventually_primeRemainder_natCast_le` uses only
the lower end, and only one term of the bound depends on m. Steps 4 and 7 keep their roles and reach
their results by other arguments, a count of places and Stirling's formula for log a! with a level
that absorbs the extra terms a·log M up to an error of order a·log b. For Step 7 the old term
m·`lg` has no checked counterpart. Step 5 keeps its idea, an
upper and a lower bound for one quantity, with a covolume and an index in place of a slope. Step 6
keeps its spaces and ranks and glues the lifts in pairs. Step 8 keeps its role, and this report did
not compare its arguments. The route view shows Lean names and modules of 611ce0b6301 and can stay a
view of that commit. A route view of the new edition needs a reading of the nine steps in the new
edition at the depth of the commentary, and this report gives only the comparison.
