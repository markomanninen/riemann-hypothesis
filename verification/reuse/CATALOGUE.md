# The theorems in library terms that have large proofs

The Lean source in [`src`](../../src) holds 212 theorems whose statements are written with
constants of Mathlib and Lean alone and whose proofs rest on more than 100 declarations of the
project. They state 159 different statements, and this catalogue says for each of the 159 what
it states and which published result it is. Two readers read each statement, and a third run,
the check, compared their readings with the Lean text. The check sorts the 159 into three
kinds. It takes 32 for named theorems, which are results that textbooks state under a name or
as a main theorem, 61 for standard facts of textbooks and 66 for technical steps of a larger
proof. Three of the named theorems are `riemannHypothesis` and `rhOfAll`, which state the
Riemann hypothesis, and `critAll`, which states its form for Dirichlet L-functions. The Lean
source claims to prove all three. The other 29 named theorems include the Kronecker-Weber
theorem in its global and its local form, Stein factorisation, Zariski's connectedness theorem,
the purity of the branch locus of Zariski and Nagata, Borel's finiteness of class numbers,
Chevalley's theorem on units, the product formula, the addition theorem of the Weierstrass
℘-function and Hecke's continuation of the L-functions of ideal characters.

A language model, Claude, made the two readings and the check on 25 November 2026, each as a
separate run. The two readers and the check named each published result from the model's own
knowledge of the literature and opened no source. No mathematician has checked the catalogue.
A name or a relation given here is a pointer for a specialist, who can settle it from the Lean
statement that the entry describes.

A statement of this catalogue mentions no constant of the project, so its meaning depends on
the definitions of Mathlib alone. A reader who trusts those definitions can judge from the
statement what is claimed. [`README.md`](README.md) describes how such a theorem can be
imported without the rest of the proof. [`AUDIT.md`](AUDIT.md) compares 70 propositions that
the source itself labels as results from the literature with the published theorems that they
are named after.

[`MATHLIB.md`](MATHLIB.md) tests whether Mathlib already holds a statement of this catalogue,
as one theorem of its own or within one run of a proof-search tactic. Four proof-search tactics
of Lean, run with Mathlib and without the project, proved none of the 159 statements. They
proved 8 of the 2,655 statements in library terms whose proofs rest on 11 to 100 declarations.
The same document counts the modules of the project that a Lean file has to load in order to
use each statement.

## Words used here

- A statement is in library terms when it mentions no constant of the project. A theorem rests
  on the declarations of the project that its statement and its proof use, directly or through
  other declarations. [`README.md`](README.md) gives both rules in full.
- The 159 statements come from the 212 theorems in this way. The work of
  [`../redundancy`](../redundancy/README.md) had Lean compare the statements of theorems, and
  53 of the 212 theorems state what one other of them states. The catalogue keeps one theorem
  of each such pair, the one with the larger proof, and its entry names the other one.
- The kind of a statement is one of three. A named theorem is a result that textbooks state
  under a name or as a main theorem. A standard fact is one that a textbook states as a lemma,
  a proposition or an exercise. A technical step is a statement shaped for one use inside a
  larger proof.
- The relation of a statement to the published result is one of six words. Same means that
  the two say the same up to the way of writing. Special case means that the Lean statement is
  the published result for a narrower kind of object. Weaker means that the Lean statement
  follows from the published result and claims less in another way, for example one direction
  of an equivalence. Stronger means that it claims more, different that it is another
  statement, and none that the reader named no published result.
- The five theorems are the theorems of [`Main.lean`](../../src/Main.lean), which state the
  Riemann hypothesis and its form for Dirichlet L-functions. `riemannHypothesis` is one of
  them. They use a theorem when a chain of mentions leads from one of them to it.
- A statement is empty when a hypothesis is impossible to meet or when the conclusion follows
  at once from the hypotheses.

## What the catalogue found

| Kind | First reader | Second reader | Check |
|---|---:|---:|---:|
| named theorem | 31 | 36 | 32 |
| standard fact | 61 | 62 | 61 |
| technical step | 67 | 61 | 66 |

The two readers and the check give the same kind for 142 of the 159 statements, and the same
kind and the same relation for 108. The next table gives the relations of the check within
each kind.

| Relation by the check | Named theorems | Standard facts | Technical steps |
|---|---:|---:|---:|
| same | 16 | 14 | 2 |
| special case | 10 | 15 | 11 |
| weaker | 6 | 28 | 19 |
| stronger | 0 | 3 | 2 |
| none | 0 | 1 | 32 |

The check found one error in an account of the first reader and two in accounts of the second
reader. An entry prints the error of the first reader, and `catalogue.json` holds the other
two. For 104 statements the check wrote that it found no emptiness, and for 55 it added a
remark. In 46 of the 55 remarks the check again finds none and names a case that meets the
hypotheses or a part of the statement that is immediate. No remark says that a whole statement
is empty. The remarks on statements 69, 80, 81 and 149 say that a statement has content for a
part of its cases only, or that a condition in it does no work, and the entries print them.

A name of the source tells little about a statement. The theorem
`finiteRing_sq_sub_mul_sq_eq_of_card`, statement 57, states the purity of the branch locus for
a finite normal extension of a regular local ring, and the theorem `kwHom`, statement 7, states
the Kronecker-Weber theorem. The theorem `gaussian_fourier_self_dual_adelic`, statement 22,
states an asymptotic count of vectors of a quadratic form, for which the check knows no
published result.

The five theorems use 156 of the 159 statements. The other three are statement 1, `critAll`,
and statement 3, `rhOfAll`, which lie in the library `Supplements` outside `Main.lean`, and
statement 81, `weber_congruences`.

## How the catalogue was made

1. [`catalogue.py`](catalogue.py) took the theorems in library terms whose proofs rest on more
   than 100 declarations from the list of `statements.py`, kept one for each statement and
   wrote a dossier for each. A dossier holds the whole Lean statement with the `variable`
   lines in scope. The 159 dossiers hold 139,105 characters.
2. A first reader wrote, from the dossier alone, what the statement claims and the statement in
   ordinary notation. It then named the published result from its own knowledge with one
   reference, judged the relation, gave the kind and looked for emptiness.
3. A second reader did the same from the same dossier without seeing the first.
4. A check compared both accounts with the Lean text and gave its own name, relation and kind.

The first reader, the second reader and the check are runs of the command line tool Claude
Code. The 159 dossiers were split into seven batches of twenty and one of nineteen, in the order
of the size of the proofs. Each run was started in a folder that held only the dossiers of one batch and, for the
check, the two readings of that batch. The briefs of the three roles are in
[`briefs/`](briefs/), with names that begin with `catalogue`.

## Limits

- The two readers and the check are the same language model, so they can share a blind spot
  that the check does not find. A model of another maker has not repeated the check.
- The published results come from the model's memory of the literature. The reference that an
  entry names was not opened.
- A name of Mathlib is taken with the meaning that Mathlib gives it, and no definition of
  Mathlib was opened.
- The catalogue is of statements. The compiled files that count the declarations come from the
  build cache of the repository. No proof was read, with one exception. Statement 142 is an
  instance, and its dossier shows the value of the instance, which is its proof.
- The limit of 100 declarations is a choice. Another 79,053 theorems in library terms have
  smaller proofs and were not read.
- The three kinds are a judgement. The readers and the check differ on the kind of 17
  statements.

## Files

| File | Content |
|---|---|
| `catalogue.py` | writes the dossiers into `data/catalogue`, which git ignores, collects the answers and writes the entries below |
| `briefs/` | the briefs of the first reader, the second reader and the check |
| `catalogue.json` | for each of the 159 statements the two readings and the answer of the check |

## How to read the tables and the entries

The three tables below list the statements by the kind that the check gave, each in the order
of the size of the proofs. The column Known as gives the name that the check gave to the
published result, and a cell that ends in three dots is cut. An entry prints the first reader's
account of the Lean statement and its form in ordinary notation, the kind and the name by the
first reader with its reference, the kind by the second reader, the kind, the name and the
relation by the check with the relations of the two readers, a note of the check, its remark on
emptiness and the errors that it found in the first reader's account.

<!-- entries -->

## Named theorems

The check puts 32 statements in this kind.

| No. | Theorem | Known as, by the check | Relation | The proof rests on |
|---:|---|---|---|---:|
| 1 | `critAll` | The Generalized Riemann Hypothesis for Dirichlet L-functions, an open conjecture with no … | same | 800,343 |
| 2 | `riemannHypothesis` | The Riemann Hypothesis, an open conjecture and one of the Millennium Prize Problems, with … | same | 800,342 |
| 3 | `rhOfAll` | The Riemann Hypothesis, an open conjecture and one of the Millennium Prize Problems, with … | same | 800,341 |
| 7 | `kwHom` | The Kronecker–Weber theorem | same | 4,902 |
| 8 | `kw` | The Kronecker–Weber theorem | same | 4,901 |
| 9 | `stein_factorisation_connected_fibres` | The Stein factorization theorem (EGA III 4.3.3, Hartshorne III.11.5) | same | 2,002 |
| 10 | `isConnected_closed` | Zariski's connectedness theorem, for a noetherian local base and its closed fibre | special case | 1,586 |
| 14 | `exists_le_adjoin_rootsOfUnity` | The local Kronecker–Weber theorem for ℚ_p | same | 1,460 |
| 17 | `zariski_connectedness_isPreconnected_fibre` | Zariski's connectedness theorem (EGA III 4.3.1, Hartshorne III.11.3) | same | 905 |
| 20 | `zariskiConnectedness_isPreconnected_fibre_affine` | Zariski's connectedness theorem, over an affine noetherian base | special case | 891 |
| 26 | `classNumber_finite_integralLevel_closedSubgroupGL` | Borel's finiteness of the class number of a linear algebraic group over a number field … | same | 530 |
| 36 | `congr_of_det_norm` | Landherr's theorem that nondegenerate hermitian forms over a quadratic extension of … | special case | 301 |
| 45 | `etale_atPrime_of_regular_of_isIntegrallyClosedIn` | Zariski–Nagata purity of the branch locus | same | 254 |
| 49 | `exists_places` | Chevalley's theorem that every subgroup of finite index in the S-unit group of a number … | special case | 251 |
| 50 | `etale_integralClosure_of_isArtinianRing` | Zariski–Nagata purity of the branch locus | same | 249 |
| 54 | `exists_places_of_fg` | Chevalley's theorem that every subgroup of finite index in a finitely generated subgroup … | weaker | 245 |
| 56 | `etale_of_etale_height_one_of_regularLocalRing` | Zariski–Nagata purity of the branch locus | same | 243 |
| 57 | `finiteRing_sq_sub_mul_sq_eq_of_card` | Zariski–Nagata purity of the branch locus | same | 241 |
| 59 | `exists_coboundary_of_fraction_cocycle_homogeneous_ideal` | Serre's vanishing theorem, here for H¹ of the twists of the structure sheaf of the closed … | special case | 225 |
| 62 | `adicCompletion_isDomain_and_isIntegrallyClosed` | Zariski's theorem on analytic normality in the form of Nagata and Grothendieck (EGA IV … | special case | 220 |
| 65 | `free_of_etale_on_punctured_spectrum` | The Zariski–Nagata purity of the branch locus for a finite normal extension of a regular … | special case | 209 |
| 78 | `exists_idele_ne_algebraMap_mul_norm_of_not_isSquare` | The first fundamental inequality of global class field theory for the quadratic extension … | special case | 170 |
| 95 | `dblA` | Duplication formula for the Weierstrass ℘-function | same | 152 |
| 100 | `P_add` | Addition theorem for the Weierstrass ℘-function | same | 148 |
| 104 | `exists_continuous_normCharLFunction_ne_zero_one` | Nonvanishing at s = 1 of the L-function of a nontrivial ray class character (Hecke, … | weaker | 142 |
| 108 | `rational_units_haar_character_one` | Product formula ∏_v \|a\|_v = 1 for a ∈ Fˣ (Artin and Whaples), in Weil's form that the … | same | 135 |
| 118 | `idealCharacterL_continuation_ne_zero_one` | Hecke's theorem on the analytic continuation of L-functions of nontrivial … | weaker | 126 |
| 126 | `invariant_isAlgebraic` | Algebraicity of singular moduli, the part of the theory of complex multiplication that … | special case | 120 |
| 138 | `exists_entire_sub_one_mul_euler_exp_ne_zero_one` | Hecke's theorem that the Dedekind zeta function continues meromorphically to ℂ with a … | weaker | 110 |
| 145 | `isPreconnected_points_over` | Connectedness of an irreducible complex algebraic variety in the classical topology … | special case | 108 |
| 148 | `dedekindZeta_eulerProduct_mul_sub_one_entire` | Hecke's theorem on the analytic continuation of the Dedekind zeta function to a … | weaker | 106 |
| 154 | `idealCharacter_LSeries_continuation` | Hecke's theorem on the analytic continuation of the L-functions of Hecke characters … | weaker | 103 |

## Standard facts

The check puts 61 statements in this kind.

| No. | Theorem | Known as, by the check | Relation | The proof rests on |
|---:|---|---|---|---:|
| 4 | `exists_prime` | The theorem that every ideal class of a number field contains infinitely many prime … | special case | 4,930 |
| 5 | `exists_principal` | The theorem that every ideal class of a number field contains infinitely many prime … | special case | 4,928 |
| 11 | `finite_appTop_restrict` | The coherence of π_*O_Y for a proper morphism π to a locally noetherian scheme, the … | special case | 1,499 |
| 12 | `finite_app_of_isProper` | The coherence of g_*O_X for a proper morphism g, the degree-zero case for the structure … | special case | 1,493 |
| 13 | `exists_zmod_char_not_norm` | The half of the nondegeneracy of the local duality pairing between H^1(F, ℤ/nℤ) and … | weaker | 1,468 |
| 16 | `isProper_of_properSpecialFibre_universallyOpen_dvr` | A properness criterion through the special fibre over a discrete valuation ring, the case … | special case | 910 |
| 21 | `isPreconnected_closedFibre` | The local form of Zariski's connectedness theorem, by which a connected scheme proper … | same | 882 |
| 23 | `eq_top_of_forall_exists_norm` | The corollary of the norm index equality of local class field theory, by which the index … | weaker | 791 |
| 29 | `exists_finite_etale_representing_clopen_subschemes` | Representability of the Weil restriction along a finite étale G → S of the constant … | special case | 388 |
| 30 | `kummer_cocycle_norm_criterion` | The norm criterion for cyclic algebras in the direction that a norm U from the cyclic … | weaker | 381 |
| 31 | `exists_lift_of_norm` | The splitting of the cyclic algebra (ψ, U) when U is a norm from the cyclic extension cut … | weaker | 366 |
| 32 | `oddWeight_modular_cusp_dimension_lower_bound` | The dimension formulas for modular and cusp forms of odd weight k ≥ 3 on a group without … | weaker | 363 |
| 35 | `mul_norm_of_not_norm` | The fact that the norm group of a quadratic extension of a local field has index 2 in … | weaker | 314 |
| 37 | `exists_eliminationForm_generalLinearForms_cone` | The existence of an eliminating form of Chow form type for the projective variety V(I) ∩ … | weaker | 300 |
| 40 | `subsingleton_groupCohomology_three_of_tate` | Tate's theorem on cup product with a fundamental class (Tate–Nakayama), by which cup … | weaker | 274 |
| 41 | `subsingleton_groupCohomology_three_of_tate_int` | The degree-three case of Tate's theorem on a class in H² whose restrictions generate H² … | weaker | 265 |
| 44 | `torsion_ext` | Injectivity of reduction on N-torsion points of a smooth commutative group scheme over a … | special case | 256 |
| 46 | `existsUnique_torsion_lift` | Bijectivity of reduction on N-torsion points over a henselian local ring when N is … | special case | 254 |
| 51 | `exists_homogeneous_form_of_compatible_fractions` | The theorem that M_d → Γ(Pⁿ, M~(d)) is an isomorphism for large d when M is a finitely … | weaker | 249 |
| 61 | `exists_represent` | The representation criterion for Hermitian forms over a quadratic extension of number … | weaker | 223 |
| 63 | `wp_isAlgebraic` | The algebraicity of the division values of the Weierstrass ℘-function over ℚ(g₂, g₃), … | same | 218 |
| 64 | `jacobiTheta₂_eq_zero_iff` | The location of the zeros of the Jacobi theta function, which vanishes exactly at the … | same | 211 |
| 66 | `c_one_h2_units_subsingleton` | The vanishing of the Brauer group of a quasi-algebraically closed (C₁) field, stated for … | same | 195 |
| 68 | `exists_le_forall_torsion_mem` | The finiteness of the m-division field L₀(A[m]) of an elliptic curve over its field of … | same | 189 |
| 70 | `isAlgebraic_of_nsmul_eq_zero` | The algebraicity of the coordinates of the torsion points of an elliptic curve over its … | same | 188 |
| 71 | `exists_prime_absNorm_eq_of_irreducible_cyclotomic'` | Dirichlet's theorem on primes in arithmetic progressions for primes of degree one in a … | weaker | 180 |
| 72 | `exists_place_not_pow_adicCompletion` | The local–global principle for p-th powers, by which an element that is a p-th power in … | special case | 179 |
| 73 | `finite_torsionBy_natCast` | The finiteness of the n-torsion subgroup E[n] of an elliptic curve, which has at most n² … | weaker | 177 |
| 74 | `elliptic_points_stabilizer` | The location of the zeros of E₄ and E₆, which by the valence formula lie only on the … | weaker | 173 |
| 75 | `isReduced_adicCompletion_tensor_residueField` | The reducedness of the formal fibres of an excellent local ring, whose formal fibres are … | weaker | 171 |
| 76 | `isOpen_identityComponents_smooth_groupScheme` | The openness of the identity component G⁰ of a smooth group scheme (SGA 3, Exposé VI_B, … | same | 171 |
| 82 | `j_invariant_equal_sl2_orbit` | Injectivity of the modular j-invariant on SL₂(ℤ)∖ℍ, one half of the theorem that j … | weaker | 166 |
| 83 | `exists_strictHenselisation` | Existence of the strict henselization of a local ring with its standard properties (EGA … | weaker | 165 |
| 85 | `exists_place_isSquare_and_not_isSquare` | A corollary of the Chebotarev density theorem for the biquadratic extension F(√δ, √u)/F, … | weaker | 162 |
| 86 | `classGroup_dedekind_algClosed_divisible` | Divisibility of the Picard group of a smooth affine curve over an algebraically closed … | weaker | 162 |
| 88 | `pic_divisible_dedekind_finiteType_algClosed` | Divisibility of the Picard group of a smooth affine curve over an algebraically closed … | weaker | 160 |
| 90 | `exists_place_not_isSquare_adicCompletion` | The case n = 2 of the Grunwald–Wang theorem on local powers in contrapositive form, which … | special case | 156 |
| 99 | `collinear` | The collinearity or determinant form of the addition theorem for ℘, by which the points … | same | 149 |
| 101 | `pNeg` | Injectivity of the Weierstrass parametrization z ↦ (℘(z), ℘′(z)) on (ℂ/L) ∖ {0}, part of … | weaker | 144 |
| 103 | `pInj` | Injectivity part of the Weierstrass uniformization ℂ/L ≅ E(ℂ), z ↦ (℘(z), ℘′(z)) … | weaker | 143 |
| 107 | `derivWeierstrassP_ne_zero` | The zeros of ℘′ modulo L are exactly the three nonzero half-periods (the direction that … | weaker | 137 |
| 109 | `exists_dixmierMalliavin_line` | Dixmier–Malliavin lemma (Dixmier and Malliavin, 1978), the one-variable decomposition δ = … | same | 133 |
| 110 | `P_sub_ne` | ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo L (the direction that z ≢ ±w forces ℘(z) ≠ … | weaker | 132 |
| 111 | `wp_ne` | ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo L (the direction that z ≢ ±w forces ℘(z) ≠ … | weaker | 132 |
| 114 | `ferrand_glue_flat_artinian_fibreProduct` | Gluing of flat schemes over a fibre product of Artinian rings, the Schlessinger condition … | special case | 128 |
| 115 | `exists_field_cm_curves_unit_discriminant` | Potential good reduction everywhere of elliptic curves with complex multiplication … | stronger | 127 |
| 120 | `formalFibre_isReduced_of_field` | Geometric reducedness of the formal fibres of an excellent local ring, for local rings … | weaker | 124 |
| 124 | `eq_zero_of_forall_sylow_map_eq_zero` | Injectivity of restriction to a Sylow p-subgroup on the p-primary part of positive-degree … | same | 122 |
| 133 | `weierstrassP_halfPeriods_ne` | The distinctness of the half-period values e₁, e₂, e₃ of the Weierstrass ℘-function | same | 112 |
| 136 | `halfPeriod_facts` | The factorization 4x³ − g₂x − g₃ = 4(x − e₁)(x − e₂)(x − e₃) with distinct roots at the … | same | 111 |
| 140 | `formalFibre_isRegularRing_essFiniteType_int` | The excellence of rings essentially of finite type over ℤ (EGA IV 7.8.3), in its part … | weaker | 109 |
| 141 | `exists_zero_fderiv_ne_zero` | Nondegeneracy of the Gauss map of the theta divisor of a principally polarized abelian … | special case | 109 |
| 142 | `isReduced_coordinateRing` | No published result known. It is the reducedness of the affine coordinate ring of an … | none | 109 |
| 143 | `sub_mem_or_add_mem_of_weierstrassP_eq` | One direction of the description of the fibres of the Weierstrass function, which says … | weaker | 109 |
| 144 | `two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero` | The zeros of ℘′ are exactly the three nonzero half-periods modulo the lattice | same | 109 |
| 146 | `isZero_tateCohomology_of_index` | The Sylow criterion for the vanishing of Tate cohomology, which rests on restriction … | stronger | 107 |
| 152 | `adic_completion_reduced_of_jacobson` | Reducedness of the completion of a reduced excellent ring (EGA IV, Scholie 7.8.3, and … | special case | 103 |
| 153 | `schwartzSubmodule_eq_top_of_gaussian_mem_derivStable` | Density of the Hermite functions, the polynomial multiples of a Gaussian, in the Schwartz … | stronger | 103 |
| 155 | `index_range_powMonoidHom_adicCompletion_mul_norm` | The index formula for n-th powers in a nonarchimedean local field F, which says that the … | special case | 103 |
| 156 | `index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity` | The index formula for n-th powers in a nonarchimedean local field F, which says that the … | special case | 103 |
| 157 | `index_range_powMonoidHom_adicCompletion` | The index formula for n-th powers in a nonarchimedean local field F, which says that the … | same | 102 |

## Technical steps

The check puts 66 statements in this kind.

| No. | Theorem | Known as, by the check | Relation | The proof rests on |
|---:|---|---|---|---:|
| 6 | `embed` | The Kronecker–Weber theorem, in a form that is uniform along the cyclotomic l-tower over … | stronger | 4,905 |
| 15 | `pic_localization_strictHenselisation_no_torsion` | No published result known, a lemma that the Picard group of the generic fibre over T of a … | none | 1,155 |
| 18 | `isProper_of_irreducible_properSpecialFibre_completeDvr` | A special case of the lemma that a separated scheme of finite type over a henselian local … | special case | 902 |
| 19 | `isClosed_image_closure_completeDVR_specialFibre` | No published result known, a closedness lemma for an immersed scheme with proper special … | none | 898 |
| 22 | `gaussian_fourier_self_dual_adelic` | No published result known, a quantitative Siegel mass formula or Hardy–Littlewood type … | none | 824 |
| 24 | `positive_majorant_gaussian` | No published result known, a quantitative Siegel mass formula or Hardy–Littlewood type … | none | 757 |
| 25 | `core_estimate` | No published result known, a quantitative Siegel mass formula or Hardy–Littlewood type … | none | 756 |
| 27 | `units_localization_pow_surj` | The q-divisibility of the units of the generic fibre of a strict henselization of the … | weaker | 418 |
| 28 | `units_localization_strictHenselian_eq_const_mul_unit` | The lemma in Artin's proof that smooth morphisms are locally acyclic (SGA 4 XV, Deligne's … | same | 415 |
| 33 | `exists_base_element_negative_at_two_embeddings` | The existence of a global element with prescribed local Hilbert symbols (O'Meara, … | special case | 341 |
| 34 | `exists_signs` | The existence of a global element with prescribed local Hilbert symbols (O'Meara, … | special case | 340 |
| 38 | `homogeneous_correction_next_level_alt` | No published result known, a gluing lemma that in every large degree t, uniformly in e, … | none | 280 |
| 39 | `uniform_serre_sections_alt` | Serre's theorem that for a finitely generated graded module M over a polynomial ring over … | weaker | 276 |
| 42 | `unit_prod` | No published result known, a product form of the lemma that the rescaled x-coordinates of … | none | 258 |
| 43 | `unit_point` | No published result known, a lemma that combines the injectivity of reduction on torsion … | none | 257 |
| 47 | `uniform_serre_vanishing_cech_cocycles` | Serre's vanishing theorem for H¹ of twisted coherent sheaves on projective space, applied … | special case | 253 |
| 48 | `desc_sub` | No published result known, an elementary restriction and corestriction lemma for modules … | none | 251 |
| 52 | `core` | Chevalley's theorem on units of a number field, that for every exponent n some integer … | special case | 247 |
| 53 | `mem_span_sup_pow_of_forall_complete_dvr_local_test` | No published result known, a valuative test of membership in a principal ideal of the … | none | 247 |
| 55 | `core` | Chevalley's theorem on congruence subgroups of a finitely generated subgroup of E^×, for … | weaker | 244 |
| 58 | `orthonormal_of_diagonal` | Landherr's theorem classifying Hermitian forms over a quadratic extension of number … | special case | 225 |
| 60 | `exists_orthonormal_hermitian_of_diag_pos_isSquare` | Landherr's theorem classifying Hermitian forms over a quadratic extension of number … | special case | 224 |
| 67 | `exists_place_pow_and_not_pow'` | A consequence of the Chebotarev density theorem for the Kummer extension F(δ^{1/p}, … | weaker | 189 |
| 69 | `exists_odd_order_at_even_elsewhere` | No published result known, a lemma that finds an element with odd valuation at one given … | none | 188 |
| 77 | `card_zeros_le_of_growth` | A Bézout-type bound, the refined Bézout inequality (Fulton, Intersection Theory, Example … | weaker | 171 |
| 79 | `smoothAffineCurve_divisor_unit_decomposition` | No published result known, a lemma that prescribes the divisor of a unit on a smooth … | none | 170 |
| 80 | `weber_values_congruences_mod_degree_one_prime` | Hasse's congruences for the singular modulus j(𝓞_K) and for the Weber function at torsion … | special case | 170 |
| 81 | `weber_congruences` | Hasse's congruence for the Weber function and the Kronecker congruence for the … | special case | 169 |
| 84 | `nsAbs` | No published result known, a norm-lifting statement along a finite Galois extension of … | none | 165 |
| 87 | `exists_ne_zero_of_scaled` | A corollary of Mumford's theorem that the theta group acts irreducibly on the sections of … | weaker | 160 |
| 89 | `thetaFunction_ne_zero_at_divisionPoint_selfDual` | A corollary of Mumford's theorem that the theta group acts irreducibly on the sections of … | weaker | 159 |
| 91 | `exists_ne_zero_of_principal` | A corollary of Mumford's theorem that the theta group acts irreducibly on the sections of … | weaker | 156 |
| 92 | `exists_field` | Potential good reduction everywhere of elliptic curves with complex multiplication (Serre … | stronger | 153 |
| 93 | `graded_bezout_bound` | A Bézout inequality for a projective variety X of dimension g whose degree is at most … | weaker | 153 |
| 94 | `isOpen_sectionComponents_of_family` | Openness of the union of the connected components of the fibres that meet a section of a … | weaker | 152 |
| 96 | `cdAbs` | A consequence of the divisibility of the divisor class group of a smooth affine curve … | weaker | 152 |
| 97 | `alg_main` | The standard properties of an unramified quadratic extension of non-archimedean local … | special case | 150 |
| 98 | `stepA` | Addition theorem for the Weierstrass ℘-function, rewritten with the differential equation … | same | 150 |
| 102 | `weierstrassP_superlattice_half_period_prod` | No published result known, an identity of elliptic functions that writes ℘_{L′}(z) − … | none | 143 |
| 105 | `exists_eq_smul_pow` | No published result known, a Kummer-type descent lemma saying that a unit on a smooth … | none | 140 |
| 106 | `zero_density_mult` | Large sieve zero-density estimate for the family of primitive Dirichlet L-functions near … | weaker | 139 |
| 112 | `exists_open_nbhd_section_fiber_isPreirreducible` | A weak local form of the openness of the union X⁰ of the connected components of the … | weaker | 131 |
| 113 | `exists_lift_adicCompletion` | No published result known, a lemma that extends a ring map from a local ring essentially … | none | 130 |
| 116 | `exists_isStandardSmoothOfRelativeDimension_of_isMaximal` | No published result known, a smoothness criterion for flat finite-type algebras over a … | none | 126 |
| 117 | `exists_theta_division_point_ne_zero` | No published result known, the statement that a nonzero theta function of level N ≥ 2 … | none | 126 |
| 119 | `isIso_of_isClosedImmersion` | No published result known, a criterion that a closed subscheme which is surjective and … | none | 125 |
| 121 | `rem_2` | No published result known, an elementary ideal-membership estimate proved by a binomial … | none | 122 |
| 122 | `rem_M` | No published result known, an elementary ideal-membership estimate proved by a binomial … | none | 122 |
| 123 | `length_coker_le` | The formula that over a discrete valuation ring the length of the cokernel of a square … | weaker | 122 |
| 125 | `holomorphic_disc_ratio_growth` | No published result known, a holomorphic disc that runs into the polar divisor of a … | none | 120 |
| 127 | `isIso_of_isClosedImmersion` | No published result known, a fibrewise dimension criterion for a closed immersion between … | none | 119 |
| 128 | `exists_dirichletLFunction_zero_gap_near_one` | The zero-free region of de la Vallée Poussin for Dirichlet L-functions together with the … | weaker | 118 |
| 129 | `exists_isStandardSmoothOfRelativeDimension_of_localization` | No published result known, a smoothness criterion at a closed point of the special fibre … | none | 117 |
| 130 | `exists_conductor_adicCompletion_essFiniteType` | Zariski's analytic normality theorem in Grothendieck's form, that the completion of an … | weaker | 117 |
| 131 | `exists_pow_eq_unit_of_continuous_complex_root` | A consequence of the Riemann existence theorem (SGA 1, Exposé XII) for the Kummer … | weaker | 115 |
| 132 | `isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective` | No published result known, a smoothness criterion at a closed point of the special fibre … | none | 113 |
| 134 | `exists_complete_normal` | No published result known, an approximation of a p-adically complete normal local domain … | none | 112 |
| 135 | `isSmoothAt_of_flat_of_finrank_cotangentSpace_le` | No published result known, a smoothness criterion at a closed point of the special fibre … | none | 111 |
| 137 | `disc_of_pole` | No published result known, a holomorphic disc that runs into the polar divisor of a … | none | 110 |
| 139 | `differentiable_discr_cpow_mul_gamma_inv` | The entireness of the reciprocal Gamma function 1/Γ, applied to the archimedean factor of … | weaker | 110 |
| 147 | `isRegularRing_formalFibre_of_essFiniteType` | No published result known. It is a regularity statement for the formal fibres of a local … | none | 106 |
| 149 | `function_field_class_group_powers` | Divisibility of the ideal class group of a smooth affine curve over an algebraically … | weaker | 105 |
| 150 | `exists_basis_unique_min_and_sums_separated` | No published result known. It is a lattice reduction lemma with explicit constants that … | none | 105 |
| 151 | `exists_basis_unique_min_pair_sums` | No published result known. It is a lattice reduction lemma with explicit constants that … | none | 104 |
| 158 | `primitive_derivation_pairing` | No published result known. It is a divisibility bound for the order of a finite … | none | 101 |
| 159 | `htPres` | The dimension formula ht 𝔮 + dim B/𝔮 = dim B in the regular local ring B = O[[x₁,…,x_N]] … | special case | 101 |

## The statements

### 1, `critAll`

The theorem is `critAll` in the module `Supplements.Kernels.MainTheorems`. Its proof rests on 800,343 declarations, and the five theorems do not use it.

For every positive integer N, every primitive complex Dirichlet character χ modulo N and every complex number s with 0 < Re s < 1, if the Dirichlet L-function L(s, χ) vanishes at s, then Re s = 1/2. Here L(s, χ) is Mathlib's analytic continuation of the Dirichlet series of χ, and for N = 1 it is the Riemann zeta function. The statement is therefore the Generalized Riemann Hypothesis for Dirichlet L-functions in the open critical strip, and it contains the Riemann Hypothesis as the case N = 1.

```
∀ N ≥ 1, ∀ primitive χ mod N, ∀ s ∈ ℂ, (0 < Re s < 1 ∧ L(s, χ) = 0) ⇒ Re s = 1/2
```

The first reader gives it the kind named theorem and names the published result as follows. The Generalized Riemann Hypothesis for Dirichlet L-functions, an open conjecture that has no accepted published proof. Harold Davenport, Multiplicative Number Theory, 3rd edition revised by Hugh L. Montgomery, 2000.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Generalized Riemann Hypothesis for Dirichlet L-functions, an open conjecture with no accepted published proof. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The statement is an open conjecture, so a claimed proof of it calls for a check of the axioms and of any unproved assumptions behind its 800,343 declarations, and the primitivity hypothesis has an underscore name, which in Lean marks a hypothesis that the proof leaves unused.

On emptiness the check wrote this. None found, since for N = 1 the first nontrivial zero 1/2 + 14.1347…i of the Riemann zeta function meets every hypothesis.

### 2, `riemannHypothesis`

The theorem is `riemannHypothesis` in the module `Main`. Its proof rests on 800,342 declarations, and the five theorems use it.

The theorem asserts Mathlib's proposition RiemannHypothesis. That proposition says that every complex number s with ζ(s) = 0 that is not one of the trivial zeros −2, −4, −6, … and differs from 1 has real part 1/2. Here ζ is Mathlib's Riemann zeta function, the meromorphic continuation of the sum of n^(−s), to which Mathlib also assigns a finite value at the pole s = 1.

```
∀ s ∈ ℂ, (ζ(s) = 0 ∧ s ∉ {−2, −4, −6, …} ∧ s ≠ 1) ⇒ Re s = 1/2
```

The first reader gives it the kind named theorem and names the published result as follows. The Riemann Hypothesis, an open conjecture that has no accepted published proof. Bernhard Riemann, Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse, 1859.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Riemann Hypothesis, an open conjecture and one of the Millennium Prize Problems, with no accepted published proof. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The statement is an open conjecture, so a claimed proof of it calls for a check of the axioms and of any unproved assumptions behind its 800,342 declarations.

On emptiness the check wrote this. None found, and the side condition s ≠ 1 is redundant because the value (γ − log 4π)/2 that Mathlib assigns to ζ at 1 is nonzero.

### 3, `rhOfAll`

The theorem is `rhOfAll` in the module `Supplements.Kernels.MainTheorems`. Its proof rests on 800,341 declarations, and the five theorems do not use it.

The theorem asserts Mathlib's proposition RiemannHypothesis, exactly as theorem 2 does. That proposition says that every complex number s with ζ(s) = 0 that is not one of the trivial zeros −2, −4, −6, … and differs from 1 has real part 1/2.

```
∀ s ∈ ℂ, (ζ(s) = 0 ∧ s ∉ {−2, −4, −6, …} ∧ s ≠ 1) ⇒ Re s = 1/2
```

The first reader gives it the kind named theorem and names the published result as follows. The Riemann Hypothesis, an open conjecture that has no accepted published proof. Bernhard Riemann, Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse, 1859.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Riemann Hypothesis, an open conjecture and one of the Millennium Prize Problems, with no accepted published proof. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The Lean text is word for word that of theorem 2, so the two entries record one claim under two names and in two modules.

On emptiness the check wrote this. None found, and the side condition s ≠ 1 is redundant because the value (γ − log 4π)/2 that Mathlib assigns to ζ at 1 is nonzero.

### 4, `exists_prime`

The theorem is `PositivityTheory.KB.PrincipalPrimes.exists_prime` in the module `Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.ExistsPrincipal`. Its proof rests on 4,930 declarations, and the five theorems use it.

For every number field L and every natural number B, there is a prime element π of the ring of integers 𝒪_L such that the absolute norm of the principal ideal π𝒪_L, which is the index of π𝒪_L in 𝒪_L, is at least B. Since only finitely many ideals of 𝒪_L have norm below a given bound, the statement says that 𝒪_L has infinitely many principal prime ideals.

```
∀ number field L, ∀ B ∈ ℕ, ∃ π ∈ 𝒪_L prime with N(π𝒪_L) ≥ B
```

The first reader gives it the kind standard fact and names the published result as follows. The infinitude of principal prime ideals, the case of the trivial class in the theorem that every ideal class of a number field contains infinitely many prime ideals. Jürgen Neukirch, Algebraic Number Theory, Chapter VII §13, 1999.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The theorem that every ideal class of a number field contains infinitely many prime ideals, in the case of the principal class. For the relation to that result the check has special case, the first reader weaker and the second reader special case.

The check adds this. The norm bound B expresses infinitude because only finitely many ideals have norm below a bound, and the proof needs class field theory, since a prime ideal of L is principal exactly when it splits completely in the Hilbert class field of L.

### 5, `exists_principal`

The theorem is `PositivityTheory.KB.PrincipalPrimes.exists_principal` in the module `Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.ExistsPrincipal`. Its proof rests on 4,928 declarations, and the five theorems use it.

For every number field L and every finite set T of nonzero prime ideals of 𝒪_L, there is a nonzero prime ideal of 𝒪_L outside T that is principal. Mathlib's HeightOneSpectrum of the Dedekind domain 𝒪_L is the set of its nonzero prime ideals. The statement is thus another form of the infinitude of principal prime ideals of 𝒪_L.

```
∀ number field L, ∀ finite set T of nonzero primes of 𝒪_L, ∃ nonzero prime 𝔭 ∉ T with 𝔭 principal
```

The first reader gives it the kind standard fact and names the published result as follows. The infinitude of principal prime ideals, the case of the trivial class in the theorem that every ideal class of a number field contains infinitely many prime ideals. Jürgen Neukirch, Algebraic Number Theory, Chapter VII §13, 1999.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The theorem that every ideal class of a number field contains infinitely many prime ideals, in the case of the principal class. For the relation to that result the check has special case, the first reader weaker and the second reader special case.

The check adds this. The statement has the same content as theorem 4, with a finite set of excluded primes in place of the norm bound.

### 6, `embed`

The theorem is `UpperTheory.V.FW.embed` in the module `Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbedDeg`. Its proof rests on 4,905 declarations, and the five theorems use it.

For every prime l and every number field K that is Galois over ℚ with abelian Galois group, there are natural numbers f and D with f > 1 and f prime to l such that the following holds for all natural numbers n and n₀. For every field K′ that is the extension of K generated by the l^n-th roots of unity, there are a natural number m ≥ n₀, a field L isomorphic to the cyclotomic field ℚ(ζ_{f·l^m}) and a field embedding of K′ into L such that the degree of L over K′ is at most D·l^{n₀}. In words, the cyclotomic l-tower over K lies inside the fields ℚ(ζ_{f·l^m}) for one fixed level f prime to l, with a relative degree bounded independently of n.

```
∀ prime l, ∀ abelian number field K, ∃ f, D ∈ ℕ with f > 1 and gcd(f, l) = 1, ∀ n, n₀ ∈ ℕ, ∃ m ≥ n₀, ∃ embedding K(μ_{l^n}) ↪ L = ℚ(μ_{f·l^m}) with dim_{K(μ_{l^n})} L ≤ D·l^{n₀}
```

The first reader gives it the kind technical step and names the published result as follows. A consequence of the Kronecker–Weber theorem that places the cyclotomic l-tower of an abelian field inside the cyclotomic fields ℚ(ζ_{f·l^m}) with f prime to l, as in the setup of the Ferrero–Washington theorem. Lawrence C. Washington, Introduction to Cyclotomic Fields, 2nd edition, 1997.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The Kronecker–Weber theorem, in a form that is uniform along the cyclotomic l-tower over an abelian field and uses one level f prime to l. For the relation to that result the check has stronger, the first reader weaker and the second reader weaker.

The check adds this. Taking n = n₀ = 0 makes K′ equal to K, so the statement contains the Kronecker–Weber theorem for K itself and the relation weaker that both readers give understates it, while the uniformity in n follows from that theorem by counting degrees of cyclotomic fields.

### 7, `kwHom`

The theorem is `UpperTheory.V.CF.kwHom` in the module `Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom`. Its proof rests on 4,902 declarations, and the five theorems use it.

For every number field L that is Galois over ℚ with abelian Galois group, there are a positive integer N and a homomorphism of ℚ-algebras from L to the cyclotomic field ℚ(ζ_N). Such a homomorphism is injective because L is a field, so every abelian number field embeds into a cyclotomic field.

```
∀ number field L with L/ℚ abelian, ∃ N ≥ 1, ∃ ℚ-embedding L ↪ ℚ(ζ_N)
```

The first reader gives it the kind named theorem and names the published result as follows. The Kronecker–Weber theorem. Lawrence C. Washington, Introduction to Cyclotomic Fields, 2nd edition, Chapter 14, 1997.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Kronecker–Weber theorem. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. Theorem 8 states the same theorem with the abelian field placed inside an algebraically closed field of characteristic zero, where this statement embeds it into a cyclotomic field by a ℚ-algebra map.

### 8, `kw`

The theorem is `UpperTheory.V.CF.kw` in the module `Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Kw`. Its proof rests on 4,901 declarations, and the five theorems use it.

For every algebraically closed field Ω of characteristic zero and every subfield L of Ω that is finite and Galois over ℚ with abelian Galois group, there are a positive integer N and a primitive N-th root of unity ζ in Ω such that L is contained in ℚ(ζ). This is the Kronecker–Weber theorem for abelian fields given as subfields of a fixed algebraically closed field.

```
∀ algebraically closed Ω with char Ω = 0, ∀ L ⊆ Ω finite abelian over ℚ, ∃ N ≥ 1, ∃ ζ ∈ Ω primitive N-th root of unity with L ⊆ ℚ(ζ)
```

The first reader gives it the kind named theorem and names the published result as follows. The Kronecker–Weber theorem. Lawrence C. Washington, Introduction to Cyclotomic Fields, 2nd edition, Chapter 14, 1997.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Kronecker–Weber theorem. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The statement is equivalent to theorem 7, because every number field embeds into an algebraically closed field of characteristic zero and a field that is normal over ℚ has the same image under every embedding into that field.

### 9, `stein_factorisation_connected_fibres`

The theorem is `GlobalTheory.T.stein_factorisation_connected_fibres` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibresStatement`. Its proof rests on 2,002 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.SteinFact.stein_factorisation`.

For all schemes X and Y and every proper morphism g from X to Y with Y locally noetherian, there are a scheme Y′, a morphism a from X to Y′ and a morphism b from Y′ to Y with g = b ∘ a, such that b is finite, a is proper and surjective, the ring map a^# from O_{Y′}(V) to O_X(a^{−1}(V)) is bijective for every open set V of Y′, and every fibre a^{−1}(y) is a preconnected subset of X. The bijectivity condition says that a_*O_X = O_{Y′}, and preconnected means connected or empty.

```
Y locally noetherian, g ∈ Hom(X, Y) proper ⇒ ∃ X —a→ Y′ —b→ Y with g = b∘a, b finite, a proper and surjective, O_{Y′} ≅ a_*O_X, and a^{−1}(y) preconnected for every y ∈ Y′
```

The first reader gives it the kind named theorem and names the published result as follows. The Stein factorization theorem. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique III, première partie, §4.3, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Stein factorization theorem (EGA III 4.3.3, Hartshorne III.11.5). For the relation to that result the check has same, the first reader weaker and the second reader same.

The check adds this. The stated properties force Y′ to be the relative spectrum of g_*O_X, because b is finite and a_*O_X = O_{Y′} gives g_*O_X = b_*O_{Y′}, so the Lean text leaves out only the geometric connectedness of the fibres that EGA and the Stacks Project add, which is the gap behind reader A's verdict weaker.

On emptiness the check wrote this. None found, and the surjectivity of a makes every fibre nonempty, so the preconnected fibres are connected.

### 10, `isConnected_closed`

The theorem is `PositivityTheory.Xgn.SpecialFibreConnected.isConnected_closed` in the module `Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ZeroSetSpecialFibreConnected`. Its proof rests on 1,586 declarations, and the five theorems use it.

Let O be a noetherian local ring, Z a scheme and f a proper morphism from Z to Spec O such that the ring map from O through Γ(Spec O) to Γ(Z, O_Z) induced by f is bijective. Then the fibre of f over the closed point of Spec O is a nonempty connected subset of Z.

```
O noetherian local, f ∈ Hom(Z, Spec O) proper, O ≅ Γ(Z, O_Z) via f^# ⇒ f^{−1}(closed point) nonempty and connected
```

The first reader gives it the kind named theorem and names the published result as follows. Zariski's connectedness theorem, in the case of a local base and its closed point. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique III, première partie, §4.3, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski's connectedness theorem, for a noetherian local base and its closed fibre. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The hypothesis on global sections alone suffices because the base is affine and f_*O_Z is quasi-coherent, which makes the hypothesis equivalent to f_*O_Z = O_{Spec O}.

On emptiness the check wrote this. None found, and the nonemptiness in the conclusion is real content, which holds because a local ring is nonzero, so Z is nonempty and the closed image of f contains the closed point.

### 11, `finite_appTop_restrict`

The theorem is `GlobalTheory.ZariskiSections.finite_appTop_restrict` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirational`. Its proof rests on 1,499 declarations, and the five theorems use it.

For a proper morphism π from a scheme Y to a locally noetherian scheme Z and an affine open subset V of Z, the ring map from Γ(V, O_Z) to Γ(π^{−1}(V), O_Y) induced by the restriction of π over V is finite. In other words, Γ(π^{−1}(V), O_Y) is a finitely generated module over Γ(V, O_Z).

```
π ∈ Hom(Y, Z) proper, Z locally noetherian, V ⊆ Z affine open ⇒ Γ(π^{−1}V, O_Y) finite over Γ(V, O_Z)
```

The first reader gives it the kind standard fact and names the published result as follows. The finiteness of sections under a proper morphism, the degree zero case of Grothendieck's coherence theorem for direct images under proper morphisms. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique III, première partie, §3.2, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The coherence of π_*O_Y for a proper morphism π to a locally noetherian scheme, the degree-zero case for the structure sheaf of Grothendieck's finiteness theorem for proper morphisms (EGA III 3.2.1). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Theorem 12 proves the same finiteness under the weaker hypothesis that only the ring of sections over the affine open set is noetherian.

### 12, `finite_app_of_isProper`

The theorem is `GlobalTheory.SteinFact.finite_app_of_isProper` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres`. Its proof rests on 1,493 declarations, and the five theorems use it.

For a proper morphism g from a scheme X to a scheme Y and an affine open subset V of Y whose ring of sections Γ(V, O_Y) is noetherian, the ring map g^# from Γ(V, O_Y) to Γ(g^{−1}(V), O_X) is finite. Unlike theorem 11, it asks only that this one ring be noetherian and not that the whole of Y be locally noetherian.

```
g ∈ Hom(X, Y) proper, V ⊆ Y affine open with Γ(V, O_Y) noetherian ⇒ Γ(g^{−1}V, O_X) finite over Γ(V, O_Y)
```

The first reader gives it the kind standard fact and names the published result as follows. The finiteness of sections under a proper morphism, the degree zero case of Grothendieck's coherence theorem for direct images under proper morphisms. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique III, première partie, §3.2, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The coherence of g_*O_X for a proper morphism g, the degree-zero case for the structure sheaf of Grothendieck's finiteness theorem for proper morphisms (EGA III 3.2.1). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The weaker noetherian hypothesis suffices because the restriction of g over V is a proper morphism to the noetherian affine scheme V, to which the finiteness theorem applies.

### 13, `exists_zmod_char_not_norm`

The theorem is `GroundTheory.ProfCoh.exists_zmod_char_not_norm` in the module `GroundTheory.ProfiniteCohomology.LocalTateDuality.NormCharacters`. Its proof rests on 1,468 declarations, and the five theorems use it.

Let F be a nonarchimedean local field with separable closure Ω, and let n be a natural number whose image in F is nonzero. If an element a of F^× is not the n-th power of any element of F^×, then there is a group homomorphism ψ from Gal(Ω/F) to ℤ/nℤ with open kernel such that a is not the norm of any element of the fixed field L of the kernel of ψ. The field L is a cyclic extension of F of degree dividing n, so the conclusion says that a lies outside the norm group N_{L/F}(L^×).

```
F nonarchimedean local, n·1_F ≠ 0, a ∈ F^× ∖ (F^×)^n ⇒ ∃ ψ ∈ Hom(Gal(F^sep/F), ℤ/n) with open kernel and a ∉ N_{L/F}(L) for L = (F^sep)^{ker ψ}
```

The first reader gives it the kind standard fact and names the published result as follows. The consequence of local class field theory that (F^×)^n is the intersection of the norm groups of the cyclic extensions of F of degree dividing n, which is the nondegeneracy of the local duality pairing between H^1(F, ℤ/n) and F^×/(F^×)^n. Jürgen Neukirch, Alexander Schmidt and Kay Wingberg, Cohomology of Number Fields, 2nd edition, 2008.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The half of the nondegeneracy of the local duality pairing between H^1(F, ℤ/nℤ) and F^×/(F^×)^n which says that an element of F^× that is a norm from every cyclic extension of degree dividing n is an n-th power, a consequence of local class field theory. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The field F may have positive characteristic, and the hypothesis that n is nonzero in F is what makes (F^×)^n an open subgroup of finite index, so that the existence theorem of local class field theory applies to it.

On emptiness the check wrote this. None found, since a uniformizer of F meets the hypotheses for every n ≥ 2 that is nonzero in F, while the hypotheses themselves exclude n = 0 and n = 1.

### 14, `exists_le_adjoin_rootsOfUnity`

The theorem is `GroundTheory.LocalField.Padic.exists_le_adjoin_rootsOfUnity` in the module `GroundTheory.LocalFields.KroneckerWeber`. Its proof rests on 1,460 declarations, and the five theorems use it.

Let p be a prime and Ω a separable closure of the field ℚ_p of p-adic numbers. For every intermediate field L between ℚ_p and Ω that is finite over ℚ_p and Galois with abelian Galois group, there is a positive integer N such that L is contained in the field generated over ℚ_p by all N-th roots of unity in Ω.

```
∀ prime p, ∀ finite abelian L/ℚ_p inside a separable closure Ω, ∃ N ≥ 1 with L ⊆ ℚ_p(μ_N)
```

The first reader gives it the kind named theorem and names the published result as follows. The local Kronecker–Weber theorem. Lawrence C. Washington, Introduction to Cyclotomic Fields, 2nd edition, Chapter 14, 1997.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The local Kronecker–Weber theorem for ℚ_p. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The instances IsSepClosed and Algebra.IsSeparable make Ω a separable closure of ℚ_p, which is an algebraic closure because ℚ_p has characteristic zero.

### 15, `pic_localization_strictHenselisation_no_torsion`

The theorem is `GlobalTheory.pic_localization_strictHenselisation_no_torsion` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicLocalizationStrictHenselisationNoTorsion`. Its proof rests on 1,155 declarations, and the five theorems use it.

Let T be a local domain in which every monic polynomial of positive degree has a root, and let q be a positive integer that is a unit in T. Let O be a henselian local ring with separably closed residue field that is an algebra over T[X], compatibly with T, and is the directed union of T[X]-subalgebras each isomorphic to the localization of an étale T[X]-algebra at a prime ideal, a condition that a strict henselization of T[X] satisfies. Then the Picard group of the localization of O at the nonzero elements of T, which is O ⊗_T K for the fraction field K of T, has no nontrivial element whose q-th power is trivial.

```
T absolutely integrally closed local domain, q ∈ T^×, O strictly henselian and a directed union of local rings of étale T[X]-algebras ⇒ Pic(O ⊗_T Frac T)[q] = 0
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a technical lemma saying that the Picard group of the generic fibre of a strict henselization of the affine line over an absolutely integrally closed local domain has no q-torsion, of the kind used in proofs of the local acyclicity of smooth morphisms.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a lemma that the Picard group of the generic fibre over T of a strictly henselian local ring of the affine line over an absolutely integrally closed local domain T has no q-torsion. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The ring whose Picard group is studied inverts only the nonzero elements of T, so it is in general not local, and the hypotheses describe the strict henselization of T[X] at a prime by its shape as a directed union without naming it.

On emptiness the check wrote this. None found, since a valuation ring with algebraically closed fraction field gives a case with content, although for a field T the localization is the local ring O itself and the conclusion holds at once because a local ring has trivial Picard group.

### 16, `isProper_of_properSpecialFibre_universallyOpen_dvr`

The theorem is `GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvrStatement`. Its proof rests on 910 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.FibreProperDvr.isProper_of_specialFibre`.

Let W be a discrete valuation ring with residue field k, and let f be a morphism from a scheme X to Spec W that is separated, locally of finite type, quasi-compact and universally open, and whose fibres are geometrically irreducible. If the special fibre X ×_{Spec W} Spec k is proper over k, then f is proper.

```
W DVR, f ∈ Hom(X, Spec W) separated, of finite type, universally open, with geometrically irreducible fibres, X_k proper over k ⇒ f proper
```

The first reader gives it the kind standard fact and names the published result as follows. A properness criterion through the special fibre, which I relate to Grothendieck's results on the set of proper fibres of a separated universally open morphism of finite type with geometrically connected fibres. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique IV, troisième partie, §15.7, Publications Mathématiques de l'IHÉS 28, 1966.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. A properness criterion through the special fibre over a discrete valuation ring, the case of Spec W of Grothendieck's theorem that the points with proper fibre form an open and closed set for a separated universally open morphism of finite type with geometrically connected fibres (EGA IV_3 15.7.10). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Neither reader is sure of the exact published form, so the reference to EGA IV_3 15.7.10 should be checked against the text before it is cited.

On emptiness the check wrote this. None found, since the projective line over W meets every hypothesis, and the nonemptiness of fibres that Mathlib builds into geometric irreducibility excludes the open immersion of the generic point into Spec W, which would otherwise be a counterexample.

### 17, `zariski_connectedness_isPreconnected_fibre`

The theorem is `GlobalTheory.T.zariski_connectedness_isPreconnected_fibre` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreStatement`. Its proof rests on 905 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ZConn.isPreconnected_fibre`.

For all schemes X and Y and every proper morphism a from X to Y with Y locally noetherian such that the ring map a^# from O_Y(V) to O_X(a^{−1}(V)) is bijective for every open set V of Y, every fibre a^{−1}(y) is a preconnected subset of X. The bijectivity condition says that a_*O_X = O_Y, and preconnected means connected or empty.

```
Y locally noetherian, a ∈ Hom(X, Y) proper, O_Y ≅ a_*O_X ⇒ a^{−1}(y) preconnected for every y ∈ Y
```

The first reader gives it the kind named theorem and names the published result as follows. Zariski's connectedness theorem. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique III, première partie, §4.3, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski's connectedness theorem (EGA III 4.3.1, Hartshorne III.11.3). For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The bijectivity of the section maps over every open set V of Y is the usual hypothesis a_*O_X = O_Y, and the conclusion gives connected fibres as in EGA III 4.3.1 and leaves out their geometric connectedness.

On emptiness the check wrote this. None found, and the hypotheses force a to be surjective, so every fibre is nonempty and the preconnected fibres are connected.

### 18, `isProper_of_irreducible_properSpecialFibre_completeDvr`

The theorem is `GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteDStatement`. Its proof rests on 902 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre`.

Let O be a complete discrete valuation ring with residue field k, and let f be a separated and quasi-compact morphism locally of finite type from an irreducible scheme X to Spec O. If some point of X maps to the closed point of Spec O and the special fibre X ×_{Spec O} Spec k is proper over k, then f is proper.

```
O complete DVR, X irreducible, f ∈ Hom(X, Spec O) separated of finite type, X_k ≠ ∅ proper over k ⇒ f proper
```

The first reader gives it the kind technical step and names the published result as follows. A special case of the decomposition lemma for a separated scheme of finite type over a henselian local ring, which splits off an open and closed part that is proper over the base and has a given open and closed proper part of the special fibre. The Stacks Project Authors, The Stacks Project, chapter More on Morphisms, 2024.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A special case of the lemma that a separated scheme of finite type over a henselian local ring has an open and closed subscheme that is proper over the base and whose special fibre is any prescribed open and closed part of the special fibre that is proper (Stacks Project, More on Morphisms). For the relation to that result the check has special case, the first reader special case and the second reader none.

The check adds this. The completeness of O is used only through the henselian property, and it cannot simply be dropped, since over a non-henselian discrete valuation ring an open part of the spectrum of a finite semilocal Dedekind extension meets the other hypotheses and is not proper.

On emptiness the check wrote this. None found, since the projective line over O meets every hypothesis.

### 19, `isClosed_image_closure_completeDVR_specialFibre`

The theorem is `GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibreStatement`. Its proof rests on 898 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.FibProperClosed.isClosed_image_closure`.

Let O be a complete discrete valuation ring with residue field k, let s be a proper morphism from a scheme P to Spec O and q an immersion from a scheme Y into P, and assume that the special fibre of the composite morphism from Y to Spec O is proper over k. For every irreducible subset C of Y whose closure in Y contains a point lying over the closed point of Spec O, the image under q of the closure of C is closed in P.

```
O complete DVR, s ∈ Hom(P, Spec O) proper, q ∈ Hom(Y, P) immersion, Y_k proper over k, C ⊆ Y irreducible with cl(C) ∩ Y_k ≠ ∅ ⇒ q(cl C) closed in P
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a closedness lemma for a locally closed subscheme with proper special fibre inside a proper scheme over a complete discrete valuation ring, which follows from the properness criterion of theorem 18 applied to the closure of C.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a closedness lemma for an immersed scheme with proper special fibre inside a proper scheme over a complete discrete valuation ring. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The statement follows from theorem 18 applied to the closure of C with its reduced structure, which is irreducible, separated and of finite type over O with a nonempty special fibre that is proper because it is closed in the special fibre of Y.

On emptiness the check wrote this. None found, since an irreducible scheme P proper over O with Y = P and C = P meets every hypothesis.

### 20, `zariskiConnectedness_isPreconnected_fibre_affine`

The theorem is `GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffineStatement`. Its proof rests on 891 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ZariskiConn.isPreconnected_fibre`.

Let X be an affine locally noetherian scheme and f a proper morphism from a scheme Y to X such that the ring map f^# from Γ(X, O_X) to Γ(Y, O_Y) is bijective. Then every fibre f^{−1}(x) is a preconnected subset of Y, which means connected or empty.

```
X affine noetherian, f ∈ Hom(Y, X) proper, Γ(X, O_X) ≅ Γ(Y, O_Y) via f^# ⇒ f^{−1}(x) preconnected for every x ∈ X
```

The first reader gives it the kind named theorem and names the published result as follows. Zariski's connectedness theorem, in the case of an affine base. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique III, première partie, §4.3, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski's connectedness theorem, over an affine noetherian base. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Over the affine base the condition on global sections is equivalent to f_*O_Y = O_X because f_*O_Y is quasi-coherent, and theorem 17 is the same theorem over any locally noetherian base.

On emptiness the check wrote this. None found, and the hypotheses force f to be surjective, so every fibre is nonempty.

### 21, `isPreconnected_closedFibre`

The theorem is `GlobalTheory.ZariskiConn.isPreconnected_closedFibre` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine`. Its proof rests on 882 declarations, and the five theorems use it.

Let O be a Noetherian local ring that is complete and separated for the adic topology of its maximal ideal, and let f from a scheme Y to Spec O be a proper morphism. If the underlying space of Y is preconnected, then the preimage under f of the closed point of Spec O is preconnected. Since preconnected allows the empty set, the statement says that a connected scheme proper over O has a connected closed fibre.

```
(O, 𝔪) Noetherian local and 𝔪-adically complete, f: Y → Spec O proper, Y preconnected ⟹ f⁻¹({𝔪}) preconnected
```

The first reader gives it the kind standard fact and names the published result as follows. Zariski's connectedness theorem in its form over a complete Noetherian local base, by which the connected components of a scheme proper over such a ring correspond to those of its closed fibre. A. Grothendieck and J. Dieudonné, Éléments de géométrie algébrique III. Étude cohomologique des faisceaux cohérents, première partie, Publications Mathématiques de l'IHÉS 11, 1961.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The local form of Zariski's connectedness theorem, by which a connected scheme proper over a complete Noetherian local ring has a connected closed fibre, a corollary of the theorem on formal functions and the Stein factorisation (EGA III 4.3). For the relation to that result the check has same, the first reader weaker and the second reader same.

The check adds this. The Lean text gives only the direction from a preconnected Y to a preconnected closed fibre, and since preconnected allows the empty set, the nonemptiness of the closed fibre of a nonempty Y that A's gloss uses comes from properness and not from the stated conclusion.

### 22, `gaussian_fourier_self_dual_adelic`

The theorem is `GlobalTheory.T.gaussian_fourier_self_dual_adelic` in the module `Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianFourierSelfDualAdelicStatement`. Its proof rests on 824 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CompanionTheory.SW.Core0.core_zero`.

Let F be a totally real number field of degree d, B a nonsingular symmetric matrix over F of size 2M with M ≥ 3, Q(x) = ½ xᵀBx, and P_w a positive definite majorant of B at each real place w, meaning P_w B_w⁻¹ P_w = B_w. Fix a Haar measure on the finite adeles A_f that gives the integral adeles mass 1 and a probability space carrying measurable elements g_∞,w(ω) of the real orthogonal groups of B and g_f(ω) of O(B)(A_f), and assume that for each N ≥ 1 the expected number of nonzero x ∈ F^{2M} with N g_f(ω)x integral and every ‖g_∞,w(ω)x‖ ≤ R is at most C_N(R^{dM} + R^{2dM}) for all R > 0. Then there are a constant C, continuous nonnegative densities D_f(a, ·) on A_f of the image under Q of Haar measure on {x | a x integral}, and a continuous nonnegative density D_∞ on ℝ^{places} of the image under (Q_w)_w of the Gaussian exp(−π Σ_w x_wᵀ P_w x_w) dx. For every integer a ≥ 1 the expectation I of the sum of exp(−π Σ_w (g_∞,w(ω)x)ᵀ P_w g_∞,w(ω)x) over nonzero x ∈ F^{2M} with Q(x) = 0 and a g_f(ω)x integral is finite and satisfies |I − |Δ_F|^{−(2M−1)/2} D_f(a, 0) D_∞(0)| ≤ C a^{dM}, where Δ_F is the discriminant of F.

```
E_ω Σ_{x ∈ F^{2M}∖{0}, Q(x) = 0, a g_f(ω)x ∈ Ô^{2M}} exp(−π Σ_w ‖g_∞,w(ω)x‖²_{P_w}) = I(a) with |I(a) − |Δ_F|^{−(2M−1)/2} D_f(a, 0) D_∞(0)| ≤ C a^{dM} for all a ≥ 1
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a quantitative Siegel–Weil type asymptotic with error of order a^{dM} for the averaged Gaussian-weighted count of nonzero isotropic vectors of a quadratic form in 2M ≥ 6 variables over a totally real field.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a quantitative Siegel mass formula or Hardy–Littlewood type asymptotic with error of order a^{dM} for the averaged Gaussian-weighted count of nonzero isotropic vectors of a nondegenerate quadratic form in 2M ≥ 6 variables over a totally real field. For the relation to that result the check has none, the first reader none and the second reader different.

The check adds this. By scaling, Df(a, 0) equals a^{2d(M−1)} times Df(1, 0) with d the degree of F, so against the error C·a^{dM} the estimate is a genuine asymptotic exactly because M ≥ 3, and the constant C is uniform in a but may depend on all other data, Ω included.

On emptiness the check wrote this. None found, since a one-point probability space with any single choice of orthogonal elements meets the averaged counting hypothesis.

### 23, `eq_top_of_forall_exists_norm`

The theorem is `GroundTheory.ProfCoh.eq_top_of_forall_exists_norm` in the module `GroundTheory.ProfiniteCohomology.LocalTateDuality.NormCharacters`. Its proof rests on 791 declarations, and the five theorems use it.

Let F be a nonarchimedean local field with separable closure Ω and Galois group G = Gal(Ω/F), and let H be an open normal subgroup of G that contains every commutator στσ⁻¹τ⁻¹. These conditions make the fixed field L of H a finite abelian extension of F. If every element of F^× is the norm from L to F of an element of L, then H = G, which means L = F.

```
H ⊴ Gal(Ω/F) open, [G, G] ⊆ H, F^× ⊆ N_{Ω^H/F}(Ω^H) ⟹ H = Gal(Ω/F)
```

The first reader gives it the kind standard fact and names the published result as follows. The norm index equality of local class field theory, by which the index of N_{L/F}(L^×) in F^× equals the degree of L over F for a finite abelian extension L/F. J.-P. Serre, Local Fields, Graduate Texts in Mathematics 67, 1979.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The corollary of the norm index equality of local class field theory, by which the index of N_{L/F}(L^×) in F^× equals the degree of L over F for a finite abelian extension L/F, that a finite abelian extension whose norm group is all of F^× is trivial. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The normality hypothesis on H is implied by the commutator condition, and the openness of H makes the fixed field finite over F, so the norm in the hypothesis is the field norm of a finite extension.

### 24, `positive_majorant_gaussian`

The theorem is `GlobalTheory.T.positive_majorant_gaussian` in the module `CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveMajorantGaussianStatement`. Its proof rests on 757 declarations, and the five theorems use it.

Let F be a totally real number field of degree d, B a nonsingular symmetric matrix over F of size 2M with M ≥ 3, Q(x) = ½ xᵀBx, and P_w a positive definite majorant of B at each real place w, meaning P_w B_w⁻¹ P_w = B_w. Fix a Haar measure on the finite adeles A_f that gives the integral adeles mass 1 and a probability space carrying measurable elements g_∞,w(ω) of the real orthogonal groups of B and g_f(ω) of O(B)(A_f), and assume that for each N ≥ 1 the expected number of nonzero x ∈ F^{2M} with N g_f(ω)x integral and every ‖g_∞,w(ω)x‖ ≤ R is at most C_N(R^{dM} + R^{2dM}) for all R > 0. Then there are a constant C, continuous nonnegative densities D_f(a, ·) on A_f of the image under Q of Haar measure on {x | a x integral}, and a continuous nonnegative density D_∞ on ℝ^{places} of the image under (Q_w)_w of the Gaussian exp(−π Σ_w x_wᵀ P_w x_w) dx. For every integer a ≥ 1 and every nonzero β ∈ F the expectation I of the sum of exp(−π Σ_w (g_∞,w(ω)x)ᵀ P_w g_∞,w(ω)x) over x ∈ F^{2M} with Q(x) = β and a g_f(ω)x integral is finite and satisfies |I − |Δ_F|^{−(2M−1)/2} D_f(a, β) D_∞((ρ_w β)_w)| ≤ C a^{dM}, with C independent of a and β and Δ_F the discriminant of F.

```
E_ω Σ_{x ∈ F^{2M}, Q(x) = β, a g_f(ω)x ∈ Ô^{2M}} exp(−π Σ_w ‖g_∞,w(ω)x‖²_{P_w}) = I(a, β) with |I(a, β) − |Δ_F|^{−(2M−1)/2} D_f(a, β) D_∞((ρ_w β)_w)| ≤ C a^{dM} for all a ≥ 1 and β ∈ F^×
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a quantitative Siegel–Weil type asymptotic, uniform in β with error of order a^{dM}, for averaged Gaussian-weighted representation numbers of a nonzero β by a quadratic form in 2M ≥ 6 variables over a totally real field.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a quantitative Siegel mass formula or Hardy–Littlewood type asymptotic with error of order a^{dM}, uniform in β, for the averaged Gaussian-weighted number of representations of a nonzero β in F by a nondegenerate quadratic form in 2M ≥ 6 variables over a totally real field. For the relation to that result the check has none, the first reader none and the second reader different.

The check adds this. One constant C serves all positive integers a and all nonzero β, and number 25 has word for word the same Lean statement under another name.

On emptiness the check wrote this. None found, since a one-point probability space with any single choice of orthogonal elements meets the averaged counting hypothesis.

### 25, `core_estimate`

The theorem is `GlobalTheory.CompanionTheory.SW.Core.core_estimate` in the module `CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PositiveMajorantGaussian`. Its proof rests on 756 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `CompanionTheory.PlacePermOperatorBicommutantSpan.core`.

Let F be a totally real number field of degree d, B a nonsingular symmetric matrix over F of size 2M with M ≥ 3, Q(x) = ½ xᵀBx, and P_w a positive definite majorant of B at each real place w, meaning P_w B_w⁻¹ P_w = B_w. Fix a Haar measure on the finite adeles A_f that gives the integral adeles mass 1 and a probability space carrying measurable elements g_∞,w(ω) of the real orthogonal groups of B and g_f(ω) of O(B)(A_f), and assume that for each N ≥ 1 the expected number of nonzero x ∈ F^{2M} with N g_f(ω)x integral and every ‖g_∞,w(ω)x‖ ≤ R is at most C_N(R^{dM} + R^{2dM}) for all R > 0. Then there are a constant C, continuous nonnegative densities D_f(a, ·) on A_f of the image under Q of Haar measure on {x | a x integral}, and a continuous nonnegative density D_∞ on ℝ^{places} of the image under (Q_w)_w of the Gaussian exp(−π Σ_w x_wᵀ P_w x_w) dx. For every integer a ≥ 1 and every nonzero β ∈ F the expectation I of the sum of exp(−π Σ_w (g_∞,w(ω)x)ᵀ P_w g_∞,w(ω)x) over x ∈ F^{2M} with Q(x) = β and a g_f(ω)x integral is finite and satisfies |I − |Δ_F|^{−(2M−1)/2} D_f(a, β) D_∞((ρ_w β)_w)| ≤ C a^{dM}, with C independent of a and β and Δ_F the discriminant of F.

```
E_ω Σ_{x ∈ F^{2M}, Q(x) = β, a g_f(ω)x ∈ Ô^{2M}} exp(−π Σ_w ‖g_∞,w(ω)x‖²_{P_w}) = I(a, β) with |I(a, β) − |Δ_F|^{−(2M−1)/2} D_f(a, β) D_∞((ρ_w β)_w)| ≤ C a^{dM} for all a ≥ 1 and β ∈ F^×
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a quantitative Siegel–Weil type asymptotic, uniform in β with error of order a^{dM}, for averaged Gaussian-weighted representation numbers of a nonzero β by a quadratic form in 2M ≥ 6 variables over a totally real field.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a quantitative Siegel mass formula or Hardy–Littlewood type asymptotic with error of order a^{dM}, uniform in β, for the averaged Gaussian-weighted number of representations of a nonzero β in F by a nondegenerate quadratic form in 2M ≥ 6 variables over a totally real field. For the relation to that result the check has none, the first reader none and the second reader different.

The check adds this. The Lean statement is word for word that of number 24, so the two entries record one result twice.

On emptiness the check wrote this. None found, since a one-point probability space with any single choice of orthogonal elements meets the averaged counting hypothesis.

### 26, `classNumber_finite_integralLevel_closedSubgroupGL`

The theorem is `GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGLStatement`. Its proof rests on 530 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ClassFin.classFinite_integralLevel`.

Let F be a number field and S a set of polynomials over F in the n² entries of an n × n matrix such that, for every commutative F-algebra B, the invertible matrices over B that satisfy all of S contain the identity and are closed under products and inverses. This makes S the set of equations of a linear algebraic group G ⊆ GL_n over F. Then there is a finite set T ⊆ G(A_f), with A_f the finite adeles of F, such that every x ∈ G(A_f) equals γ s u with γ ∈ G(F), s ∈ T and u ∈ G(A_f) such that u and u⁻¹ have entries integral at every finite place.

```
G = V(S) ∩ GL_n a subgroup scheme over F ⟹ G(F) \ G(A_f) / (G(A_f) ∩ GL_n(Ô_F)) is finite
```

The first reader gives it the kind named theorem and names the published result as follows. Borel's finiteness of class numbers for linear algebraic groups over number fields. A. Borel, Some finiteness properties of adele groups over number fields, Publications Mathématiques de l'IHÉS 16, 1963.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Borel's finiteness of the class number of a linear algebraic group over a number field (Borel 1963, Platonov–Rapinchuk Theorem 5.1), with the class number taken for the integral structure that the embedding in GL_n gives. For the relation to that result the check has same, the first reader special case and the second reader same.

The check adds this. Platonov and Rapinchuk define the class number with exactly this subgroup of points with integral entries and integral inverse, and because any two compact open subgroups of G(A_f) are commensurable, finiteness here also gives finiteness for every compact open subgroup, which is why A's special case and B's same describe one content.

### 27, `units_localization_pow_surj`

The theorem is `GlobalTheory.LocAcycUnits.units_localization_pow_surj` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationPowSurj`. Its proof rests on 418 declarations, and the five theorems use it.

Let T be a local domain in which every monic polynomial of positive degree has a root, a condition that makes T integrally closed with algebraically closed fraction field K. Let O be a Henselian local ring with separably closed residue field that is an algebra over T and over T[X] compatibly, and assume O is the union of a directed family of T[X]-subalgebras each isomorphic over T[X] to the localization of an étale T[X]-algebra at a prime ideal. Let q be a positive integer that is a unit in T. Then every unit of O ⊗_T K, the localization of O at the images of the nonzero elements of T, is the q-th power of a unit.

```
T absolutely integrally closed local domain, O strictly Henselian and ind-étale over T[X], q ∈ T^× ⟹ ∀ u ∈ (O ⊗_T K)^× ∃ v ∈ (O ⊗_T K)^× with v^q = u
```

The first reader gives it the kind technical step and names the published result as follows. The vanishing of H¹ with coefficients μ_q on the geometric generic fibre of a strict henselization of the affine line, from the proof that smooth morphisms are locally acyclic, in its unit part through the Kummer sequence. M. Artin, Morphismes acycliques, Exposé XV in Théorie des topos et cohomologie étale des schémas (SGA 4), tome 3, Lecture Notes in Mathematics 305, 1973.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The q-divisibility of the units of the generic fibre of a strict henselization of the affine line over an absolutely integrally closed strictly local base, the unit part, through the Kummer sequence, of the vanishing of H¹ with μ_q coefficients in Artin's proof that smooth morphisms are locally acyclic (SGA 4 XV, Deligne's Arcata in SGA 4½). For the relation to that result the check has weaker, the first reader weaker and the second reader same.

The check adds this. A local domain in which every monic polynomial of positive degree has a root is strictly henselian with algebraically closed fraction field, so the Lean base matches the published one, while O is described only through its properties and may lie over any prime of T[X], and the repeated IsDomain T and the condition 0 < q add nothing.

### 28, `units_localization_strictHenselian_eq_const_mul_unit`

The theorem is `GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnitStatement`. Its proof rests on 415 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.VertUnits.units_eq_const_mul_unit`.

Let T be a local domain in which every monic polynomial of positive degree has a root, a condition that makes T integrally closed with algebraically closed fraction field K. Let O be a Henselian local ring with separably closed residue field that is an algebra over T and over T[X] compatibly, and assume O is the union of a directed family of T[X]-subalgebras each isomorphic over T[X] to the localization of an étale T[X]-algebra at a prime ideal. Then for every unit u of O ⊗_T K, the localization of O at the images of the nonzero elements of T, there are nonzero c, d ∈ T and a unit w of O with u d = c w in O ⊗_T K. Every such unit is therefore an element c/d of K^× times a unit of O.

```
∀ u ∈ (O ⊗_T K)^× ∃ c, d ∈ T∖{0}, w ∈ O^× with u d = c w, so (O ⊗_T K)^× ⊆ K^× · O^×
```

The first reader gives it the kind technical step and names the published result as follows. The description of the units of the geometric generic fibre of a strict henselization of the affine line as constants times units, a lemma in Artin's proof that smooth morphisms are locally acyclic. M. Artin, Morphismes acycliques, Exposé XV in Théorie des topos et cohomologie étale des schémas (SGA 4), tome 3, Lecture Notes in Mathematics 305, 1973.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The lemma in Artin's proof that smooth morphisms are locally acyclic (SGA 4 XV, Deligne's Arcata in SGA 4½) that every unit of the generic fibre of a strict henselization of the affine line over an absolutely integrally closed strictly local base is a nonzero constant times a unit of the strict henselization. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The q-divisibility of number 27 follows from this decomposition, because nonzero constants of the algebraically closed fraction field and units of the henselian ring O with separably closed residue field are both q-th powers when q is invertible in T.

### 29, `exists_finite_etale_representing_clopen_subschemes`

The theorem is `UpperTheory.Cb.exists_finite_etale_representing_clopen_subschemes` in the module `Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleRepresentingClopenSubschemes`. Its proof rests on 388 declarations, and the five theorems use it.

Let S be a locally Noetherian scheme and G a finite étale S-scheme. Then there are a finite étale S-scheme Y and an open and closed subset U of Y ×_S G with a universal property. For every S-scheme T and every open and closed subset V of T ×_S G there is exactly one S-morphism y from T to Y with (y × id_G)⁻¹(U) = V. Thus Y represents the functor that sends T to the set of open and closed subsets of T ×_S G.

```
∃ Y finite étale over S, U ⊆ Y ×_S G clopen, with Hom_S(T, Y) ≅ {V ⊆ T ×_S G clopen} via y ↦ (y × id_G)⁻¹(U) for every S-scheme T
```

The first reader gives it the kind standard fact and names the published result as follows. Representability of the Weil restriction along G → S of the constant scheme S ⊔ S, which classifies open and closed subschemes of the products T ×_S G. S. Bosch, W. Lütkebohmert and M. Raynaud, Néron Models, Ergebnisse der Mathematik und ihrer Grenzgebiete 21, 1990.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Representability of the Weil restriction along a finite étale G → S of the constant scheme S ⊔ S by a finite étale S-scheme, equivalently the finite étale scheme that classifies open and closed subschemes of the base changes of G (Bosch, Lütkebohmert and Raynaud, Néron Models, Section 7.6). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The hypothesis that S is locally Noetherian is more than the published result needs, and under Galois theory Y corresponds to the set of subsets of a geometric fibre of G.

### 30, `kummer_cocycle_norm_criterion`

The theorem is `GlobalTheory.T.kummer_cocycle_norm_criterion` in the module `Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterionStatement`. Its proof rests on 381 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary`.

Let K be a field with separable closure Ω and Galois group G, let N ≥ 1, let ζ ∈ Ω be a primitive N-th root of unity, and let c₀ be the cyclotomic character, a map from G to Z/N with g(ζ) = ζ^{c₀(g)}. Let ψ be a homomorphism from G to Z/N with open kernel, and let U ∈ K^× be a norm from the fixed field of ker ψ. If T ∈ Ω satisfies T^N = U and κ from G to Z/N satisfies g(T) = ζ^{κ(g)} T, then there is a locally constant c from G to Z/N with c₀(g) c(h) − c(gh) + c(g) = κ(g) ψ(h) for all g, h ∈ G. The left side is the coboundary of c in Z/N(1) and the right side is the cup product of the Kummer cocycle of U with ψ, so the class (U) ∪ ψ vanishes in H²(G, μ_N).

```
U ∈ N_{L_ψ/K}(L_ψ^×) ⟹ ∃ c ∈ C⁰(G, Z/N(1)) with c₀(g)c(h) − c(gh) + c(g) = κ_U(g)ψ(h), that is κ_U ∪ ψ = dc
```

The first reader gives it the kind standard fact and names the published result as follows. The norm criterion for the splitting of a cyclic algebra, in the direction that a norm b from L_χ gives (χ, b) = 0, written with the Kummer class of b in H²(K, μ_N). P. Gille and T. Szamuely, Central Simple Algebras and Galois Cohomology, Cambridge Studies in Advanced Mathematics 101, 2006.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The norm criterion for cyclic algebras in the direction that a norm U from the cyclic extension cut out by ψ makes the class of the cyclic algebra (ψ, U) vanish, here written as the cup product of the Kummer class of U with ψ in H²(K, μ_N) (Serre, Local Fields XIV §1). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The maps c0 and κ are determined by ζ and T, so their hypotheses only fix notation, and the conclusion is a cocycle identity with a locally constant cochain c rather than a statement about classes.

On emptiness the check wrote this. None found, although the hypothesis of a primitive N-th root of unity in Ω can be met only when the characteristic of K does not divide N.

### 31, `exists_lift_of_norm`

The theorem is `GlobalTheory.CompanionTheory.KummerCup.exists_lift_of_norm` in the module `Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion`. Its proof rests on 366 declarations, and the five theorems use it.

Let K be a field with separable closure Ω and Galois group G, let N ≥ 1, let ψ be a homomorphism from G to Z/N with open kernel, and let U ∈ K^× be a norm from the fixed field L of ker ψ. Write ψ̄(g) ∈ {0, …, N − 1} for the representative of ψ(g). Then there is a locally constant map b from G to Ω^× with g(b(h)) b(g) = U^{⌊(ψ̄(g) + ψ̄(h))/N⌋} b(gh) for all g, h ∈ G. The 2-cocycle U^{⌊(ψ̄(g) + ψ̄(h))/N⌋} represents the cyclic algebra (ψ, U) in Br(K) = H²(G, Ω^×), so the statement says that this class is zero.

```
U ∈ N_{L/K}(L^×) ⟹ ∃ b ∈ C⁰(G, Ω^×) with U^{⌊(ψ̄(g)+ψ̄(h))/N⌋} = g(b(h)) b(g) b(gh)⁻¹ for all g, h
```

The first reader gives it the kind standard fact and names the published result as follows. The norm criterion for the splitting of a cyclic algebra, in the direction that a norm b from L_χ gives (χ, b) = b ∪ δχ = 0 in Br(K). J.-P. Serre, Local Fields, Graduate Texts in Mathematics 67, 1979.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The splitting of the cyclic algebra (ψ, U) when U is a norm from the cyclic extension cut out by ψ, the easy direction of the isomorphism of K^×/N(L^×) with Br(L/K) for a cyclic extension L/K (Serre, Local Fields XIV §1). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The cocycle U^{⌊(ψ̄(g) + ψ̄(h))/N⌋} is the cup product of U with the coboundary of ψ/N in H²(G, ℤ), and ψ need not be onto ℤ/N, so the fixed field of its kernel can have any degree dividing N.

### 32, `oddWeight_modular_cusp_dimension_lower_bound`

The theorem is `GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddWeightModularCuspDimensionLowerBoundStatement`. Its proof rests on 363 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.OddFrame.dim_lower_bound`.

Let N ≥ 5 and M ≥ 1, let Γ be a subgroup of SL₂(Z) with Γ(M) ⊆ Γ ⊆ Γ₁(N), and let k ≥ 3 be odd. Then the complex spaces M_k(Γ) of modular forms and S_k(Γ) of cusp forms of weight k are finite-dimensional, and k − 1 times the index of Γ in SL₂(Z) is at most 12 (dim M_k(Γ) + dim S_k(Γ)).

```
Γ(M) ⊆ Γ ⊆ Γ₁(N), N ≥ 5, k ≥ 3 odd ⟹ dim M_k(Γ), dim S_k(Γ) < ∞ and (k − 1)[SL₂(Z) : Γ] ≤ 12 (dim_C M_k(Γ) + dim_C S_k(Γ))
```

The first reader gives it the kind standard fact and names the published result as follows. The dimension formulas for modular and cusp forms of odd weight combined with the genus formula, which for such Γ give equality. F. Diamond and J. Shurman, A First Course in Modular Forms, Graduate Texts in Mathematics 228, 2005.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The dimension formulas for modular and cusp forms of odd weight k ≥ 3 on a group without −I, elliptic points or irregular cusps, combined with the genus formula (Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Chapter 2, and Diamond–Shurman, Chapter 3), which give that 12(dim M_k + dim S_k) equals k − 1 times the index of Γ in SL₂(ℤ). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The index is taken in SL₂(ℤ), which is twice the index of the image of Γ in PSL₂(ℤ) because Γ omits −I, and with that index the inequality is in fact an equality.

On emptiness the check wrote this. None found, though the chain Γ(M) ≤ Γ ≤ Γ₁(N) can be met only when N divides M, for example with Γ = Γ₁(N) and M = N.

### 33, `exists_base_element_negative_at_two_embeddings`

The theorem is `GlobalTheory.T.exists_base_element_negative_at_two_embeddings` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddingsStatement`. Its proof rests on 341 declarations, and the five theorems use it.

Let L/K be a quadratic extension of number fields with a ring endomorphism σ ≠ id of L that fixes K and satisfies φ(σx) = conj φ(x) for every complex embedding φ of L. These conditions force K to be totally real and L to be totally imaginary, so L is a CM field with totally real subfield K. Let ε and ε′ be complex embeddings of L with ε′ ≠ ε and ε′ ≠ ε̄, so that they lie over two distinct real places of K. Then there is a nonzero h ∈ K such that ε(h) and ε′(h) have negative real part, φ(h) has positive real part for every embedding φ outside {ε, ε̄, ε′, ε̄′}, and h is a norm from K_v ⊗_K L to K_v at every finite place v of K.

```
L/K CM quadratic, ε, ε′ over distinct real places ⟹ ∃ h ∈ K^× with ε(h), ε′(h) < 0, φ(h) > 0 for φ ∉ {ε, ε̄, ε′, ε̄′}, h ∈ N(K_v ⊗_K L) for every finite v
```

The first reader gives it the kind technical step and names the published result as follows. Existence of a global element with prescribed local Hilbert symbols, here an element that is a local norm from L at every place of K except the two real places below ε and ε′. O. T. O'Meara, Introduction to Quadratic Forms, Grundlehren der mathematischen Wissenschaften 117, 1963, §71.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The existence of a global element with prescribed local Hilbert symbols (O'Meara, Introduction to Quadratic Forms, §71, and Serre, A Course in Arithmetic III Theorem 4 over ℚ), applied to the CM extension L/K with symbol −1 at exactly the two real places below ε and ε′ and +1 at every other place. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The hypotheses on ε and ε′ can be met only when K has at least two real places, so the case K = ℚ is empty, and the norm condition at a finite place v is stated for the algebra K_v ⊗_K L, which is K_v × K_v when v splits in L.

### 34, `exists_signs`

The theorem is `GlobalTheory.QuadSigns.exists_signs` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddings`. Its proof rests on 340 declarations, and the five theorems use it.

Let L/K be a quadratic extension of number fields with a ring endomorphism σ ≠ id of L that fixes K and satisfies φ(σx) = conj φ(x) for every complex embedding φ of L. These conditions force K to be totally real and L to be totally imaginary, so L is a CM field with totally real subfield K. Let ε and ε′ be complex embeddings of L with ε′ ≠ ε and ε′ ≠ ε̄, so that they lie over two distinct real places of K. Then there is a nonzero h ∈ K such that ε(h) and ε′(h) have negative real part, φ(h) has positive real part for every embedding φ outside {ε, ε̄, ε′, ε̄′}, and h is a norm from K_v ⊗_K L to K_v at every finite place v of K.

```
L/K CM quadratic, ε, ε′ over distinct real places ⟹ ∃ h ∈ K^× with ε(h), ε′(h) < 0, φ(h) > 0 for φ ∉ {ε, ε̄, ε′, ε̄′}, h ∈ N(K_v ⊗_K L) for every finite v
```

The first reader gives it the kind technical step and names the published result as follows. Existence of a global element with prescribed local Hilbert symbols, here an element that is a local norm from L at every place of K except the two real places below ε and ε′. O. T. O'Meara, Introduction to Quadratic Forms, Grundlehren der mathematischen Wissenschaften 117, 1963, §71.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The existence of a global element with prescribed local Hilbert symbols (O'Meara, Introduction to Quadratic Forms, §71, and Serre, A Course in Arithmetic III Theorem 4 over ℚ), applied to the CM extension L/K with symbol −1 at exactly the two real places below ε and ε′ and +1 at every other place. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The Lean statement is that of number 33 with the hypotheses named, and its hypotheses on ε and ε′ can be met only when K has at least two real places.

### 35, `mul_norm_of_not_norm`

The theorem is `GlobalTheory.JR.WeilQuad.NormSign.mul_norm_of_not_norm` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOne`. Its proof rests on 314 declarations, and the five theorems use it.

Let K be a nonarchimedean local field of characteristic zero and L a field extension of K of degree 2. If s, t ∈ K^× are both not norms of elements of L, then st is the norm of an element of L.

```
[L : K] = 2, s, t ∈ K^× ∖ N_{L/K}(L) ⟹ st ∈ N_{L/K}(L)
```

The first reader gives it the kind standard fact and names the published result as follows. The norm index theorem for quadratic extensions of local fields, by which N_{L/K}(L^×) has index 2 in K^×. J.-P. Serre, Local Fields, Graduate Texts in Mathematics 67, 1979.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The fact that the norm group of a quadratic extension of a local field has index 2 in K^×, from local class field theory or the nondegeneracy of the Hilbert symbol. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Only the bound of at most 2 on the index enters the Lean conclusion, and the hypothesis CharZero K is more than that bound needs.

### 36, `congr_of_det_norm`

The theorem is `GlobalTheory.LandherrSignature.congr_of_det_norm` in the module `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature`. Its proof rests on 301 declarations, and the five theorems use it.

Let E be a CM number field with its complex conjugation as the star operation, and let G and G′ be n × n matrices over E that are Hermitian for this conjugation and have nonzero determinant. Suppose that det G = z z̄ det G′ for some z ∈ E, and that for every embedding τ of E into C there is a nonsingular complex matrix Q with Q* τ(G) Q = τ(G′), which by Sylvester's law of inertia says that G and G′ have the same signature at every embedding. Then there is a nonsingular matrix P over E with P* G P = G′.

```
G* = G, G′* = G′, det G ∈ N_{E/E⁺}(E) · det G′, τ(G) ≅ τ(G′) over C for all τ ⟹ ∃ P ∈ GL_n(E) with P* G P = G′
```

The first reader gives it the kind named theorem and names the published result as follows. Landherr's theorem on the classification of Hermitian forms over number fields by rank, determinant modulo norms and signatures. W. Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg 11, 1936.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Landherr's theorem that nondegenerate hermitian forms over a quadratic extension of number fields are classified by rank, determinant modulo norms and signatures at the real places that become complex (Landherr 1936, Scharlau, Quadratic and Hermitian Forms, Chapter 10). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The Lean text gives only the sufficiency direction for a CM field over its totally real subfield, and it states the signature condition as congruence over ℂ at every complex embedding, which by Sylvester's law of inertia means equal signatures.

### 37, `exists_eliminationForm_generalLinearForms_cone`

The theorem is `GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsConeStatement`. Its proof rests on 300 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.HSShort.exists_elim_form_of_field`.

Let F be a field of characteristic zero, I a homogeneous prime ideal of F[x₁, …, x_N] whose quotient ring has Krull dimension D + 1 with D ≥ 1, and g a homogeneous polynomial of degree d with g ∉ I. Then there is a nonzero polynomial Q over F in the D·N coefficients s_{ij} of D linear forms with the following property for every field extension K of F. If the D linear forms with coefficients s ∈ K^{D×N} have a common nonzero zero y ∈ K^N on which every element of I and g vanish, then Q(s) = 0. Geometrically, the D-tuples of linear forms whose common zero set meets the projective variety V(I) ∩ V(g) of dimension D − 1 lie in a hypersurface.

```
∃ Q ∈ F[s_{ij}]∖{0} ∀ K ⊇ F ∀ s ∈ K^{D×N} ∀ y ∈ K^N∖{0} (y ∈ V(I), g(y) = 0, Σ_j s_{ij} y_j = 0 ∀ i ⟹ Q(s) = 0)
```

The first reader gives it the kind standard fact and names the published result as follows. Existence of the Chow form, or elimination form, of a projective variety, by which the linear subspaces of complementary dimension that meet the variety form a hypersurface. I. M. Gelfand, M. M. Kapranov and A. V. Zelevinsky, Discriminants, Resultants, and Multidimensional Determinants, 1994.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The existence of an eliminating form of Chow form type for the projective variety V(I) ∩ V(g) of dimension D − 1, by which the D-tuples of hyperplanes that meet a projective variety of dimension D − 1 lie in a hypersurface (Shafarevich, Basic Algebraic Geometry I.6, and the elimination theory of Nesterenko and Philippon). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The Lean text keeps only the vanishing of Q on the tuples that meet the variety and leaves out the converse and the irreducibility of the Chow form, and the hypothesis of characteristic zero is more than the published fact needs.

On emptiness the check wrote this. None found, and for d = 0 the polynomial g is a nonzero constant, so that case holds with any nonzero Q.

### 38, `homogeneous_correction_next_level_alt`

The theorem is `GlobalTheory.T.homogeneous_correction_next_level_alt` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevelStatement`. Its proof rests on 280 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.homogeneous_correction_next_level`.

Let R be a Noetherian ring, I an ideal of R and K₀, K₁, … ideals of R[X₀, …, X_n] with three properties. Each K_e contains every homogeneous F for which each X_i has a power with X_i^N F ∈ K_e, each K_e contains the constants from I^{e+1}, and for every homogeneous F ∈ K_e of degree t and every i there are N and a homogeneous G of degree t + N with coefficients in I^{e+1} such that X_i^N F − G ∈ K_{e+1}. Then there is t₀ such that for every t ≥ t₀, every e and every homogeneous F ∈ K_e of degree t there is a homogeneous G of degree t with coefficients in I^{e+1} and F − G ∈ K_{e+1}.

```
(K_e saturated, I^{e+1} ⊆ K_e, ∀ F ∈ (K_e)_t ∀ i ∃ N, G_i ∈ (I^{e+1}R[X])_{t+N} with X_i^N F − G_i ∈ K_{e+1}) ⟹ ∃ t₀ ∀ t ≥ t₀ ∀ e ∀ F ∈ (K_e)_t ∃ G ∈ (I^{e+1}R[X])_t with F − G ∈ K_{e+1}
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a gluing lemma of Serre vanishing type that turns corrections on the standard affine charts of projective space into one global correction in large degree, uniformly in e.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a gluing lemma that in every large degree t, uniformly in e, writes each homogeneous element of K_e modulo K_{e+1} as one with coefficients in I^{e+1}, a consequence of Serre's theorem on graded modules applied over the associated graded ring of I. For the relation to that result the check has none, the first reader none and the second reader weaker.

The check adds this. The three hypotheses together give I·K_e ⊆ K_{e+1} on homogeneous elements, and this inclusion is what lets a single bound t₀ serve every e.

### 39, `uniform_serre_sections_alt`

The theorem is `GlobalTheory.T.uniform_serre_sections_alt` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreSectionsStatement`. Its proof rests on 276 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.uniform_serre_sections`.

Let R be a Noetherian ring, I an ideal of R and J₀, J₁, … ideals of R[X₀, …, X_n] such that a F ∈ J_{e+1} whenever a ∈ I and F is a homogeneous polynomial in J_e with coefficients in I^e. Then there is d₀ such that the following holds for every d ≥ d₀, every e and every N. If F₀, …, F_n are homogeneous of degree d + N with coefficients in I^e and for all i, j some power of X_i X_j times X_j^N F_i − X_i^N F_j lies in J_e, then there is a homogeneous G of degree d with coefficients in I^e such that for each i some power of X_i times F_i − X_i^N G lies in J_e. In sheaf language, compatible local sections F_i / X_i^N on the charts D₊(X_i) come from one homogeneous polynomial of degree d, with d₀ independent of e and N.

```
∃ d₀ ∀ d ≥ d₀ ∀ e, N ∀ F_i ∈ (I^e R[X])_{d+N} ((X_iX_j)^L (X_j^N F_i − X_i^N F_j) ∈ J_e ∀ i, j ⟹ ∃ G ∈ (I^e R[X])_d with X_i^L (F_i − X_i^N G) ∈ J_e ∀ i)
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a version of Serre's theorem that M_d → Γ(ℙ^n, M̃(d)) is surjective for large d, made uniform over the modules I^e R[X] modulo J_e.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Serre's theorem that for a finitely generated graded module M over a polynomial ring over a Noetherian base the map M_d → Γ(ℙ^n, M̃(d)) is onto for large d (Serre's FAC, Hartshorne II Exercise 5.9), applied to the modules I^e R[X] modulo J_e assembled over the Rees algebra of I so that the bound is uniform in e. For the relation to that result the check has weaker, the first reader none and the second reader weaker.

The check adds this. The hypothesis that a·F lies in J_{e+1} for a in I and homogeneous F in J_e with coefficients in I^e is what makes the direct sum of these modules a module over the Rees algebra, and the bound d₀ is uniform in N as well as in e.

### 40, `subsingleton_groupCohomology_three_of_tate`

The theorem is `GroundTheory.ProfCoh.subsingleton_groupCohomology_three_of_tate` in the module `GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.TateThree`. Its proof rests on 274 declarations, and the five theorems use it.

Let Γ be a finite group, M a Γ-module and u ∈ H²(Γ, M). Suppose that for every subgroup S of Γ the group H¹(S, M) is zero, the restriction of u to S has additive order |S|, and every element of H²(S, M) is an integer multiple of that restriction. Then H³(Γ, M) = 0.

```
∀ S ≤ Γ (H¹(S, M) = 0, H²(S, M) = ⟨res_S u⟩ ≅ Z/|S|) ⟹ H³(Γ, M) = 0
```

The first reader gives it the kind standard fact and names the published result as follows. Tate's theorem on cup product with a fundamental class, which gives H³(Γ, M) ≅ Ĥ¹(Γ, Z) = Hom(Γ, Z) = 0. J. Tate, The higher dimensional cohomology groups of class field theory, Annals of Mathematics 56, 1952.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Tate's theorem on cup product with a fundamental class (Tate–Nakayama), by which cup product with u gives isomorphisms from Ĥ^n(Γ, ℤ) to Ĥ^{n+2}(Γ, M), here at n = 1 where Ĥ¹(Γ, ℤ) = Hom(Γ, ℤ) = 0. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypotheses on u say that for every subgroup S the group H²(S, M) is cyclic of order |S| and generated by the restriction of u, which are exactly Tate's hypotheses, and the Lean conclusion is only the case n = 1.

### 41, `subsingleton_groupCohomology_three_of_tate_int`

The theorem is `GroundTheory.ProfCoh.subsingleton_groupCohomology_three_of_tate_int` in the module `GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.TateThree`. Its proof rests on 265 declarations, and the five theorems use it.

Let Γ be a finite group, M a representation of Γ over ℤ and u a class in H²(Γ, M). Assume that for every subgroup S of Γ the group H¹(S, M) is zero, the restriction of u to H²(S, M) has additive order equal to the order of S, and every element of H²(S, M) is an integer multiple of that restriction. Then H³(Γ, M) has at most one element, so it is the zero group.

```
Γ finite, M ∈ Rep_ℤ(Γ), u ∈ H²(Γ,M), and for all S ≤ Γ, H¹(S,M) = 0, ord(res_S u) = |S|, H²(S,M) = ℤ·res_S u ⟹ H³(Γ,M) = 0
```

The first reader gives it the kind standard fact and names the published result as follows. The degree-three case of Tate's theorem, in which cup product with u gives an isomorphism Ĥ¹(Γ,ℤ) ≅ H³(Γ,M) and Ĥ¹(Γ,ℤ) = Hom(Γ,ℤ) vanishes because Γ is finite. J. Tate, The higher dimensional cohomology groups of class field theory, Annals of Mathematics 56 (1952).

The second reader gives it the kind technical step and the check the kind standard fact. The check names the published result as follows. The degree-three case of Tate's theorem on a class in H² whose restrictions generate H² of every subgroup with order equal to the subgroup's order (Tate 1952), which gives H³(Γ, M) ≅ Ĥ¹(Γ, ℤ) = Hom(Γ, ℤ) = 0. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypotheses are exactly those of Tate's theorem taken at every subgroup, and the Lean statement keeps only the vanishing of H³ that the isomorphism Ĥ¹(Γ, ℤ) ≅ H³(Γ, M) gives.

### 42, `unit_prod`

The theorem is `ReciprocityTheory.ChartRestriction.L1.unit_prod` in the module `ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValB`. Its proof rests on 258 declarations, and the five theorems use it.

Let L be a lattice in ℂ with Weierstrass invariants g₂, g₃ and Weierstrass function ℘, let l ≥ 5 be a prime, ι a field isomorphism from ℂ to ℂ_l, and μ ∈ ℂ_l with μ¹²ι(g₂³ − 27g₃²) = 1, |μ⁴ι(g₂)| ≤ 1 and |μ⁶ι(g₃)| ≤ 1. Let e and N be natural numbers such that e = 3 and |μ⁴ι(g₂)| < 1, or e = 2 and |μ⁶ι(g₃)| < 1, and such that neither l nor e divides N. Then for every finite set T of complex numbers z with z ∉ L and Nz ∈ L, the product |μ|^{2|T|}·|ι(∏_{z∈T} ℘(z))| of l-adic absolute values equals 1. The hypotheses on μ say that the model y² = 4x³ − μ⁴ι(g₂)x − μ⁶ι(g₃) of the curve has good reduction at l, with reduced j-invariant 0 when e = 3 and 1728 when e = 2.

```
l ≥ 5 prime, μ¹²ι(g₂³−27g₃²) = 1, |μ⁴ιg₂|, |μ⁶ιg₃| ≤ 1, (e = 3 and |μ⁴ιg₂| < 1) or (e = 2 and |μ⁶ιg₃| < 1), l ∤ N, e ∤ N, T ⊂ N⁻¹L ∖ L finite ⟹ |μ|^{2|T|}·|ι(∏_{z∈T} ℘_L(z))|_l = 1
```

The first reader gives it the kind technical step and names the published result as follows. The product over a finite set of nonzero N-torsion points of the unit statement of Theorem 43, which rests on the integrality of torsion points of order prime to l on an elliptic curve with good reduction and on the injectivity of reduction on such torsion. J. H. Silverman, The Arithmetic of Elliptic Curves, 1986.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a product form of the lemma that the rescaled x-coordinates of the nonzero N-torsion points of an elliptic curve with good reduction at l and reduced j-invariant 0 or 1728 are l-adic units. For the relation to that result the check has none, the first reader different and the second reader none.

The check adds this. The statement follows from Theorem 43 by the multiplicativity of ι and of the l-adic norm, and the hypotheses can be met, for example by the hexagonal lattice with g₂ = 0, e = 3 and N = 2.

### 43, `unit_point`

The theorem is `ReciprocityTheory.ChartRestriction.L1.unit_point` in the module `ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedValB`. Its proof rests on 257 declarations, and the five theorems use it.

Let L be a lattice in ℂ with Weierstrass invariants g₂, g₃ and Weierstrass function ℘, let l ≥ 5 be a prime, ι a field isomorphism from ℂ to ℂ_l, and μ ∈ ℂ_l with μ¹²ι(g₂³ − 27g₃²) = 1, |μ⁴ι(g₂)| ≤ 1 and |μ⁶ι(g₃)| ≤ 1. Let e and N be natural numbers such that e = 3 and |μ⁴ι(g₂)| < 1, or e = 2 and |μ⁶ι(g₃)| < 1, and such that neither l nor e divides N. Then every complex number z with z ∉ L and Nz ∈ L satisfies |μ²ι(℘(z))| = 1 for the l-adic absolute value. In terms of the model y² = 4x³ − μ⁴ι(g₂)x − μ⁶ι(g₃), which has good reduction at l, the x-coordinate of every nonzero N-torsion point is an l-adic unit.

```
l ≥ 5 prime, μ¹²ι(g₂³−27g₃²) = 1, |μ⁴ιg₂|, |μ⁶ιg₃| ≤ 1, (e = 3 and |μ⁴ιg₂| < 1) or (e = 2 and |μ⁶ιg₃| < 1), l ∤ N, e ∤ N, z ∉ L, Nz ∈ L ⟹ |μ²ι(℘_L(z))|_l = 1
```

The first reader gives it the kind technical step and names the published result as follows. The integrality of torsion points of order prime to l on an elliptic curve with good reduction and the injectivity of reduction on such torsion, combined with the fact that the points with x = 0 on the reduced curve have order 3 when j = 0 and order 2 when j = 1728. J. H. Silverman, The Arithmetic of Elliptic Curves, 1986.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a lemma that combines the injectivity of reduction on torsion of order prime to l for an elliptic curve with good reduction (Silverman, AEC VII.3.1) with the orders of the points with x = 0 on reduced curves with j-invariant 0 or 1728. For the relation to that result the check has none, the first reader different and the second reader none.

The check adds this. The hypotheses on μ say that the rescaled model y² = 4x³ − μ⁴ι(g₂)x − μ⁶ι(g₃) has good reduction at l with reduced j-invariant 0 when e = 3 and 1728 when e = 2, and the condition that e does not divide N excludes the torsion points that reduce to a point with x = 0, which have order 3 or 2.

### 44, `torsion_ext`

The theorem is `GlobalTheory.UU.SpecialPairing.torsion_ext` in the module `Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PairingNondegenerate`. Its proof rests on 256 declarations, and the five theorems use it.

Let W be a local ring that is complete for its maximal ideal, S a scheme, G a smooth commutative group scheme over S, p a morphism from Spec W to S, and N a natural number that is a unit in W. Let f be a local ring homomorphism from W to a field Ω, so that Spec Ω maps to the closed point of Spec W. If two W-points y and y' of G over p satisfy y^N = 1 and y'^N = 1 and agree after composition with the morphism Spec Ω → Spec W induced by f, then y = y'.

```
G/S smooth commutative group scheme, W complete local, N ∈ W^×, f ∈ Hom_loc(W, Ω), y, y' ∈ G(W) over p, y^N = y'^N = 1, y ∘ Spec f = y' ∘ Spec f ⟹ y = y'
```

The first reader gives it the kind standard fact and names the published result as follows. Injectivity of reduction on torsion of order invertible in the base for a smooth commutative group scheme over a local ring, which holds because the N-torsion subgroup scheme is étale. S. Bosch, W. Lütkebohmert and M. Raynaud, Néron Models, 1990.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Injectivity of reduction on N-torsion points of a smooth commutative group scheme over a local ring in which N is invertible, which comes from the étaleness of the N-torsion subgroup scheme. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The completeness of W is not needed for this uniqueness, because the N-torsion of G is unramified over Spec W and two points of an unramified scheme over a local base that agree at the closed point agree everywhere.

### 45, `etale_atPrime_of_regular_of_isIntegrallyClosedIn`

The theorem is `GlobalTheory.T.etale_atPrime_of_regular_of_isIntegrallyClosedIn` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeOfRegularOfIsIntegrallyClosedInStatement`. Its proof rests on 254 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.PurityLoc.etale_atPrime_of_isIntegrallyClosedIn`.

Let R be a domain and C a commutative R-algebra that is finite as an R-module and integrally closed in its localization at the nonzero elements of R. Let P be a prime of R such that the localization R_P is a regular local ring. If C ⊗_R R_{P'} is étale over R_{P'} for every prime P' ⊆ P of height at most one, then C ⊗_R R_P is étale over R_P.

```
R domain, C finite R-algebra integrally closed in C ⊗_R Frac(R), R_P regular, C_{P'} étale over R_{P'} for all primes P' ⊆ P with ht P' ≤ 1 ⟹ C_P étale over R_P
```

The first reader gives it the kind named theorem and names the published result as follows. The Zariski–Nagata purity of the branch locus. M. Nagata, On the purity of branch loci in regular local rings, Illinois Journal of Mathematics 3 (1959).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski–Nagata purity of the branch locus. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. No Noetherian hypothesis is placed on R itself, which costs nothing because only the regular local ring R_P and the primes inside P enter, and the hypothesis at P' = 0 supplies the generic étaleness that purity needs.

On emptiness the check wrote this. None found, although when P has height at most one the conclusion is the hypothesis taken at P' = P.

### 46, `existsUnique_torsion_lift`

The theorem is `GlobalTheory.existsUnique_torsion_lift` in the module `Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete`. Its proof rests on 254 declarations, and the five theorems use it.

Let W be a local ring that is complete for its maximal ideal, with residue field k, let S be a scheme, G a smooth commutative group scheme over S, p a morphism from Spec W to S, and N a natural number that is a unit in W. For every k-point x₀ of G over the composite Spec k → Spec W → S with x₀^N = 1 there is exactly one W-point x of G over p with x^N = 1 whose restriction to Spec k is x₀.

```
G/S smooth commutative group scheme, W complete local with residue field k, N ∈ W^×, x₀ ∈ G(k), x₀^N = 1 ⟹ ∃! x ∈ G(W) with x^N = 1 and x|_{Spec k} = x₀
```

The first reader gives it the kind standard fact and names the published result as follows. Unique lifting of N-torsion points from the residue field to a henselian local ring, that is the bijectivity of G[N](W) → G[N](k) for the étale group scheme G[N] when N is invertible. S. Bosch, W. Lütkebohmert and M. Raynaud, Néron Models, 1990.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Bijectivity of reduction on N-torsion points over a henselian local ring when N is invertible, from the étaleness of the N-torsion subgroup scheme and Hensel's lemma (EGA IV 18.5). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Existence of the lift uses that a complete local ring is henselian, and its uniqueness holds over any local ring in which N is invertible, as in Theorem 44.

### 47, `uniform_serre_vanishing_cech_cocycles`

The theorem is `GlobalTheory.T.uniform_serre_vanishing_cech_cocycles` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocyclesStatement`. Its proof rests on 253 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.uniformSerre_cocycle`.

Let R be a Noetherian ring, I an ideal of R, and J_e for e ∈ ℕ ideals of S = R[X_0,…,X_n] such that for every a ∈ I and every homogeneous form F ∈ J_e whose coefficients lie in I^e the product aF lies in J_{e+1}. Then there is d₀ such that for all d ≥ d₀, all e and all N, every family of forms F_{ij} of degree d + 2N with coefficients in I^e for which X_l^N F_{ij} + X_i^N F_{jl} − X_j^N F_{il} lies in J_e after multiplication by a power of X_iX_jX_l is a Čech coboundary with coefficients in I^e. That means there are N' and forms G_i of degree d + N' with coefficients in I^e such that (X_iX_j)^{N'}F_{ij} − (X_iX_j)^N(X_j^{N'}G_i − X_i^{N'}G_j) lies in J_e after multiplication by a power of X_iX_j.

```
∃ d₀ ∀ d ≥ d₀ ∀ e ∀ N, every Čech 1-cocycle (F_{ij}/(X_iX_j)^N) of (S/J_e)~(d) with F_{ij} ∈ I^e·S_{d+2N} is the coboundary of some (G_i/X_i^{N'}) with G_i ∈ I^e·S_{d+N'}
```

The first reader gives it the kind technical step and names the published result as follows. Serre's vanishing theorem for the first cohomology of twisted coherent sheaves on projective space, applied over the Rees algebra R[It] so that the bound d₀ is uniform along the I-adic filtration. J.-P. Serre, Faisceaux algébriques cohérents, Annals of Mathematics 61 (1955).

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Serre's vanishing theorem for H¹ of twisted coherent sheaves on projective space, applied over the Rees algebra of I so that the bound d₀ is uniform in e and written with Čech cocycles of the standard affine cover. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The ideals J e are not assumed homogeneous, which costs nothing because every element that the statement tests for membership in some J e is homogeneous.

### 48, `desc_sub`

The theorem is `Formalism.MainNotions.LiftingTheory.desc_sub` in the module `Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation`. Its proof rests on 251 declarations, and the five theorems use it.

Let ℓ be a prime and O a commutative ℤ_ℓ-algebra, and let H₁, H₂, H₁', H₂' be O-modules with submodules Hf₁, Hf₂, Hf₁', Hf₂' and with O-linear maps h from H₁ to H₂, h' from H₁' to H₂', res₂ from H₂' to H₂, cor₁ from H₁ to H₁' and cor₂ from H₂ to H₂'. Assume that g > 0, cor₂ ∘ res₂ is multiplication by g, h' ∘ cor₁ = cor₂ ∘ h, res₂ maps Hf₂' into Hf₂, cor₁ maps Hf₁ into Hf₁', and every κ ∈ Hf₂ satisfies ℓ^E·κ = h(κ₁) for some κ₁ ∈ Hf₁. Then every κ' ∈ Hf₂' satisfies ℓ^{E + v_ℓ(g)}·κ' = h'(κ₁') for some κ₁' ∈ Hf₁', where v_ℓ is the ℓ-adic valuation.

```
cor₂∘res₂ = g, h'∘cor₁ = cor₂∘h, res₂(Hf₂') ⊆ Hf₂, cor₁(Hf₁) ⊆ Hf₁', ℓ^E·Hf₂ ⊆ h(Hf₁) ⟹ ℓ^{E+v_ℓ(g)}·Hf₂' ⊆ h'(Hf₁')
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, an elementary restriction and corestriction lemma for modules over a ℤ_ℓ-algebra.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, an elementary restriction and corestriction lemma for modules over a ℤ_ℓ-algebra. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The proof applies the last hypothesis to res₂ κ', pushes the result through cor₁ and divides by the part of g prime to ℓ, which is invertible in O because it is a unit of ℤ_ℓ.

### 49, `exists_places`

The theorem is `GlobalTheory.ChevalleySUnits.exists_places` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField`. Its proof rests on 251 declarations, and the five theorems use it.

Let E be a number field, S a finite set of nonzero primes of its ring of integers and m a positive integer. Then there is a finite set T of nonzero primes, disjoint from S, such that every x ∈ E^× that is a unit at every prime outside S and satisfies x ≡ 1 modulo every t ∈ T is an m-th power of an element of E.

```
∃ T finite with T ∩ S = ∅ such that ∀ x ∈ O_{E,S}^×, (x ≡ 1 mod t for all t ∈ T) ⟹ x ∈ (E^×)^m
```

The first reader gives it the kind named theorem and names the published result as follows. Chevalley's theorem that every subgroup of finite index in a finitely generated subgroup of the multiplicative group of a number field contains a congruence subgroup, here for the S-unit group and its subgroup of m-th powers. C. Chevalley, Deux théorèmes d'arithmétique, Journal of the Mathematical Society of Japan 3 (1951).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Chevalley's theorem that every subgroup of finite index in the S-unit group of a number field contains a congruence subgroup, here for the subgroup of m-th powers. For the relation to that result the check has special case, the first reader special case and the second reader stronger.

The check adds this. The Lean form asks for a modulus made of distinct primes outside S, which the usual statement does not mention but which follows from a Chevalley modulus prime to S and to m by raising x to a power prime to m.

### 50, `etale_integralClosure_of_isArtinianRing`

The theorem is `GlobalTheory.PurityProd.etale_integralClosure_of_isArtinianRing` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing`. Its proof rests on 249 declarations, and the five theorems use it.

Let A be a regular local ring and E a reduced Artinian A-algebra on which nonzero elements of A act injectively, and assume that the integral closure B of A in E is a finite A-module. If B ⊗_A A_q is étale over A_q for every prime q of A of height at most one, then B is étale over A.

```
A regular local, E reduced Artinian and torsion-free over A, B = integral closure of A in E finite over A, B_q étale over A_q for all primes q with ht q ≤ 1 ⟹ B étale over A
```

The first reader gives it the kind named theorem and names the published result as follows. The Zariski–Nagata purity of the branch locus. M. Nagata, On the purity of branch loci in regular local rings, Illinois Journal of Mathematics 3 (1959).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski–Nagata purity of the branch locus. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. Torsion-freeness makes the reduced Artinian ring E an algebra over the fraction field K of A, and the hypothesis at q = 0 makes the integral closure tensored with K a finite étale K-algebra, which is the setting of purity.

On emptiness the check wrote this. None found, although when A has dimension at most one the conclusion is the hypothesis at the maximal ideal up to the isomorphism of A with its localization there.

### 51, `exists_homogeneous_form_of_compatible_fractions`

The theorem is `GlobalTheory.T.exists_homogeneous_form_of_compatible_fractions` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfCompatibleFractionsStatement`. Its proof rests on 249 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.exists_form_of_compatible_fractions`.

Let A be a Noetherian ring and J a homogeneous ideal of S = A[X_0,…,X_n]. Then there is d₀ such that for every d ≥ d₀ and every N, every family of forms F_i of degree d + N for which X_j^N F_i − X_i^N F_j lies in J after multiplication by a power of X_iX_j comes from a single form G of degree d. That means X_i^L(F_i − X_i^N G) lies in J for some L, for every i, so the fractions F_i/X_i^N all equal G in the localizations of S/J.

```
∃ d₀ ∀ d ≥ d₀, the map (S/J)_d → Γ(P^n_A, (S/J)~(d)) is surjective, with a global section written as fractions F_i/X_i^N, deg F_i = d + N, that agree on D(X_iX_j)
```

The first reader gives it the kind standard fact and names the published result as follows. The fact that the natural map M_d → Γ(P^n, M~(d)) is an isomorphism for d large, here its surjectivity for M = S/J. R. Hartshorne, Algebraic Geometry, 1977.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The theorem that M_d → Γ(Pⁿ, M~(d)) is an isomorphism for large d when M is a finitely generated graded module (Hartshorne, Exercise II.5.9), here its surjectivity for M = A[X_0,…,X_n]/J. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The homogeneity hypothesis on J costs nothing, because every element that the statement tests for membership in J is homogeneous.

### 52, `core`

The theorem is `GlobalTheory.ChevalleyUnitsProof.core` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits`. Its proof rests on 247 declarations, and the five theorems use it.

Let E be a number field, l a prime, r a natural number and b a positive integer. Then there is a positive integer a coprime to b such that every unit u of the ring of integers of E with u − 1 divisible by a is the l^r-th power of a unit.

```
∃ a ∈ ℕ, a > 0, gcd(a, b) = 1, ∀ u ∈ O_E^×, u ≡ 1 (mod a·O_E) ⟹ ∃ v ∈ O_E^×, u = v^{l^r}
```

The first reader gives it the kind technical step and names the published result as follows. Chevalley's theorem that every subgroup of finite index in the unit group of a number field contains a congruence subgroup, here for the subgroup of l^r-th powers with a modulus prime to b. C. Chevalley, Deux théorèmes d'arithmétique, Journal of the Mathematical Society of Japan 3 (1951).

The second reader gives it the kind named theorem and the check the kind technical step. The check names the published result as follows. Chevalley's theorem on units of a number field, that for every exponent n some integer modulus makes each unit congruent to 1 an n-th power of a unit, here for prime-power exponents and a modulus prime to a given b. For the relation to that result the check has special case, the first reader special case and the second reader stronger.

The check adds this. The coprimality of the modulus with b is more than the usual statement on units asserts, but it follows from the S-unit form of Chevalley's theorem with S the primes dividing b, and the restriction to exponents l^r loses nothing because the statement covers every prime l and every r.

### 53, `mem_span_sup_pow_of_forall_complete_dvr_local_test`

The theorem is `GlobalTheory.T.mem_span_sup_pow_of_forall_complete_dvr_local_test` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanSupPowOfForallCompleteDvrLocalTestStatement`. Its proof rests on 247 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr`.

Let O be a local normal domain of characteristic zero that is essentially of finite type over ℤ, with maximal ideal 𝔪, let g ∈ O be nonzero, and let (b_n) be a sequence in O with b_m − b_n ∈ 𝔪^m whenever m ≤ n. Assume that for every complete discrete valuation ring V of characteristic zero and every injective local homomorphism ρ from O to V one has ρ(b_e) ∈ ρ(g)V + 𝔪_V^e for every e. Then b_n ∈ gO + 𝔪^n for every n. In other words, the limit of (b_n) in the completion of O lies in the principal ideal generated by g as soon as its image does under every such map.

```
(b_n) 𝔪-adically Cauchy, and for all complete DVRs V of characteristic 0 and all injective local ρ ∈ Hom(O, V), ρ(b_e) ∈ (ρ(g)) + 𝔪_V^e for all e ⟹ b_n ∈ (g) + 𝔪^n for all n
```

The first reader gives it the kind technical step and names the published result as follows. A test of membership in a principal ideal of the completion by maps into complete discrete valuation rings, akin to the valuative criterion for integral closure of ideals applied to the analytically normal completion of an excellent normal local domain. I. Swanson and C. Huneke, Integral Closure of Ideals, Rings, and Modules, 2006.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a valuative test of membership in a principal ideal of the completion of an excellent normal local domain. For the relation to that result the check has none, the first reader different and the second reader none.

The check adds this. The statement says that the limit of the Cauchy sequence b in the completion of O lies in g times the completion whenever every complete discrete valuation ring of characteristic zero that dominates O sees this, and it rests on the completion being a normal domain because O is excellent.

### 54, `exists_places_of_fg`

The theorem is `GlobalTheory.ChevalleySUnits.exists_places_of_fg` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField`. Its proof rests on 245 declarations, and the five theorems use it.

Let E be a number field, Γ a finitely generated subgroup of E^×, S a finite set of nonzero primes of the ring of integers of E and m a positive integer. Then there is a finite set T of nonzero primes, disjoint from S, such that every x ∈ Γ with x ≡ 1 modulo every t ∈ T is an m-th power of an element of E.

```
Γ ≤ E^× finitely generated ⟹ ∃ T finite with T ∩ S = ∅ such that ∀ x ∈ Γ, (x ≡ 1 mod t for all t ∈ T) ⟹ x ∈ (E^×)^m
```

The first reader gives it the kind named theorem and names the published result as follows. Chevalley's theorem that every subgroup of finite index in a finitely generated subgroup of the multiplicative group of a number field contains a congruence subgroup. C. Chevalley, Deux théorèmes d'arithmétique, Journal of the Mathematical Society of Japan 3 (1951).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Chevalley's theorem that every subgroup of finite index in a finitely generated subgroup Γ of E^× contains a congruence subgroup. For the relation to that result the check has weaker, the first reader weaker and the second reader stronger.

The check adds this. The conclusion asks only for an m-th root in E and not in Γ, and the modulus made of distinct primes outside S follows from a Chevalley modulus prime to S and to m by raising x to a power prime to m.

### 55, `core`

The theorem is `GlobalTheory.ChevalleySUnits.core` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerField`. Its proof rests on 244 declarations, and the five theorems use it.

Let E be a number field, Γ a finitely generated subgroup of E^×, S a finite set of nonzero primes of the ring of integers of E, l a prime and r a natural number. Then there is a finite set T of nonzero primes, disjoint from S, such that every x ∈ Γ with x ≡ 1 modulo every t ∈ T is an l^r-th power of an element of E.

```
Γ ≤ E^× finitely generated, l prime ⟹ ∃ T finite with T ∩ S = ∅ such that ∀ x ∈ Γ, (x ≡ 1 mod t for all t ∈ T) ⟹ x ∈ (E^×)^{l^r}
```

The first reader gives it the kind technical step and names the published result as follows. Chevalley's theorem that every subgroup of finite index in a finitely generated subgroup of the multiplicative group of a number field contains a congruence subgroup, here for the exponent l^r. C. Chevalley, Deux théorèmes d'arithmétique, Journal of the Mathematical Society of Japan 3 (1951).

The second reader gives it the kind named theorem and the check the kind technical step. The check names the published result as follows. Chevalley's theorem on congruence subgroups of a finitely generated subgroup of E^×, for the exponent l^r. For the relation to that result the check has weaker, the first reader weaker and the second reader stronger.

The check adds this. The statement is Theorem 54 for the exponent l^r, and since it covers every prime l and every r it gives Theorem 54 back by combining the prime-power cases.

### 56, `etale_of_etale_height_one_of_regularLocalRing`

The theorem is `GlobalTheory.T.etale_of_etale_height_one_of_regularLocalRing` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRingStatement`. Its proof rests on 243 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.BranchPurity.etale_of_etale_height_one`.

Let R be a Noetherian local domain whose maximal ideal is generated by dim R elements, so that R is regular, with dim R ≥ 1 and R not a field. Let A be an integrally closed domain that is a finite and faithful R-algebra. If A ⊗_R R_p is étale over R_p for every prime p of R of height one, then A is étale over R.

```
R regular local, dim R ≥ 1, A normal domain finite and faithful over R, A_p étale over R_p for all primes p with ht p = 1 ⟹ A étale over R
```

The first reader gives it the kind named theorem and names the published result as follows. The Zariski–Nagata purity of the branch locus. M. Nagata, On the purity of branch loci in regular local rings, Illinois Journal of Mathematics 3 (1959).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski–Nagata purity of the branch locus. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The assumption that R is not a field repeats the assumption dim R ≥ 1, and étaleness at the height-one primes already gives étaleness at the generic point, which purity needs.

On emptiness the check wrote this. None found, although in dimension one the conclusion is the hypothesis at the maximal ideal up to the isomorphism of R with its localization there.

### 57, `finiteRing_sq_sub_mul_sq_eq_of_card`

The theorem is `GlobalTheory.BranchPurity.finiteRing_sq_sub_mul_sq_eq_of_card` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleHeightOneOfRegularLocalRing`. Its proof rests on 241 declarations, and the five theorems use it.

For every natural number n, let R be a Noetherian local domain whose maximal ideal needs exactly n generators and whose Krull dimension equals that number of generators, so that R is regular, and assume that R is not a field. Let A be an integrally closed domain that is a finite and faithful R-algebra. If A ⊗_R R_p is étale over R_p for every prime p of R of height one, then A is étale over R. The name of the theorem refers to finite rings and to a difference of squares, which does not describe this content.

```
R regular local and not a field, A normal domain finite and faithful over R, A_p étale over R_p for all primes p with ht p = 1 ⟹ A étale over R
```

The first reader gives it the kind named theorem and names the published result as follows. The Zariski–Nagata purity of the branch locus. M. Nagata, On the purity of branch loci in regular local rings, Illinois Journal of Mathematics 3 (1959).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski–Nagata purity of the branch locus. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The variable n only names the number of generators of the maximal ideal and constrains nothing, the hypothesis dim R ≥ 1 of Theorem 56 is dropped because a regular local ring that is not a field has positive dimension, and the name of the theorem does not describe its content.

On emptiness the check wrote this. None found, although in dimension one the conclusion is the hypothesis at the maximal ideal up to the isomorphism of R with its localization there.

### 58, `orthonormal_of_diagonal`

The theorem is `GlobalTheory.OddGenus.orthonormal_of_diagonal` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis`. Its proof rests on 225 declarations, and the five theorems use it.

Let K be a number field containing θ with θ² = −d for a positive integer d and such that every element of K is a + bθ with rational a and b, so that K is the imaginary quadratic field ℚ(√−d), and let σ be a ring endomorphism of K with σ(θ) = −θ, which is complex conjugation. Let h be a form on a K-vector space V that is K-linear in the first argument and σ-semilinear in the second. If vectors v_1,…,v_r satisfy h(v_i, v_j) = a_i δ_{ij} with positive rationals a_i whose product is a square in ℚ, then there are vectors e_1,…,e_r in V with h(e_i, e_j) = δ_{ij}.

```
K = ℚ(√−d), h sesquilinear on V, h(v_i, v_j) = a_i δ_{ij} with a_i ∈ ℚ_{>0} and ∏ a_i ∈ (ℚ^×)² ⟹ ∃ e_1,…,e_r ∈ V with h(e_i, e_j) = δ_{ij}
```

The first reader gives it the kind technical step and names the published result as follows. Landherr's theorem that Hermitian forms over a quadratic extension of number fields are classified by rank, determinant modulo norms and signatures, here for a positive definite diagonal form with square determinant, which is therefore isometric to the unit form. W. Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg 11 (1936).

The second reader gives it the kind standard fact and the check the kind technical step. The check names the published result as follows. Landherr's theorem classifying Hermitian forms over a quadratic extension of number fields by rank, determinant modulo norms and signatures, here for a positive definite diagonal form over an imaginary quadratic field with square determinant. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The form h is assumed neither Hermitian nor nondegenerate on V, which costs nothing because the vectors e_i can be found in the span of the v_i, where the Gram matrix of h is the positive diagonal matrix of the a_i.

### 59, `exists_coboundary_of_fraction_cocycle_homogeneous_ideal`

The theorem is `GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement`. Its proof rests on 225 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.exists_coboundary_of_cocycle_homogeneous`.

Let A be a Noetherian ring and J a homogeneous ideal of S = A[X_0,…,X_n]. Then there is d₀ such that for every d ≥ d₀ and every N, every family of forms F_{ij} of degree d + 2N for which X_l^N F_{ij} + X_i^N F_{jl} − X_j^N F_{il} lies in J after multiplication by a power of X_iX_jX_l is a Čech coboundary. That means there are N' and forms G_i of degree d + N' such that (X_iX_j)^{N'}F_{ij} − (X_iX_j)^N(X_j^{N'}G_i − X_i^{N'}G_j) lies in J after multiplication by a power of X_iX_j.

```
∃ d₀ ∀ d ≥ d₀, Ȟ¹({D(X_i)}, (S/J)~(d)) = 0 on P^n_A, with cochains written as fractions F_{ij}/(X_iX_j)^N
```

The first reader gives it the kind named theorem and names the published result as follows. Serre's vanishing theorem, here for the first Čech cohomology of the twisted structure sheaf of a closed subscheme of P^n_A in the standard affine cover. J.-P. Serre, Faisceaux algébriques cohérents, Annals of Mathematics 61 (1955).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Serre's vanishing theorem, here for H¹ of the twists of the structure sheaf of the closed subscheme V(J) of Pⁿ_A, written with Čech cocycles of the standard affine cover. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The fractions F_{ij}/(X_iX_j)^N with F_{ij} of degree d + 2N are the Čech 1-cochains of (S/J)~(d) for the standard affine cover, and the homogeneity hypothesis on J costs nothing because every element tested for membership in J is homogeneous.

### 60, `exists_orthonormal_hermitian_of_diag_pos_isSquare`

The theorem is `GlobalTheory.T.exists_orthonormal_hermitian_of_diag_pos_isSquare` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalHermitianOfDiagPosIsSquareStatement`. Its proof rests on 224 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare`.

Let K be a number field containing θ with θ² = −d for a positive integer d and such that every element of K is a + bθ with rational a and b, so that K is the imaginary quadratic field ℚ(√−d), and let σ be a ring endomorphism of K with σ(θ) = −θ, which is complex conjugation. Let h be a form on a K-vector space V that is K-linear in the first argument and σ-semilinear in the second. If vectors v_1,…,v_r satisfy h(v_i, v_j) = a_i δ_{ij} with positive rationals a_i whose product is a square in ℚ, then there are vectors e_1,…,e_r in V with h(e_i, e_j) = δ_{ij}.

```
K = ℚ(√−d), h sesquilinear on V, h(v_i, v_j) = a_i δ_{ij} with a_i ∈ ℚ_{>0} and ∏ a_i ∈ (ℚ^×)² ⟹ ∃ e_1,…,e_r ∈ V with h(e_i, e_j) = δ_{ij}
```

The first reader gives it the kind technical step and names the published result as follows. Landherr's theorem that Hermitian forms over a quadratic extension of number fields are classified by rank, determinant modulo norms and signatures, here for a positive definite diagonal form with square determinant, which is therefore isometric to the unit form. W. Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg 11 (1936).

The second reader gives it the kind standard fact and the check the kind technical step. The check names the published result as follows. Landherr's theorem classifying Hermitian forms over a quadratic extension of number fields by rank, determinant modulo norms and signatures, here for a positive definite diagonal form over an imaginary quadratic field with square determinant. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The statement is word for word the same as Theorem 58, and h is assumed neither Hermitian nor nondegenerate, which costs nothing because the e_i can be found in the span of the v_i.

### 61, `exists_represent`

The theorem is `GlobalTheory.HermGlobal.exists_represent` in the module `Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds`. Its proof rests on 223 declarations, and the five theorems use it.

Let E/F be an extension of number fields with an F-automorphism σ of E such that σ∘σ is the identity and the elements fixed by σ are exactly the elements of F, and let θ ∈ E be nonzero with σ(θ) = −θ, which forces σ ≠ id and makes E/F quadratic. Let r ≥ 2, let g_1, …, g_r be nonzero elements of E fixed by σ and let b be a nonzero element of E fixed by σ, so that all of them lie in F. Assume that for every ring homomorphism τ from E to ℂ with τ∘σ equal to complex conjugation after τ there is an index i such that Re τ(g_i) > 0 holds exactly when Re τ(b) > 0, which says that b has the sign of some g_i at every real place of F that becomes complex in E. Then some z ∈ E^r satisfies Σ_i g_i z_i σ(z_i) = b, so the diagonal Hermitian form ⟨g_1, …, g_r⟩ represents b.

```
σ² = id, E^σ = F, θ ≠ 0, σθ = −θ, r ≥ 2, g_i, b ∈ F^×, (∀ τ ∈ Hom(E, ℂ) with τ∘σ = conj∘τ ∃ i with (Re τ(g_i) > 0 ⇔ Re τ(b) > 0)) ⇒ ∃ z ∈ E^r with Σ_{i=1}^r g_i z_i σ(z_i) = b
```

The first reader gives it the kind standard fact and names the published result as follows. Local–global principle for representations by Hermitian forms over a quadratic extension of number fields, a consequence of Landherr's theorem or of the Hasse–Minkowski theorem for the trace form, for a diagonal form of rank at least 2, where only the real places of F that ramify in E impose a condition. W. Scharlau, Quadratic and Hermitian Forms, Springer, 1985, Chapter 10.

The second reader gives it the kind named theorem and the check the kind standard fact. The check names the published result as follows. The representation criterion for Hermitian forms over a quadratic extension of number fields, a corollary of Landherr's Hasse principle (or of the Hasse–Minkowski theorem applied to the trace form), by which a Hermitian form of rank at least 2 represents a nonzero element of the base field exactly when that element has the sign of some diagonal coefficient at every real place of F that becomes complex in E. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The Lean text lists no condition at the finite places and at the other infinite places because a Hermitian form of rank at least 2 represents every nonzero element there, which is why the hypothesis r ≥ 2 appears, and the dropped converse is elementary.

### 62, `adicCompletion_isDomain_and_isIntegrallyClosed`

The theorem is `GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed` in the module `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosedStatement`. Its proof rests on 220 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed`.

For every commutative ring A that is a local integral domain, integrally closed, of characteristic zero and essentially of finite type over ℤ, the completion of A with respect to its maximal ideal is again an integral domain and is integrally closed.

```
A local normal domain, char A = 0, A essentially of finite type over ℤ ⇒ Â = lim A/𝔪^n is a normal domain
```

The first reader gives it the kind named theorem and names the published result as follows. Analytic normality of excellent normal local rings, which is Zariski's theorem on analytic normality in the generality of Nagata and Grothendieck, applied to rings essentially of finite type over ℤ, which are excellent. A. Grothendieck, Éléments de géométrie algébrique IV, seconde partie, Publ. Math. IHÉS 24, 1965, (7.8.3).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Zariski's theorem on analytic normality in the form of Nagata and Grothendieck (EGA IV 7.8.3), by which the completion of an excellent normal local domain is a normal domain, applied to local rings essentially of finite type over ℤ, which are excellent. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The hypothesis of characteristic zero is not needed for the published theorem and only narrows the class of rings, while mixed-characteristic rings such as ℤ localized at a prime stay included.

### 63, `wp_isAlgebraic`

The theorem is `PI.GalTorsConj.W.wp_isAlgebraic` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite`. Its proof rests on 218 declarations, and the five theorems use it.

Let L be the lattice in ℂ of a period pair, with Weierstrass invariants g₂ and g₃ and Weierstrass function ℘_L, and let M be a subfield of ℂ that contains g₂ and g₃. If n > 0 and t ∈ ℂ satisfy n·t ∈ L and t ∉ L, then ℘_L(t) is algebraic over M.

```
g₂(L), g₃(L) ∈ M ⊆ ℂ, n ≥ 1, nt ∈ L, t ∉ L ⇒ ℘_L(t) is algebraic over M
```

The first reader gives it the kind standard fact and names the published result as follows. Algebraicity of the division values of the Weierstrass ℘-function, since ℘ at a nonzero n-torsion point is a root of the n-th division polynomial, whose coefficients lie in ℤ[g₂, g₃]. J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer, 2009, Exercise 3.7.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The algebraicity of the division values of the Weierstrass ℘-function over ℚ(g₂, g₃), which follows from the division polynomials. For the relation to that result the check has same, the first reader same and the second reader same.

### 64, `jacobiTheta₂_eq_zero_iff`

The theorem is `GlobalTheory.ThetaNullNormSquares.jacobiTheta₂_eq_zero_iff` in the module `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeanSquareNormalizedThetaTwoTorsion`. Its proof rests on 211 declarations, and the five theorems use it.

Let τ lie in the upper half-plane, let a ≠ 0 and let Λ be the additive subgroup a(ℤτ + ℤ) of ℂ. Then for every w ∈ ℂ the Jacobi theta function θ(z, τ) = Σ_{n∈ℤ} exp(2πinz + πin²τ) vanishes at z = w + (τ+1)/2 if and only if a·w ∈ Λ, which holds exactly when w ∈ ℤτ + ℤ.

```
Λ = a(ℤτ + ℤ), a ≠ 0 ⇒ ∀ w ∈ ℂ, θ(w + (τ+1)/2, τ) = 0 ⇔ aw ∈ Λ
```

The first reader gives it the kind standard fact and names the published result as follows. Zeros of the Jacobi theta function, which vanishes exactly at the points (1+τ)/2 + ℤ + ℤτ. D. Mumford, Tata Lectures on Theta I, Birkhäuser, 1983, Chapter I.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The location of the zeros of the Jacobi theta function, which vanishes exactly at the points (τ + 1)/2 + ℤ + ℤτ. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The parameters a and Λ add nothing to the content, since a·w ∈ Λ holds exactly when w ∈ ℤτ + ℤ.

### 65, `free_of_etale_on_punctured_spectrum`

The theorem is `GlobalTheory.T.free_of_etale_on_punctured_spectrum` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePuncturedStatement`. Its proof rests on 209 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.PurityStep.free_of_etale_punctured`.

Let R be a Noetherian local domain whose maximal ideal is generated by as many elements as the Krull dimension of R, so that R is a regular local ring, and assume dim R ≥ 3. Let A be an integrally closed domain that is a finite R-algebra on which R acts faithfully. If R_𝔭 ⊗_R A is étale over R_𝔭 for every prime 𝔭 of R other than the maximal ideal, then A is a free R-module.

```
R regular local, dim R ≥ 3, R ↪ A finite, A normal domain, R_𝔭 → A_𝔭 étale for all 𝔭 ≠ 𝔪 ⇒ A ≅ R^n as R-modules
```

The first reader gives it the kind named theorem and names the published result as follows. Zariski–Nagata purity of the branch locus, which makes A étale and hence free over R. M. Nagata, On the purity of branch loci in regular local rings, Illinois J. Math. 3, 1959.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The Zariski–Nagata purity of the branch locus for a finite normal extension of a regular local ring, in dimension at least 3 and with étaleness assumed on the whole punctured spectrum. For the relation to that result the check has special case, the first reader weaker and the second reader weaker.

The check adds this. Under the hypotheses the conclusion that A is free is equivalent to étaleness, because the discriminant of a free A that is not a unit would lie in a height-one prime other than the maximal ideal, so the Lean text is the hard case of purity in dimension at least 3 and not a weakening of its conclusion.

### 66, `c_one_h2_units_subsingleton`

The theorem is `GlobalTheory.c_one_h2_units_subsingleton` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.COneH2UnitsSubsingleton`. Its proof rests on 195 declarations, and the five theorems use it.

Let L/K be a finite Galois extension of fields. Assume that K has property C₁, which means that every homogeneous polynomial over K of degree d in n variables with 0 < d < n has a nonzero zero in K^n. Then the second cohomology group of Aut_K(L) with coefficients in the multiplicative group L^× has at most one element.

```
L/K finite Galois, K is C₁ ⇒ H²(Gal(L/K), L^×) = 0
```

The first reader gives it the kind standard fact and names the published result as follows. Vanishing of the Brauer group of a quasi-algebraically closed (C₁) field. J.-P. Serre, Local Fields, Springer, 1979, Chapter X, §7.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The vanishing of the Brauer group of a quasi-algebraically closed (C₁) field, stated for each relative Brauer group H²(Gal(L/K), L^×). For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The Lean hypothesis is the usual definition of a C₁ field, which finite fields meet by the Chevalley–Warning theorem and function fields of curves over algebraically closed fields meet by Tsen's theorem.

### 67, `exists_place_pow_and_not_pow'`

The theorem is `GlobalTheory.T.exists_place_pow_and_not_pow'` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlacePowAndNotPowStatement`. Its proof rests on 189 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CNorm.exists_place_pow_and_not_pow`.

Let p be a prime and F a totally complex number field that contains a primitive p-th root of unity. Let δ and u be nonzero elements of F such that δ is not a p-th power in F and u differs from δ^k r^p for every k ∈ ℕ and r ∈ F, so that δ and u are independent in F^×/F^{×p}, and let S₀ be a finite set of finite places of F. Then some finite place v outside S₀ has δ a p-th power in the completion F_v and u not a p-th power in F_v.

```
ζ_p ∈ F, δ ∉ F^p, u ∉ δ^ℕ·F^p, S₀ finite ⇒ ∃ v ∉ S₀ with δ ∈ (F_v)^p and u ∉ (F_v)^p
```

The first reader gives it the kind technical step and names the published result as follows. Consequence of the Chebotarev density theorem for the Kummer extension F(δ^{1/p}, u^{1/p})/F, whose Galois group is (ℤ/p)². N. Tschebotareff, Die Bestimmung der Dichtigkeit einer Menge von Primzahlen, welche zu einer gegebenen Substitutionsklasse gehören, Math. Ann. 95, 1926.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A consequence of the Chebotarev density theorem for the Kummer extension F(δ^{1/p}, u^{1/p})/F, whose Galois group is (ℤ/pℤ)². For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypothesis that F is totally complex follows from ζ ∈ F when p is odd and only narrows the fields when p = 2.

### 68, `exists_le_forall_torsion_mem`

The theorem is `GroundTheory.Global.Elliptic.exists_le_forall_torsion_mem` in the module `GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFields`. Its proof rests on 189 declarations, and the five theorems use it.

Let K be a field with a ring map to ℂ, let L₀ be an intermediate field between K and ℂ that is finite over K, and let A be an elliptic curve in Weierstrass form over L₀. For every m ≠ 0 there is an intermediate field M, finite over K and containing L₀, such that both coordinates of every affine point of A over ℂ that is killed by m lie in M.

```
L₀/K finite, A/L₀ elliptic, m ≠ 0 ⇒ ∃ M ⊇ L₀ with M/K finite and x(P), y(P) ∈ M for every affine P ∈ A(ℂ) with mP = O
```

The first reader gives it the kind standard fact and names the published result as follows. Finiteness of the m-division field L₀(A[m]) over L₀. J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer, 2009, Chapter VIII, §1.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The finiteness of the m-division field L₀(A[m]) of an elliptic curve over its field of definition. For the relation to that result the check has same, the first reader same and the second reader same.

### 69, `exists_odd_order_at_even_elsewhere`

The theorem is `GlobalTheory.QNorm.exists_odd_order_at_even_elsewhere` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddOrderAtEvenElsewhere`. Its proof rests on 188 declarations, and the five theorems use it.

Let F be a number field, δ ∈ F^× a non-square and σ₀ a real embedding of F. Assume a condition H, which says that every nonzero t ∈ F whose valuation is even at every finite place where δ is not a local square, and which is positive under every real embedding other than σ₀, is also positive under σ₀. Then for every finite place v₀ there is a nonzero t ∈ F with odd valuation at v₀ and even valuation at every other finite place where δ is not a local square.

```
δ ∉ F^{×2}, σ₀ real, [∀ t ≠ 0, ((∀ v finite, δ ∈ (F_v)² ∨ 2 | v(t)) ∧ (∀ real σ ≠ σ₀, σ(t) > 0)) ⇒ σ₀(t) > 0] ⇒ ∀ v₀ ∃ t ≠ 0 with v₀(t) odd and (∀ v ≠ v₀, δ ∈ (F_v)² ∨ 2 | v(t))
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a parity lemma for valuations at the non-split places of the quadratic extension F(√δ)/F, whose hypothesis H acts as a sign condition of Hilbert reciprocity type.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a lemma that finds an element with odd valuation at one given place and even valuation at the other places where δ is not a local square, under a sign hypothesis of Hilbert reciprocity type. For the relation to that result the check has none, the first reader none and the second reader weaker.

The check adds this. The statement is true because its hypothesis keeps F(√δ) out of the Hilbert class field of F, and the Chebotarev density theorem then puts primes that split in F(√δ) into every ideal class.

On emptiness the check wrote this. The hypothesis on t fails at t = −1 when F has exactly one real embedding and at any unit that is negative at σ₀ and positive at the other real embeddings, and a totally complex F has no σ₀, so the theorem is empty for such fields, although F = ℚ(√3) with δ = −1 meets the hypothesis by Hilbert reciprocity.

### 70, `isAlgebraic_of_nsmul_eq_zero`

The theorem is `GroundTheory.Global.Elliptic.isAlgebraic_of_nsmul_eq_zero` in the module `GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremFields`. Its proof rests on 188 declarations, and the five theorems use it.

Let F be a field with a ring map to ℂ and A an elliptic curve in Weierstrass form over F. If m ≠ 0 and (x, y) is a nonsingular affine point of A over ℂ whose m-th multiple is the identity in the group of points, then x and y are algebraic over F.

```
A/F elliptic, F → ℂ, m ≠ 0, P = (x, y) ∈ A(ℂ), mP = O ⇒ x and y are algebraic over F
```

The first reader gives it the kind standard fact and names the published result as follows. Torsion points of an elliptic curve have algebraic coordinates, A[m] ⊆ A(F̄), as the division polynomials show. J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer, 2009, Exercise 3.7.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The algebraicity of the coordinates of the torsion points of an elliptic curve over its field of definition, through the division polynomials. For the relation to that result the check has same, the first reader same and the second reader same.

### 71, `exists_prime_absNorm_eq_of_irreducible_cyclotomic'`

The theorem is `GlobalTheory.T.exists_prime_absNorm_eq_of_irreducible_cyclotomic'` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement`. Its proof rests on 180 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic`.

Let K be a number field and m a prime such that the cyclotomic polynomial Φ_m is irreducible over K. Then for every unit τ of ℤ/mℤ and every finite set S of nonzero primes of 𝓞_K there is a nonzero prime P outside S whose absolute norm N(P) is a rational prime congruent to τ modulo m.

```
Φ_m irreducible over K, τ ∈ (ℤ/m)^×, S finite ⇒ ∃ P ∉ S with N(P) prime and N(P) ≡ τ (mod m)
```

The first reader gives it the kind standard fact and names the published result as follows. Chebotarev density theorem for the cyclotomic extension K(ζ_m)/K, whose Galois group is all of (ℤ/m)^× because Φ_m is irreducible, combined with the fact that primes of degree one have density one. J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VII, Theorem 13.4.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Dirichlet's theorem on primes in arithmetic progressions for primes of degree one in a number field, which is the Chebotarev density theorem for K(ζ_m)/K combined with the density one of primes of degree one. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. For K = ℚ the statement is Dirichlet's theorem on primes in arithmetic progressions to a prime modulus.

### 72, `exists_place_not_pow_adicCompletion`

The theorem is `GlobalTheory.T.exists_place_not_pow_adicCompletion` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotPowAdicCompletionStatement`. Its proof rests on 179 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CNorm.exists_not_mem_not_pow_completion`.

Let p be a prime and F a totally complex number field that contains a primitive p-th root of unity. If u ∈ F is nonzero and not a p-th power in F, then for every finite set S₀ of finite places of F there is a finite place v outside S₀ such that u is not a p-th power in the completion F_v.

```
ζ_p ∈ F, u ∈ F^× ∖ F^{×p}, S₀ finite ⇒ ∃ v ∉ S₀ with u ∉ (F_v)^p
```

The first reader gives it the kind standard fact and names the published result as follows. Local–global principle for p-th powers, the prime-exponent case of the Grunwald–Wang theorem, which says that an element that is a p-th power at almost all places is a p-th power in F. E. Artin and J. Tate, Class Field Theory, Benjamin, 1968, Chapter X.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The local–global principle for p-th powers, by which an element that is a p-th power in almost all completions is a p-th power, here in the case where F contains the p-th roots of unity, which is the prime-exponent case of the Grunwald–Wang theorem. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The hypothesis that F is totally complex follows from ζ ∈ F when p is odd.

### 73, `finite_torsionBy_natCast`

The theorem is `GroundTheory.Arith.Abelian.finite_torsionBy_natCast` in the module `GroundTheory.ArithmeticGeometry.AbelianVarieties.Supersingular`. Its proof rests on 177 declarations, and the five theorems use it.

Let F be an algebraically closed field and E an elliptic curve in Weierstrass form over F. For every natural number n ≠ 0 the subgroup of points P ∈ E(F) with nP = O is finite. The prime p and the assumption that F has characteristic p appear in the variable lines but are omitted from this theorem, so the field may have any characteristic.

```
F algebraically closed, E/F elliptic, n ≥ 1 ⇒ E(F)[n] is finite
```

The first reader gives it the kind standard fact and names the published result as follows. Structure of the n-torsion of an elliptic curve, E[n] ≅ (ℤ/n)² when the characteristic does not divide n and E[p^e] ≅ 0 or ℤ/p^e in characteristic p. J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer, 2009, Corollary III.6.4.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The finiteness of the n-torsion subgroup E[n] of an elliptic curve, which has at most n² elements and is isomorphic to (ℤ/nℤ)² when the characteristic does not divide n. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

### 74, `elliptic_points_stabilizer`

The theorem is `GlobalTheory.T.elliptic_points_stabilizer` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizerStatement`. Its proof rests on 173 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.EllipticZero.elliptic_of_zero`.

For every τ₀ in the upper half-plane two implications hold. If the Eisenstein series E₆ vanishes at τ₀, then some u = (a b, c d) ∈ SL(2, ℤ) fixes τ₀ and its automorphy factor cτ₀ + d is a primitive fourth root of unity. If E₄ vanishes at τ₀, then some u ∈ SL(2, ℤ) fixes τ₀ and cτ₀ + d is a primitive sixth root of unity.

```
∀ τ₀ ∈ ℍ, (E₆(τ₀) = 0 ⇒ ∃ u ∈ SL₂(ℤ), uτ₀ = τ₀ and cτ₀ + d ∈ μ₄ primitive) ∧ (E₄(τ₀) = 0 ⇒ ∃ u ∈ SL₂(ℤ), uτ₀ = τ₀ and cτ₀ + d ∈ μ₆ primitive)
```

The first reader gives it the kind standard fact and names the published result as follows. Zeros of E₄ and E₆ by the valence formula, E₆ vanishing only on the SL₂(ℤ)-orbit of i and E₄ only on the orbit of ρ = e^{2πi/3}, together with the stabilizers of these elliptic points. J.-P. Serre, A Course in Arithmetic, Springer, 1973, Chapter VII, §3.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The location of the zeros of E₄ and E₆, which by the valence formula lie only on the SL(2, ℤ)-orbits of ρ = e^{2πi/3} and of i, together with the stabilizers of these elliptic points. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The conclusion says only that a zero of E₆ has a stabilizer element with automorphy factor of order 4 and a zero of E₄ one with automorphy factor of order 6, and it gives neither the converse nor the simplicity of the zeros.

### 75, `isReduced_adicCompletion_tensor_residueField`

The theorem is `GlobalTheory.EtaleCompletionRadical.isReduced_adicCompletion_tensor_residueField` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField`. Its proof rests on 171 declarations, and the five theorems use it.

Let A be a local ring essentially of finite type over ℤ and P a prime ideal of A. Then the formal fibre Â ⊗_A κ(P) is a reduced ring, where Â is the completion of A at its maximal ideal and κ(P) is the residue field of P.

```
A local and essentially of finite type over ℤ, P ∈ Spec A ⇒ Â ⊗_A κ(P) is reduced
```

The first reader gives it the kind standard fact and names the published result as follows. Reducedness of the formal fibres of an excellent local ring, which are even geometrically regular, together with Grothendieck's theorem that rings essentially of finite type over ℤ are excellent. A. Grothendieck, Éléments de géométrie algébrique IV, seconde partie, Publ. Math. IHÉS 24, 1965, (7.8.3).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The reducedness of the formal fibres of an excellent local ring, whose formal fibres are geometrically regular, applied to local rings essentially of finite type over ℤ, which are excellent by Grothendieck (EGA IV 7.8.3). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The Lean text assumes neither that A is a domain nor that A is Noetherian, since essential finite type over ℤ already makes A Noetherian.

### 76, `isOpen_identityComponents_smooth_groupScheme`

The theorem is `GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupSchemeStatement`. Its proof rests on 171 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.IdCompOpen.isOpen_identityComponent`.

Let S be a scheme and G a group scheme over S whose structure morphism π from G to S is smooth. For a point x of G write s = π(x) and e(s) for the image of s under the unit section. Then the set of points x that lie in the connected component of the topological fibre π⁻¹(s) containing e(s), which is the union G⁰ of the identity components of the fibres, is open in G.

```
G → S smooth group scheme ⇒ G⁰ = {x ∈ G | x lies in the connected component of π⁻¹(π(x)) that contains e(π(x))} is open in G
```

The first reader gives it the kind standard fact and names the published result as follows. Openness of the identity component G⁰ of a smooth group scheme. M. Demazure and A. Grothendieck, Schémas en groupes I (SGA 3), Lecture Notes in Math. 151, Springer, 1970, Exposé VI_B, Théorème 3.10.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The openness of the identity component G⁰ of a smooth group scheme (SGA 3, Exposé VI_B, 3.10). For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The fibre in the Lean text is the topological subspace π⁻¹(s) of G, which is homeomorphic to the underlying space of the scheme-theoretic fibre G_s, so the set is the usual G⁰.

### 77, `card_zeros_le_of_growth`

The theorem is `GlobalTheory.TorsionZero.card_zeros_le_of_growth` in the module `Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardZerosOnTorsionLeOfSymmetricVeryAmple`. Its proof rests on 171 declarations, and the five theorems use it.

Let K be algebraically closed and R an ℕ-graded K-algebra that is a domain, with elements x_1, …, x_m of degree N ≥ 1 such that every element of degree Ne times a power of each x_i is a homogeneous polynomial of matching degree in the x_j, and with dim_K R_{Ne} ≤ (Be)^g for all e ≥ 1, where g ≥ 1 is the Krull dimension of the coordinate ring C of the variety X of the x_j in the affine chart x_{i₀} ≠ 0. A set Pt of K-points of R is mapped bijectively onto the points of X by the projective coordinates (x_1(p) : … : x_m(p)). Let s ≠ 0 have degree Nd, let finitely many f_j have degree Na, and assume the common zero set Z of the f_j in Pt is finite. Then at most B^g · g! · d · a^{g−1} points of Z are zeros of s.

```
#{p ∈ Z | s(p) = 0} ≤ B^g · g! · d · a^{g−1}, where Z = V(f_j) ⊆ X is finite, dim X = g, dim R_{Ne} ≤ (Be)^g, s ∈ R_{Nd} ∖ {0} and f_j ∈ R_{Na}
```

The first reader gives it the kind technical step and names the published result as follows. Bézout-type bound for isolated common zeros of sections on a projective variety, namely the refined Bézout inequality combined with the bound deg X ≤ g!·B^g that the Hilbert-function estimate gives. W. Fulton, Intersection Theory, Springer, 1984, Example 8.4.6.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A Bézout-type bound, the refined Bézout inequality (Fulton, Intersection Theory, Example 8.4.6) for a projective variety of dimension g whose degree is at most g!·B^g by the growth of its Hilbert function. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The variety and its points are encoded through a graded domain, a ring C and a type of evaluation maps, and C turns out to be the coordinate ring of the chart x_{i₀} ≠ 0 of the projective variety that the homogeneous relations of the x_j define, because a relation of C homogenized in the variable of index i₀ is a homogeneous relation of the x_j.

### 78, `exists_idele_ne_algebraMap_mul_norm_of_not_isSquare`

The theorem is `GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare` in the module `Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNormStatement`. Its proof rests on 170 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.QNorm.exists_idele_not_mul_norm`.

Let F be a number field and δ ∈ F a non-square. Then there is an idele a of F with a ≠ t·(x² − δy²) for every t ∈ F and all adeles x and y of F. Since x² − δy² is the norm from the adeles of E = F(√δ), and an idele of this form forces t ≠ 0 and makes x + y√δ an idele of E, the statement says that F^× · N_{E/F}(𝔸_E^×) is a proper subgroup of 𝔸_F^×.

```
δ ∉ F² ⇒ ∃ a ∈ 𝔸_F^× ∀ t ∈ F ∀ x, y ∈ 𝔸_F, a ≠ t(x² − δy²)
```

The first reader gives it the kind named theorem and names the published result as follows. First fundamental inequality of global class field theory, by which the index of the norm group N_{E/F} C_E in the idele class group C_F is at least the degree of a cyclic extension E/F, here for a quadratic extension where it says that the index exceeds 1. J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI, §4.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. The first fundamental inequality of global class field theory for the quadratic extension F(√δ)/F, by which the norm index in the idele class group is at least 2. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Some textbooks call this inequality the second one, because the naming of the two fundamental inequalities varies.

### 79, `smoothAffineCurve_divisor_unit_decomposition`

The theorem is `GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDivisorUnitDecompositionStatement`. Its proof rests on 170 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.KummerDiv.divisor_step`.

Let k be algebraically closed, let B be a Dedekind domain that is a finitely generated k-algebra, as the coordinate ring of a smooth affine curve is, and let q be a natural number invertible in k. For all nonzero f and b in B and every m ∈ ℕ there are a nonzero g ∈ B comaximal with f, a unit u of B[1/(fg)] and elements n, d, t, n′, d′ of B, with n and d comaximal with f and with n′ and d′ comaximal with g, such that bd = u·n·f^m and u·t^q·d′ = n′ hold in B[1/(fg)]. In terms of divisors, u has order ord(b) − m·ord(f) at each zero of f and an order divisible by q at each zero of g.

```
∀ f, b ∈ B ∖ {0}, ∀ m ∈ ℕ, ∃ g ≠ 0 with (f, g) = B, ∃ u ∈ B_{fg}^×, ∃ n, d, t, n′, d′ ∈ B with (f, n) = (f, d) = (g, n′) = (g, d′) = B, bd = u·n·f^m and u·t^q·d′ = n′ in B_{fg}
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a technical lemma that prescribes the divisor of a unit on a smooth affine curve modulo q-th powers and rests on the divisibility of the Picard group of such a curve over an algebraically closed field.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a lemma that prescribes the divisor of a unit on a smooth affine curve over an algebraically closed field modulo q-th powers and rests on the divisibility of the Picard group of such a curve. For the relation to that result the check has none, the first reader none and the second reader weaker.

The check adds this. The order of u at each prime above g equals −q times the order of t there, so it is a multiple of q that is at most 0.

### 80, `weber_values_congruences_mod_degree_one_prime`

The theorem is `GlobalTheory.T.weber_values_congruences_mod_degree_one_prime` in the module `Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrimeStatement`. Its proof rests on 170 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.WeberCongruenceAnyOrder.weber_congruences`.

Let K ⊆ ℂ be an imaginary quadratic field, let L be a period pair whose lattice is 𝓞_K, let W be a valuation ring of ℂ, and let π ∈ 𝓞_K lie in the maximal ideal 𝔪_W and have ideal norm a prime p ≥ 5. Write Δ = g₂³ − 27g₃², j′ = g₂³/Δ, which equals j(𝓞_K)/1728, and h(t) = g₂g₃℘(t)/Δ for the Weber function. Then j′ ∈ W and j′ ≡ j′^p modulo 𝔪_W, and for every m not divisible by p and every t with mt ∈ L and t ∉ L the value h(t) lies in W and h(πt) ≡ h(t)^p modulo 𝔪_W. If moreover j′ and j′ − 1 are units of W, then h(t) ≡ h(t′) modulo 𝔪_W for two such points t and t′ forces t − t′ ∈ L or t + t′ ∈ L.

```
Δ = g₂³ − 27g₃², j′ = g₂³/Δ, h(t) = g₂g₃℘(t)/Δ ⇒ j′ ∈ W, j′ ≡ j′^p (mod 𝔪_W), and ∀ m with p ∤ m ∀ t ∈ m⁻¹L ∖ L, h(t) ∈ W and h(πt) ≡ h(t)^p (mod 𝔪_W), and if j′, j′ − 1 ∈ W^× then h(t) ≡ h(t′) (mod 𝔪_W) ⇒ t ≡ ±t′ (mod L)
```

The first reader gives it the kind standard fact and names the published result as follows. Congruence relations of Kronecker and Hasse for the singular modulus j(𝓞_K) and for the Weber function at torsion points, used in the proof of the main theorem of complex multiplication, here for a principal prime of degree one. J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic Curves, Springer, 1994, Chapter II.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Hasse's congruences for the singular modulus j(𝓞_K) and for the Weber function at torsion points modulo a principal prime of degree one (the Kronecker congruence relation), together with the injectivity of reduction on prime-to-p torsion up to sign, the steps of Hasse's proof of the main theorem of complex multiplication. For the relation to that result the check has special case, the first reader special case and the second reader weaker.

The check adds this. The statement bundles four claims for the lattice 𝓞_K and a principal prime of degree one, and the last claim needs J and J − 1 to be units, which excludes j ≡ 0 and j ≡ 1728 modulo the prime.

On emptiness the check wrote this. For K = ℚ(i) and K = ℚ(√−3) one of g₃ and g₂ vanishes, so h is identically zero and J equals 1 or 0, which makes the congruences immediate and the premise of the last clause impossible, and the statement has content only for the other imaginary quadratic fields.

### 81, `weber_congruences`

The theorem is `GlobalTheory.WeberCongruence.weber_congruences` in the module `Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantCongruencesImaginaryQuadratic`. Its proof rests on 169 declarations, and the five theorems do not use it.

Let K be a subfield of ℂ that is an imaginary quadratic number field, let L be a lattice in ℂ equal to the ring of integers 𝒪_K, let W be any valuation ring of ℂ, and let π ∈ 𝒪_K generate an ideal of norm a prime p ≥ 5 and lie in the maximal ideal of W. Then J = g₂³/(g₂³ − 27g₃²), which is j(L)/1728, lies in W and satisfies J ≡ J^p modulo the maximal ideal of W. For every odd m not divisible by p and every t with mt ∈ L and t ∉ L, the Weber value h(t) = (g₂g₃/(g₂³ − 27g₃²))·℘(t) lies in W and h(πt) ≡ h(t)^p modulo the maximal ideal. If J and J − 1 are also units of W, then two such m-division points t and t′ with h(t) ≡ h(t′) satisfy t ≡ t′ or t ≡ −t′ modulo L.

```
K ⊂ ℂ imaginary quadratic, Λ = 𝒪_K, π ∈ 𝒪_K ∩ 𝔪_W, N(π) = p ≥ 5 prime, Δ = g₂³ − 27g₃², J = g₂³/Δ ⇒ J ∈ W, J ≡ J^p mod 𝔪_W, and for all odd m with p ∤ m and all t ∈ m⁻¹Λ ∖ Λ, h(t) = (g₂g₃/Δ)℘(t) ∈ W, h(πt) ≡ h(t)^p mod 𝔪_W, and (J, J − 1 ∉ 𝔪_W ∧ h(t) ≡ h(t′) mod 𝔪_W ⇒ t ≡ ±t′ mod Λ)
```

The first reader gives it the kind technical step and names the published result as follows. Hasse's congruences for the j-invariant and the Weber function of a lattice with complex multiplication by 𝒪_K at a principal prime of degree one, together with the injectivity of the reduced Weber function on m-division points up to sign, which are the inputs of the Weber–Hasse proof that these values generate class fields of K. Goro Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, 1971, Chapter 5.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Hasse's congruence for the Weber function and the Kronecker congruence for the j-invariant of the lattice 𝒪_K at a principal prime of degree one, together with the injectivity up to sign of the reduced Weber function on division points of order prime to p, as used in the proof of the main theorem of complex multiplication. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The valuation ring W ranges over all valuation subrings of ℂ, and the hypothesis that π lies in its maximal ideal forces W to lie over the prime (π), while the statement covers only the lattice 𝒪_K itself and odd orders m.

On emptiness the check wrote this. The hypotheses can be met, for example by K = ℚ(i), π = 2 + i and p = 5, but for K = ℚ(i) and K = ℚ(√−3) the function h vanishes identically and the premise of the last clause fails, so the clauses on h have content only for the other imaginary quadratic fields.

### 82, `j_invariant_equal_sl2_orbit`

The theorem is `GlobalTheory.T.j_invariant_equal_sl2_orbit` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement`. Its proof rests on 166 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.JOrbit.exists_smul_of_E₄_E₆`.

For all points τ and σ of the upper half-plane, if E₄(τ)³E₆(σ)² = E₆(τ)²E₄(σ)³, where E₄ and E₆ are the Eisenstein series of weights 4 and 6, then some matrix γ in SL₂(ℤ) satisfies τ = γσ under the Möbius action. E₄³ and E₆² never vanish together on the upper half-plane, so the hypothesis is equivalent to j(τ) = j(σ), and it does not change when E₄ and E₆ are rescaled.

```
∀ τ, σ ∈ ℍ, E₄(τ)³E₆(σ)² = E₆(τ)²E₄(σ)³ ⇒ ∃ γ ∈ SL₂(ℤ), τ = γ·σ
```

The first reader gives it the kind standard fact and names the published result as follows. Injectivity of the modular j-function on SL₂(ℤ)∖ℍ, one half of the theorem that j induces a bijection from SL₂(ℤ)∖ℍ onto ℂ. Jean-Pierre Serre, A Course in Arithmetic, 1973, Chapter VII, Proposition 5.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Injectivity of the modular j-invariant on SL₂(ℤ)∖ℍ, one half of the theorem that j induces a bijection from SL₂(ℤ)∖ℍ onto ℂ. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypothesis is the equation j(τ) = j(σ) with the denominators cleared, which is equivalent to it because E₄³ − E₆² never vanishes on ℍ, and it does not depend on the normalisation of E₄ and E₆ because both sides scale by the same factor.

### 83, `exists_strictHenselisation`

The theorem is `GlobalTheory.exists_strictHenselisation` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation`. Its proof rests on 165 declarations, and the five theorems use it.

For every local ring R with residue field k and every separable closure Ω of k, there is a henselian local R-algebra S with local structure map whose residue field is separably closed and isomorphic to Ω as a k-algebra. Moreover S is flat over R, and the maximal ideal of R generates the maximal ideal of S. Finally S is the union of a nonempty directed family of R-subalgebras, each isomorphic as an R-algebra to the localization of some étale R-algebra at a prime ideal.

```
∀ (R, 𝔪, k) local, ∀ Ω = k^sep, ∃ S strictly henselian local, R → S local and flat, 𝔪S = 𝔪_S, κ(S) ≅_k Ω, S = ⋃_{i ∈ I} S_i with I directed and S_i ≅_R (A_i)_{𝔮_i}, A_i étale over R
```

The first reader gives it the kind standard fact and names the published result as follows. Existence of the strict henselization R^sh of a local ring, together with its standard properties. Michel Raynaud, Anneaux locaux henséliens, Lecture Notes in Mathematics 169, 1970.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Existence of the strict henselization of a local ring with its standard properties (EGA IV 18.8, Stacks Project). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The universal property of the strict henselization is absent, and the primes q of the étale algebras need not lie over the maximal ideal of R, so the statement asserts the existence of a ring with these properties and not that S is unique.

### 84, `nsAbs`

The theorem is `UpperTheory.Kd.K4.nsAbs` in the module `Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.RelOfComap`. Its proof rests on 165 declarations, and the five theorems use it.

Let k be an algebraically closed field of characteristic zero, K a finite extension of the rational function field k(X), and K′ a finite Galois extension of K, with k[X] mapping compatibly into both. Let m > 0 and let f ∈ K be nonzero such that at every valuation ring B of K containing k[X], f equals a unit of B times an m-th power. Then some nonzero f′ ∈ K′ has norm N_{K′/K}(f′) = f and has the same property at every valuation ring of K′ containing k[X]. In terms of divisors on the affine curves over the X-line, a function whose affine divisor is divisible by m is the norm of a function on the Galois cover whose affine divisor is again divisible by m.

```
f ∈ K^×, div_C(f) ∈ m·Div(C) ⇒ ∃ f′ ∈ K′^×, N_{K′/K}(f′) = f and div_{C′}(f′) ∈ m·Div(C′), where C and C′ are the normalizations of the affine X-line in K and K′
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a norm-lifting statement along a finite Galois cover of curves for functions whose divisor on the affine part is divisible by m, which refines the surjectivity of the norm that Tsen's theorem gives.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a norm-lifting statement along a finite Galois extension of function fields of curves for functions whose divisor on the affine part is divisible by m. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The valuation rings of K that contain k[X] are K itself and the local rings at the closed points of the normalisation of the X-line in K, so the hypothesis says that the divisor of f on that affine curve is divisible by m.

### 85, `exists_place_isSquare_and_not_isSquare`

The theorem is `GlobalTheory.QNorm.exists_place_isSquare_and_not_isSquare` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceIsSquareAndNotIsSquare`. Its proof rests on 162 declarations, and the five theorems use it.

Let F be a number field, let δ and u be nonzero elements such that none of δ, u and uδ is a square in F, and let S₀ be a finite set of nonzero primes of the ring of integers. Then some nonzero prime v outside S₀ makes δ a square in the completion F_v while u is not a square in F_v.

```
δ, u, uδ ∉ F^{×2}, S₀ finite ⇒ ∃ finite place v ∉ S₀ with δ ∈ F_v^{×2} and u ∉ F_v^{×2}
```

The first reader gives it the kind standard fact and names the published result as follows. Consequence of the Chebotarev density theorem for the biquadratic extension F(√δ, √u), whose Galois group is (ℤ/2)², applied to the element that fixes √δ and moves √u. Jürgen Neukirch, Algebraic Number Theory, 1999, Chapter VII, Theorem 13.4.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. A corollary of the Chebotarev density theorem for the biquadratic extension F(√δ, √u)/F, applied to the Frobenius class that fixes √δ and moves √u. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypothesis that uδ is not a square makes F(√δ, √u) an extension of degree 4 with Galois group (ℤ/2)², which is what the Chebotarev argument needs.

On emptiness the check wrote this. The hypotheses δ ≠ 0 and u ≠ 0 are redundant because 0 is a square, and the remaining hypotheses can be met, for example by F = ℚ, δ = 2 and u = 3.

### 86, `classGroup_dedekind_algClosed_divisible`

The theorem is `GlobalTheory.T.classGroup_dedekind_algClosed_divisible` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisibleStatement`. Its proof rests on 162 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.PicDiv.classGroup_divisible`.

Let k be an algebraically closed field and B a Dedekind domain that is a finitely generated k-algebra, which makes B the coordinate ring of a smooth affine curve over k or k itself. For every natural number q whose image in k is nonzero, every element of the ideal class group of B is a q-th power.

```
k = k̄, B Dedekind of finite type over k, q ∈ ℕ, q ≠ 0 in k ⇒ ∀ c ∈ Cl(B), ∃ d ∈ Cl(B), d^q = c
```

The first reader gives it the kind standard fact and names the published result as follows. Divisibility of the Picard group of a smooth affine curve over an algebraically closed field, which is a quotient of the divisible group of points of the Jacobian of the projective completion. David Mumford, Abelian Varieties, 1970.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Divisibility of the Picard group of a smooth affine curve over an algebraically closed field, which is a quotient of the divisible group of points of the Jacobian of its smooth projective model. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The published fact holds for every q ≥ 1, multiples of the characteristic included, while the Lean statement asks for q nonzero in k, and the trivial case B = k is allowed.

### 87, `exists_ne_zero_of_scaled`

The theorem is `GlobalTheory.Dict.ThetaHalf.exists_ne_zero_of_scaled` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLattice`. Its proof rests on 160 declarations, and the five theorems use it.

Let V be a finite-dimensional ℚ-vector space with a bilinear form B, let p be an injective additive map from V to ℂ^g, and let L be a finitely generated subgroup of V whose image spans ℂ^g over ℝ and which equals its own dual for B/M, where M ≥ 2. Let H(z, w) = zᵀH w̄ be a positive definite Hermitian form with Im H(p(u), p(v)) = B(u, v), let c be a function of modulus one on V, and let f be a nonzero entire function on ℂ^g with f(z + p(v)) = c(v)·exp(πH(z, p(v)) + (π/2)H(p(v), p(v)))·f(z) for all v ∈ L. Then f(p(v)/M) ≠ 0 for some v ∈ L. Geometrically, f is a nonzero theta function for a polarization of type (M, …, M) on the abelian variety ℂ^g/p(L), and the claim is that it does not vanish at every M-torsion point.

```
L = {x ∈ V | B(x, L) ⊂ Mℤ}, Im H(pu, pv) = B(u, v), f ≢ 0 entire, f(z + pv) = c(v)·e^{πH(z, pv) + (π/2)H(pv, pv)}·f(z) ∀ v ∈ L ⇒ ∃ v ∈ L, f(M⁻¹p(v)) ≠ 0
```

The first reader gives it the kind technical step and names the published result as follows. Non-vanishing of a nonzero theta function of level M at some M-division point, which follows from Mumford's theorem that the theta group acts irreducibly on the sections of a line bundle, together with the base-point freeness of the M-th power of a principal polarization for M ≥ 2. David Mumford, On the equations defining abelian varieties I, Inventiones Mathematicae 1, 1966.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A corollary of Mumford's theorem that the theta group acts irreducibly on the sections of an ample line bundle, combined with the base-point freeness of line bundles of type (M, …, M) for M ≥ 2, by which a nonzero theta function of this type does not vanish at every M-torsion point. For the relation to that result the check has weaker, the first reader weaker and the second reader same.

The check adds this. The variable line about a CM field E and a number r does not enter the statement, and no source I know states the claim in this form, so the relation rests on the deduction from the theta-group theorem.

On emptiness the check wrote this. None found, because the hypotheses force p(L) to be a lattice of rank 2g with a polarization of type (M, …, M), and a nonzero f exists whenever c restricted to L is a semicharacter for B.

### 88, `pic_divisible_dedekind_finiteType_algClosed`

The theorem is `GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosedStatement`. Its proof rests on 160 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.PicDiv.pic_divisible`.

Let k be an algebraically closed field, B a Dedekind domain that is a finitely generated k-algebra, and q a natural number that is invertible in k. Then every element of the Picard group of B, the group of isomorphism classes of invertible B-modules, is a q-th power. For a Dedekind domain the Picard group is the ideal class group, so this is the claim of dossier 86 in another notation.

```
k = k̄, B Dedekind of finite type over k, q ∈ k^× ⇒ ∀ c ∈ Pic(B), ∃ d ∈ Pic(B), d^q = c
```

The first reader gives it the kind standard fact and names the published result as follows. Divisibility of the Picard group of a smooth affine curve over an algebraically closed field, which is a quotient of the divisible group of points of the Jacobian of the projective completion. David Mumford, Abelian Varieties, 1970.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Divisibility of the Picard group of a smooth affine curve over an algebraically closed field, which is a quotient of the divisible group of points of the Jacobian of its smooth projective model. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Statement 88 is statement 86 with the group of invertible modules in place of the ideal class group, which are isomorphic for a Dedekind domain, and with q a unit in k, which in a field means q nonzero.

### 89, `thetaFunction_ne_zero_at_divisionPoint_selfDual`

The theorem is `GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionNeZeroAtDivisionPointSelfDualStatement`. Its proof rests on 159 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual`.

Let V be a finite-dimensional ℚ-vector space with a bilinear form B, let p be an injective additive map from V to ℂ^g, and let L be a finitely generated subgroup of V whose image spans ℂ^g over ℝ and which equals its own dual for B. Let H(z, w) = zᵀH w̄ be a positive definite Hermitian form with Im H(p(u), p(v)) = B(u, v), let c be a function of modulus one on V, let N ≥ 2, and let f be a nonzero entire function with f(z + p(v)) = c(v)·exp(N(πH(z, p(v)) + (π/2)H(p(v), p(v))))·f(z) for all v ∈ L. Then f(p(v)/N) ≠ 0 for some v ∈ L. Geometrically, f is a nonzero section of a line bundle algebraically equivalent to the N-th power of a principal polarization on ℂ^g/p(L), and the claim is that it does not vanish at every N-torsion point.

```
L = {x ∈ V | B(x, L) ⊂ ℤ}, Im H(pu, pv) = B(u, v), f ≢ 0 entire, f(z + pv) = c(v)·e^{N(πH(z, pv) + (π/2)H(pv, pv))}·f(z) ∀ v ∈ L ⇒ ∃ v ∈ L, f(N⁻¹p(v)) ≠ 0
```

The first reader gives it the kind technical step and names the published result as follows. Non-vanishing of a nonzero theta function of level N at some N-division point, which follows from Mumford's theorem that the theta group acts irreducibly on the sections of a line bundle, together with the base-point freeness of the N-th power of a principal polarization for N ≥ 2. David Mumford, On the equations defining abelian varieties I, Inventiones Mathematicae 1, 1966.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A corollary of Mumford's theorem that the theta group acts irreducibly on the sections of an ample line bundle, combined with the base-point freeness of line bundles of type (N, …, N) for N ≥ 2, by which a nonzero theta function of this type does not vanish at every N-torsion point. For the relation to that result the check has weaker, the first reader weaker and the second reader same.

The check adds this. Here the factor c(v) stands outside the N-th power while the exponent is multiplied by N, so f is a theta function for the Hermitian form N·H, which has type (N, …, N).

On emptiness the check wrote this. None found, because L is unimodular for B, p(L) is then a lattice, and a nonzero f exists whenever c restricted to L is a semicharacter for N·B.

### 90, `exists_place_not_isSquare_adicCompletion`

The theorem is `GlobalTheory.T.exists_place_not_isSquare_adicCompletion` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletionStatement`. Its proof rests on 156 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.QNorm.exists_not_mem_not_isSquare_completion`.

Let F be a number field, u a nonzero element that is not a square in F, and S₀ a finite set of nonzero primes of the ring of integers. Then some nonzero prime v outside S₀ has u not a square in the completion F_v.

```
u ∈ F^× ∖ F^{×2}, S₀ finite ⇒ ∃ finite place v ∉ S₀ with u ∉ F_v^{×2}
```

The first reader gives it the kind standard fact and names the published result as follows. The case n = 2 of the Grunwald–Wang theorem in contrapositive form, which says that an element that is a square in all but finitely many completions is a square. Emil Artin and John Tate, Class Field Theory, 1968, Chapter X.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The case n = 2 of the Grunwald–Wang theorem on local powers in contrapositive form, which says that an element of a number field that is a square in all but finitely many completions is a square. For the relation to that result the check has special case, the first reader special case and the second reader same.

The check adds this. Because S₀ is an arbitrary finite set, the conclusion gives infinitely many finite places at which u is not a square.

On emptiness the check wrote this. The hypothesis u ≠ 0 is redundant because 0 is a square, and the hypotheses can be met, for example by F = ℚ and u = 2.

### 91, `exists_ne_zero_of_principal`

The theorem is `GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_principal` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionNeZeroAtDivisionPointSelfDual`. Its proof rests on 156 declarations, and the five theorems use it.

Let Λ be a discrete subgroup of ℂ^g that spans ℂ^g over ℝ, H(z, w) = zᵀH w̄ a positive definite Hermitian form, χ a function of modulus one on Λ, and E an integer-valued bilinear form on Λ with E(l, m) = Im H(l, m) that induces a bijection from Λ onto Hom(Λ, ℤ). Let n ≥ 2 and let f be a nonzero entire function with f(z + l) = (χ(l)·exp(πH(z, l) + (π/2)H(l, l)))^n·f(z) for all l ∈ Λ. Then f(l/n) ≠ 0 for some l ∈ Λ. Geometrically, f is a nonzero section of the n-th power of a principal polarization on the torus ℂ^g/Λ, and the claim is that it does not vanish at every n-torsion point.

```
Λ ⊂ ℂ^g lattice, Im H|_Λ unimodular, f ≢ 0 entire, f(z + l) = (χ(l)·e^{πH(z, l) + (π/2)H(l, l)})^n·f(z) ∀ l ∈ Λ ⇒ ∃ l ∈ Λ, f(l/n) ≠ 0
```

The first reader gives it the kind technical step and names the published result as follows. Non-vanishing of a nonzero section of the n-th power of a principal polarization at some n-torsion point, which follows from Mumford's theorem that the theta group acts irreducibly on the sections of a line bundle, together with the base-point freeness of that power for n ≥ 2. David Mumford, On the equations defining abelian varieties I, Inventiones Mathematicae 1, 1966.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A corollary of Mumford's theorem that the theta group acts irreducibly on the sections of an ample line bundle, combined with the base-point freeness of the n-th power of a principal polarization for n ≥ 2, by which a nonzero section of that power does not vanish at every n-torsion point. For the relation to that result the check has weaker, the first reader weaker and the second reader same.

The check adds this. Statements 87, 89 and 91 make the same claim in three presentations, with the lattice given through V and p in the first two and directly as a discrete subgroup of ℂ^g in the third.

On emptiness the check wrote this. None found, because a nonzero section of the n-th power of a principal polarization exists, for example the n-th power of a Riemann theta function with χ a semicharacter.

### 92, `exists_field`

The theorem is `GlobalTheory.CMData.exists_field` in the module `Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves`. Its proof rests on 153 declarations, and the five theorems use it.

Let K be a quadratic number field and σ a non-real embedding of K into ℂ, so that K is imaginary quadratic. Then there is a number field M inside ℂ containing σ(K) such that every invertible fractional ideal I of 𝒪_K has a Weierstrass curve W over 𝒪_M with unit discriminant. For this W, every lattice L′ with c₄(W) = 12g₂(L′) and Δ(W) = g₂(L′)³ − 27g₃(L′)² is a nonzero complex multiple of σ(I). The equations c₄ = 12g₂ and Δ = g₂³ − 27g₃² hold for the model y² = x³ − (g₂/4)x − g₃/4 of ℂ/L′, so the claim says that W is a model of the elliptic curve ℂ/σ(I) with good reduction at every prime of M.

```
K imaginary quadratic ⇒ ∃ number field M ⊃ σ(K), ∀ I ∈ I_K, ∃ W over 𝒪_M with Δ(W) ∈ 𝒪_M^×, ∀ L′ (c₄(W) = 12g₂(L′) ∧ Δ(W) = g₂(L′)³ − 27g₃(L′)² ⇒ L′ ∈ ℂ^×·σ(I))
```

The first reader gives it the kind technical step and names the published result as follows. Everywhere good reduction of the elliptic curves with complex multiplication by 𝒪_K over one suitable number field, which rests on the Serre–Tate theorem that such curves have potentially good reduction at every prime. Jean-Pierre Serre and John Tate, Good reduction of abelian varieties, Annals of Mathematics 88, 1968.

The second reader gives it the kind standard fact and the check the kind technical step. The check names the published result as follows. Potential good reduction everywhere of elliptic curves with complex multiplication (Serre and Tate), in the global form of a Weierstrass model with unit discriminant over one number field for all curves with complex multiplication by 𝒪_K. For the relation to that result the check has stronger, the first reader stronger and the second reader special case.

The check adds this. The two equations on L′ fix g₂(L′) and fix g₃(L′) up to sign, so the conclusion says exactly that W has the j-invariant of σ(I), and the statement covers only curves with complex multiplication by the maximal order, which is narrower than the Serre–Tate theorem even though its conclusion asks for more.

On emptiness the check wrote this. None found, because a unit discriminant is nonzero in ℂ, so period pairs that meet the two equations exist and the inner claim has content.

### 93, `graded_bezout_bound`

The theorem is `GlobalTheory.graded_bezout_bound` in the module `Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne`. Its proof rests on 153 declarations, and the five theorems use it.

Let K be algebraically closed and T an ℕ-graded K-algebra that is a domain of Krull dimension g + 1 with g ≥ 1, finite over the subalgebra generated by degree-one elements x₁, …, x_m, and with dim_K T_e ≤ (Ne)^g for all e ≥ 1. Let s be a nonzero element of degree d and F a set of elements of degree a, and assume that only finitely many K-points of Proj T vanish on F, where a K-point is a K-algebra map T → K that does not kill all x_i, taken up to the scaling φ(y) = c^e ψ(y) on T_e. Then any family of pairwise inequivalent K-points that vanish on s and on F has at most N^g · g! · d · a^{g−1} members.

```
X = Proj T, dim X = g, dim T_e ≤ (Ne)^g, #(X ∩ V(F)) < ∞ ⇒ #(X ∩ V(F) ∩ V(s)) ≤ N^g · g! · d · a^{g−1}
```

The first reader gives it the kind technical step and names the published result as follows. A Bézout inequality for the points of a projective variety cut out by hypersurfaces, with the degree of the variety bounded by N^g g! through its Hilbert function. William Fulton, Intersection Theory, 1984, Example 8.4.6.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A Bézout inequality for a projective variety X of dimension g whose degree is at most g!·N^g by its Hilbert function, bounding the points cut out by a form of degree d and forms of degree a with finitely many common zeros by deg X · d · a^(g−1), a consequence of the refined Bézout theorem (Fulton, Intersection Theory, Example 8.4.6). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The exponent g − 1 on a, in place of g, comes from cutting X first by s and then by g − 1 general combinations of F, and the finiteness of the common zeros of F is what keeps each cut proper.

On emptiness the check wrote this. None found, because the polynomial ring in g + 1 variables with N = 2 and F = {x₁^a, …, x_g^a} meets the hypotheses, while an empty F would make the finiteness hypothesis fail.

### 94, `isOpen_sectionComponents_of_family`

The theorem is `GlobalTheory.IdCompOpen.isOpen_sectionComponents_of_family` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupScheme`. Its proof rests on 152 declarations, and the five theorems use it.

Let f be a smooth morphism of schemes from X to S with a section e, and let C be the set of points x of X that lie in the connected component of the fibre f⁻¹(f(x)) containing e(f(x)). Suppose O assigns to each open set U of X an open set O(U), such that every y ∈ C with e(f(y)) ∈ U lies in O(U), and such that every y ∈ O(U) lies in C whenever all points of U in the fibre of y lie in C. Then C is open in X.

```
f ∈ Hom(X, S) smooth, f ∘ e = id_S, C = {x ∈ X | x ∈ connected component of f⁻¹(f(x)) through e(f(x))}, (h1), (h2) ⇒ C open in X
```

The first reader gives it the kind technical step and names the published result as follows. Openness of the union of the connected components of the fibres that meet a section of a smooth morphism, which is the identity component in the case of group schemes, here with two extra hypotheses on an auxiliary family of open sets. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique IV, troisième partie, Publications Mathématiques de l'IHÉS 28, 1966, §15.6.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Openness of the union of the connected components of the fibres that meet a section of a smooth morphism (EGA IV 15.6.5, and SGA 3 VI_B 3.10 for the identity component of a smooth group scheme). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The two conditions on O reduce openness of C to the existence, at each point of the section, of an open neighbourhood that lies inside C, and that step is where smoothness enters.

On emptiness the check wrote this. None found, because the constant family O(U) = C meets the two conditions once C is known to be open, and the conditions do not give openness without smoothness, as the scheme Spec R[t]/(t(t − π)) over a discrete valuation ring with the section t = 0 shows.

### 95, `dblA`

The theorem is `PI.GalTorsConj.W.ZetaDoubling.dblA` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl`. Its proof rests on 152 declarations, and the five theorems use it.

For a lattice L in ℂ and a point z with z ∉ L and 2z ∉ L, the Weierstrass function satisfies ℘(2z) = ℘(z) − (12℘(z)℘′(z)² − (6℘(z)² − g₂/2)²)/(4℘′(z)²). The identity ℘″ = 6℘² − g₂/2 turns the right side into (℘″(z)/℘′(z))²/4 − 2℘(z).

```
z, 2z ∉ L ⇒ ℘(2z) = ℘(z) − [12℘(z)℘′(z)² − (6℘(z)² − g₂/2)²] / (4℘′(z)²)
```

The first reader gives it the kind named theorem and names the published result as follows. Duplication formula for the Weierstrass ℘-function. E. T. Whittaker and G. N. Watson, A Course of Modern Analysis, fourth edition, 1927, Chapter XX.

The second reader gives it the kind standard fact and the check the kind named theorem. The check names the published result as follows. Duplication formula for the Weierstrass ℘-function. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The right side equals (℘″(z)/℘′(z))²/4 − 2℘(z) through ℘″ = 6℘² − g₂/2, and the hypothesis 2z ∉ L is exactly what makes ℘′(z) nonzero for z ∉ L.

### 96, `cdAbs`

The theorem is `UpperTheory.Kd.K4.cdAbs` in the module `Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CountSpanEqZero`. Its proof rests on 152 declarations, and the five theorems use it.

Let k be an algebraically closed field of characteristic zero and K a finite extension of k(X) with the induced k[X]-structure, let m, m′ > 0, and let f ∈ K be nonzero such that at every valuation ring B of K containing k[X], f equals a unit of B times an m-th power. Then there is a nonzero h ∈ K such that at every such B, f/h^m equals a unit times an (mm′)-th power. In terms of divisors on the affine curve C over the X-line, if div(f) = mD, then the class of D in Cl(C) is divisible by m′.

```
div_C(f) = mD ⇒ ∃ h ∈ K^×, div_C(f/h^m) ∈ mm′·Div(C), equivalently [D] ∈ m′·Cl(C)
```

The first reader gives it the kind technical step and names the published result as follows. A consequence of the divisibility of the divisor class group of a smooth affine curve over an algebraically closed field, applied to divisor classes that are m-torsion. David Mumford, Abelian Varieties, 1970.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A consequence of the divisibility of the divisor class group of a smooth affine curve over an algebraically closed field, applied to the m-torsion class of div(f)/m. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. In terms of divisors on the affine curve C over the X-line, the statement says that if div(f) = mD, then the class of D in Cl(C) is divisible by m′.

### 97, `alg_main`

The theorem is `GlobalTheory.JR.UnramInt.alg_main` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiser`. Its proof rests on 150 declarations, and the five theorems use it.

Let F be a non-archimedean local field, given as a complete, locally compact, ultrametric nontrivially normed field, and let E be a finite normed extension of F with the same value group, so that E/F is unramified. Let K be a finite extension of F and L a quadratic extension of K generated over K by the image of E, with all maps compatible. Then there are ϖ ∈ K^× and the ring O of elements of L with spectral norm at most 1 such that ϖ is not a norm from L, ϖ generates the maximal ideal of O, the trace maps O onto 𝒪_K, every unit of 𝒪_K is the norm of an element of O, multiplication by powers of ϖ shrinks O uniformly to zero, and every element of L becomes integral after multiplication by some power of ϖ.

```
dim_K L = 2, L = K·E, e(E/F) = 1 ⇒ ∃ ϖ ∈ K^×, O = {y ∈ L | ‖y‖ ≤ 1}, ϖ ∉ N_{L/K}(L), 𝔪_O = ϖO, Tr_{L/K}(O) = 𝒪_K, 𝒪_K^× ⊂ N_{L/K}(O), sup_{z ∈ O} ‖ϖ^n z‖ → 0, L = ⋃_n ϖ^{−n}O
```

The first reader gives it the kind technical step and names the published result as follows. Standard properties of an unramified quadratic extension of local fields, namely that a uniformizer of the base stays a uniformizer and is not a norm, while units are norms and the trace on integers is surjective. Jean-Pierre Serre, Local Fields, 1979, Chapters III and V.

The second reader gives it the kind standard fact and the check the kind technical step. The check names the published result as follows. The standard properties of an unramified quadratic extension of non-archimedean local fields, by which a uniformizer of the base stays a uniformizer and is not a norm, every unit is the norm of an integer and the trace on integers is surjective (Serre, Local Fields, Chapters III and V). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The extension L/K is unramified because E has the value group of F and generates L over K, and every clause of the conclusion rests on that property, which the statement never names.

On emptiness the check wrote this. None found, because F = K = ℚ_p with E = L the unramified quadratic extension of ℚ_p meets the hypotheses.

The check found these errors in the first reader's account of the Lean text, and the account above is printed as the reader wrote it.

- A writes that the trace maps O onto 𝒪_K, while the Lean text states only that every s of K lying in O is the trace of some z in O and leaves the inclusion of the traces of O in 𝒪_K unstated.

### 98, `stepA`

The theorem is `PI.GalTorsConj.W.OriginCoordinatesAdd.stepA` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw`. Its proof rests on 150 declarations, and the five theorems use it.

For a lattice L in ℂ and points z and w with z, w, z − w and z + w outside L, ℘(z + w) = ℘(z) − ((6℘(z)² − g₂/2)(℘(z) − ℘(w)) − (℘′(z) − ℘′(w))℘′(z))/(2(℘(z) − ℘(w))²). The differential equation ℘′² = 4℘³ − g₂℘ − g₃ shows that the right side equals (1/4)((℘′(z) − ℘′(w))/(℘(z) − ℘(w)))² − ℘(z) − ℘(w), so the statement is the addition theorem in a rearranged form.

```
z, w, z ± w ∉ L ⇒ ℘(z + w) = ℘(z) − [(6℘(z)² − g₂/2)(℘(z) − ℘(w)) − (℘′(z) − ℘′(w))℘′(z)] / (2(℘(z) − ℘(w))²)
```

The first reader gives it the kind technical step and names the published result as follows. Addition theorem for the Weierstrass ℘-function, written in a rearranged algebraic form. E. T. Whittaker and G. N. Watson, A Course of Modern Analysis, fourth edition, 1927, Chapter XX.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Addition theorem for the Weierstrass ℘-function, rewritten with the differential equation ℘′² = 4℘³ − g₂℘ − g₃ into a form whose limit as w tends to z can be taken. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The hypotheses z − w ∉ L and z + w ∉ L together make ℘(z) − ℘(w) nonzero, which is what the division needs.

### 99, `collinear`

The theorem is `Formalism.L2.Th1.E.AddThm.collinear` in the module `Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient`. Its proof rests on 149 declarations, and the five theorems use it.

For a lattice L and points z and w with z, w and z + w outside L, (℘(z) − ℘(w))℘′(z + w) = −((℘′(z) − ℘′(w))(℘(z + w) − ℘(z)) + ℘′(z)(℘(z) − ℘(w))). The identity says that the points (℘(z), ℘′(z)), (℘(w), ℘′(w)) and (℘(z + w), −℘′(z + w)) of the curve y² = 4x³ − g₂x − g₃ lie on one line.

```
z, w, z + w ∉ L ⇒ (℘(z) − ℘(w))℘′(z + w) = −[(℘′(z) − ℘′(w))(℘(z + w) − ℘(z)) + ℘′(z)(℘(z) − ℘(w))]
```

The first reader gives it the kind standard fact and names the published result as follows. The determinant form of the addition theorem for ℘, which says that the points (℘(u), ℘′(u)), (℘(v), ℘′(v)) and (℘(w), ℘′(w)) are collinear when u + v + w = 0. E. T. Whittaker and G. N. Watson, A Course of Modern Analysis, fourth edition, 1927, Chapter XX.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The collinearity or determinant form of the addition theorem for ℘, by which the points of y² = 4x³ − g₂x − g₃ with parameters u, v and w satisfying u + v + w ≡ 0 lie on one line (Whittaker and Watson, §20.3). For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The identity is written with the denominator ℘(z) − ℘(w) cleared, which is why it needs no hypothesis on z − w.

On emptiness the check wrote this. None found, although both sides vanish when z − w lies in L, so the identity has content only when z − w lies outside L.

### 100, `P_add`

The theorem is `Formalism.L2.Th1.E.AddThm.P_add` in the module `Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient`. Its proof rests on 148 declarations, and the five theorems use it.

For a lattice L and points z and w with z, w, z + w and z − w outside L, ℘(z + w) = (1/4)((℘′(z) − ℘′(w))/(℘(z) − ℘(w)))² − ℘(z) − ℘(w).

```
z, w, z ± w ∉ L ⇒ ℘(z + w) = ¼((℘′(z) − ℘′(w))/(℘(z) − ℘(w)))² − ℘(z) − ℘(w)
```

The first reader gives it the kind named theorem and names the published result as follows. Addition theorem for the Weierstrass ℘-function. E. T. Whittaker and G. N. Watson, A Course of Modern Analysis, fourth edition, 1927, Chapter XX.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Addition theorem for the Weierstrass ℘-function. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. For z and w outside L the hypothesis z ± w ∉ L is equivalent to ℘(z) ≠ ℘(w), so the four hypotheses are exactly the classical ones.

### 101, `pNeg`

The theorem is `PI.GalTorsConj.W.pNeg` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.StAddRight`. Its proof rests on 144 declarations, and the five theorems use it.

Let L be the lattice of a period pair in ℂ, and let ℘ and ℘′ be its Weierstrass function and the derivative of that function. Take complex numbers z and w that lie outside L with ℘(z) = ℘(w) and ℘′(z) = −℘′(w). Then z + w lies in L.

```
∀ z, w ∈ ℂ ∖ L, ℘_L(z) = ℘_L(w) ∧ ℘_L′(z) = −℘_L′(w) ⇒ z + w ∈ L
```

The first reader gives it the kind standard fact and names the published result as follows. Injectivity of the Weierstrass parametrization z ↦ (℘(z), ℘′(z)) on ℂ/L without the origin, applied to z and −w, using that ℘ is even and ℘′ is odd. Joseph H. Silverman, The Arithmetic of Elliptic Curves, 1986, Chapter VI.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Injectivity of the Weierstrass parametrization z ↦ (℘(z), ℘′(z)) on (ℂ/L) ∖ {0}, part of the uniformization ℂ/L ≅ E(ℂ) (Silverman, The Arithmetic of Elliptic Curves, Proposition VI.3.6), applied to z and −w. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Because ℘ is even and ℘′ is odd, the hypotheses say that z and −w have the same image under (℘, ℘′), so the statement is theorem 103 applied to z and −w.

### 102, `weierstrassP_superlattice_half_period_prod`

The theorem is `GlobalTheory.T.weierstrassP_superlattice_half_period_prod` in the module `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeierstrassPSuperlatticeHalfPeriodProdStatement`. Its proof rests on 143 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.HalfPeriodProduct.wp_half_period_prod`.

Let L ⊆ L′ be period lattices in ℂ. Let T be a finite set of points of L′ outside L that are pairwise incongruent modulo L and that, together with 0, represent every class of L′/L. Let w be a point with 2w ∈ L and w ∉ L′. Then for every z ∉ L′, the product of ℘_{L′}(z) − ℘_{L′}(w) with the factors ℘_L(z) − ℘_L(t) for t ∈ T equals the product of ℘_L(z) − ℘_L(w) with the factors ℘_L(z) − ℘_L(w + t) for t ∈ T.

```
(℘_{L′}(z) − ℘_{L′}(w)) ∏_{t∈T} (℘_L(z) − ℘_L(t)) = (℘_L(z) − ℘_L(w)) ∏_{t∈T} (℘_L(z) − ℘_L(w + t)) for z ∉ L′, where L′ = L ⊔ ⨆_{t∈T} (t + L), 2w ∈ L and w ∉ L′
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, an identity of elliptic functions that writes ℘_{L′} − ℘_{L′}(w) as a rational function of ℘_L for the isogeny ℂ/L → ℂ/L′, of the kind behind Vélu's isogeny formulas.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, an identity of elliptic functions that writes ℘_{L′}(z) − ℘_{L′}(w) for a superlattice L′ ⊇ L and a half-period w of L outside L′ as a rational function of ℘_L(z), in the spirit of Vélu's isogeny formulas. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. Both sides are L-elliptic functions of z whose only pole is at 0, of order 2(|T| + 1) with leading coefficient 1, and whose zeros are double zeros at the points w + s for s in L′/L, so the identity can be checked by comparing divisors and leading terms.

On emptiness the check wrote this. No hypothesis is impossible, and the identity holds at once only in the subcase L′ = L, where T is empty and both sides coincide.

### 103, `pInj`

The theorem is `PI.GalTorsConj.W.pInj` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.StAddRight`. Its proof rests on 143 declarations, and the five theorems use it.

Let L be the lattice of a period pair in ℂ. Take complex numbers z and w that lie outside L with ℘(z) = ℘(w) and ℘′(z) = ℘′(w), where ℘ is the Weierstrass function of L. Then z − w lies in L.

```
∀ z, w ∈ ℂ ∖ L, ℘_L(z) = ℘_L(w) ∧ ℘_L′(z) = ℘_L′(w) ⇒ z − w ∈ L
```

The first reader gives it the kind standard fact and names the published result as follows. Injectivity of the Weierstrass parametrization z ↦ (℘(z), ℘′(z)) on ℂ/L without the origin, part of the isomorphism of ℂ/L with the complex points of the elliptic curve y² = 4x³ − g₂x − g₃. Joseph H. Silverman, The Arithmetic of Elliptic Curves, 1986, Chapter VI.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Injectivity part of the Weierstrass uniformization ℂ/L ≅ E(ℂ), z ↦ (℘(z), ℘′(z)) (Silverman, The Arithmetic of Elliptic Curves, Proposition VI.3.6). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The statement keeps only injectivity, while the textbook result also gives surjectivity onto the affine points of y² = 4x³ − g₂x − g₃ and compatibility with the group laws.

### 104, `exists_continuous_normCharLFunction_ne_zero_one`

The theorem is `GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousNormCharLFunctionNeZeroOneStatement`. Its proof rests on 142 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.NormCharL.exists_continuous_ne_zero_one`.

Let K be a number field, m a prime number and χ a character of (ℤ/mℤ)ˣ. Let cl be a map from the nonzero primes P of the ring of integers of K to (ℤ/mℤ)ˣ that sends every P whose norm N(P) is prime to m to the class of N(P). If χ(cl P) ≠ 1 for some P with m ∤ N(P), then there is a continuous function L on ℂ with L(1) ≠ 0. For every real s > 1 this L agrees with the exponential of the sum over P of −log(1 − χ(cl P) N(P)^{−s}), which is the Euler product ∏_P (1 − χ(cl P) N(P)^{−s})^{−1}.

```
(∃ P, m ∤ N(P) ∧ χ(cl P) ≠ 1) ⇒ ∃ L ∈ C(ℂ, ℂ), L(1) ≠ 0 ∧ ∀ s ∈ ℝ, s > 1 ⇒ exp(∑_P −log(1 − χ(cl P) N(P)^{−s})) = L(s)
```

The first reader gives it the kind technical step and names the published result as follows. Nonvanishing at s = 1 of the L-function of a nontrivial finite-order Hecke character, here P ↦ χ(N(P) mod m), with Euler factors at the primes above m that use arbitrary roots of unity. Jürgen Neukirch, Algebraic Number Theory, 1999, Chapter VII.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Nonvanishing at s = 1 of the L-function of a nontrivial ray class character (Hecke, Landau), here for the character P ↦ χ(N(P) mod m), with arbitrary values of χ in the Euler factors at the primes above m. For the relation to that result the check has weaker, the first reader weaker and the second reader special case.

The check adds this. The function L has to agree with the Euler product only at real s > 1, so the conclusion says only that this product has a nonzero limit as s decreases to 1, and the statement covers only characters of the form χ ∘ N with m prime.

### 105, `exists_eq_smul_pow`

The theorem is `GlobalTheory.KeyFourth.exists_eq_smul_pow` in the module `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif`. Its proof rests on 140 declarations, and the five theorems use it.

Let K be a field with a ring map to ℂ, and let A be a smooth K-algebra such that ℂ ⊗_K A is a domain. Let n > 0, let u be a unit of A and let C be a nonzero complex number. Suppose that ρ is a function on the K-algebra maps ψ from A to ℂ, that ρ is continuous along every holomorphic family of such maps over an open subset of some ℂ^m, and that ρ(ψ)^n = C ψ(u) for every ψ. Then u = a b^n for some nonzero a in K and some b in A.

```
(ρ continuous on Hom_K(A, ℂ) ∧ ∀ ψ, ρ(ψ)^n = C ψ(u)) ⇒ ∃ a ∈ K^×, ∃ b ∈ A, u = a b^n
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a Kummer-type descent lemma saying that a unit on a smooth geometrically integral variety is an n-th power up to a constant once a constant multiple of it has a continuous n-th root on the complex points.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a Kummer-type descent lemma saying that a unit on a smooth geometrically integral affine variety is a constant times an n-th power once a constant multiple of it has a continuous n-th root on the complex points. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. Continuity along holomorphic families amounts to continuity on the complex points in the analytic topology, because the complex points of the smooth variety form a complex manifold with holomorphic charts.

### 106, `zero_density_mult`

The theorem is `GlobalTheory.ZeroDensityMult.zero_density_mult` in the module `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReLtOneOfZero`. Its proof rests on 139 declarations, and the five theorems use it.

There is a constant C > 0 with the following property for every real Q ≥ 3. Take any finite set T of triples (q, χ, ρ) in which χ is a primitive Dirichlet character of modulus q ≤ Q and ρ is a zero of L(s, χ) with Re ρ ≥ 1 − 1/400 and |Im ρ| ≤ Q. Then the orders of these zeros add up to at most C Q^{1/4}.

```
∃ C > 0, ∀ Q ≥ 3, ∑_{q ≤ Q} ∑*_{χ mod q} ∑_{L(ρ, χ) = 0, Re ρ ≥ 1 − 1/400, |Im ρ| ≤ Q} ord_ρ L(·, χ) ≤ C Q^{1/4}
```

The first reader gives it the kind technical step and names the published result as follows. Large sieve zero-density estimate for the family of primitive Dirichlet L-functions, in a weak instance close to the line Re s = 1. Hugh L. Montgomery, Topics in Multiplicative Number Theory, 1971.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Large sieve zero-density estimate for the family of primitive Dirichlet L-functions near Re s = 1 (Montgomery, Topics in Multiplicative Number Theory, 1971), in a weak instance. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Density estimates of Montgomery's type bound this count by about Q^{9/401} times a power of log Q, so the exponent 1/4 leaves much room, and the trivial character of modulus 1 counts as primitive, which brings the zeros of the Riemann zeta function into the sum.

### 107, `derivWeierstrassP_ne_zero`

The theorem is `PI.GalTorsConj.W.ZetaDoubling.derivWeierstrassP_ne_zero` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl`. Its proof rests on 137 declarations, and the five theorems use it.

Let L be the lattice of a period pair in ℂ, and let z be a point with z ∉ L and 2z ∉ L. Then the derivative ℘′(z) of the Weierstrass function of L is nonzero.

```
z ∉ L ∧ 2z ∉ L ⇒ ℘_L′(z) ≠ 0
```

The first reader gives it the kind standard fact and names the published result as follows. The zeros of ℘′ are exactly the three half periods modulo L. Lars V. Ahlfors, Complex Analysis, 1979, Chapter 7.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The zeros of ℘′ modulo L are exactly the three nonzero half-periods (the direction that ℘′ vanishes only at half-periods). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypothesis z ∉ L is redundant, because z ∈ L would give 2z ∈ L.

### 108, `rational_units_haar_character_one`

The theorem is `GlobalTheory.T.rational_units_haar_character_one` in the module `Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparateStatement`. Its proof rests on 135 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal`.

Let F be a number field, and assume as instances that its adele ring 𝔸_F is locally compact and that 2 is invertible in 𝔸_F. Then every nonzero a in F, viewed as a unit of 𝔸_F, has Haar character 1. This means that multiplication by a preserves Haar measure on 𝔸_F.

```
∀ a ∈ F^×, |a|_{𝔸_F} = μ(aE)/μ(E) = ∏_v |a|_v = 1 for a Haar measure μ on 𝔸_F
```

The first reader gives it the kind named theorem and names the published result as follows. The product formula for a number field in Weil's adelic form, which says that the module of a principal idele is 1. André Weil, Basic Number Theory, 1967.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Product formula ∏_v |a|_v = 1 for a ∈ Fˣ (Artin and Whaples), in Weil's form that the module of a principal idele acting on the adele ring is 1 (Weil, Basic Number Theory). For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The instance hypotheses that the adele ring is locally compact and that 2 is invertible in it hold for every number field, so they restrict nothing.

### 109, `exists_dixmierMalliavin_line`

The theorem is `GroundTheory.Automorphic.exists_dixmierMalliavin_line` in the module `GroundTheory.AutomorphicForms.DixmierMalliavinLine`. Its proof rests on 133 declarations, and the five theorems use it.

Take any real sequence (M_p) and any ε > 0. Then there are a real sequence (c_p) for which ∑ |c_p| M_p converges and smooth complex functions g and h supported in [−ε, ε] with the following property. Every smooth F from ℝ to ℂ whose p-th derivative has absolute value at most M_p on [−ε, ε] for every p satisfies F(0) = ∑_p c_p ∫ F^{(p)} g + ∫ F h.

```
∀ M, ∀ ε > 0, ∃ c, ∃ g, h ∈ C_c^∞([−ε, ε]), ∑ |c_p| M_p < ∞ ∧ ∀ F ∈ C^∞ with sup_{[−ε, ε]} |F^{(p)}| ≤ M_p, F(0) = ∑_p c_p ∫ F^{(p)} g dt + ∫ F h dt
```

The first reader gives it the kind standard fact and names the published result as follows. The one-dimensional lemma of Dixmier and Malliavin, δ = h + ∑ c_p (−1)^p g^{(p)} with ∑ |c_p| r_p < ∞, which drives their factorization theorem. Jacques Dixmier and Paul Malliavin, Factorisations de fonctions et de vecteurs indéfiniment différentiables, 1978.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Dixmier–Malliavin lemma (Dixmier and Malliavin, 1978), the one-variable decomposition δ = h + ∑_p (−1)^p c_p g^{(p)} that underlies their factorization theorem. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The identity is required only for smooth F whose derivatives obey the bounds M_p on [−ε, ε], and integration by parts turns it into the usual distributional form of the lemma.

On emptiness the check wrote this. Only in the subcase where some M_p is negative does the conclusion hold at once, since no F meets the bounds and c, g and h equal to zero work, while for nonnegative M the statement has its full content.

### 110, `P_sub_ne`

The theorem is `Formalism.L2.Th1.E.AddThm.P_sub_ne` in the module `Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient`. Its proof rests on 132 declarations, and the five theorems use it.

Fix the lattice L of a period pair in ℂ as a variable. Take points z and w such that z, w, z + w and z − w all lie outside L. Then ℘(z) − ℘(w) ≠ 0, where ℘ is the Weierstrass function of L.

```
z, w, z + w, z − w ∉ L ⇒ ℘_L(z) − ℘_L(w) ≠ 0
```

The first reader gives it the kind standard fact and names the published result as follows. The fact that ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo L. Lars V. Ahlfors, Complex Analysis, 1979, Chapter 7.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo L (the direction that z ≢ ±w forces ℘(z) ≠ ℘(w)). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Theorem 111 states the same with the hypotheses z + w ∉ L and z − w ∉ L in the other order.

### 111, `wp_ne`

The theorem is `PI.GalTorsConj.W.OriginCoordinatesAdd.wp_ne` in the module `Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw`. Its proof rests on 132 declarations, and the five theorems use it.

Let L be the lattice of a period pair in ℂ, and take points z and w such that z, w, z − w and z + w all lie outside L. Then ℘(z) − ℘(w) ≠ 0, where ℘ is the Weierstrass function of L.

```
z, w, z − w, z + w ∉ L ⇒ ℘_L(z) − ℘_L(w) ≠ 0
```

The first reader gives it the kind standard fact and names the published result as follows. The fact that ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo L. Lars V. Ahlfors, Complex Analysis, 1979, Chapter 7.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo L (the direction that z ≢ ±w forces ℘(z) ≠ ℘(w)). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The statement repeats theorem 110 with the hypotheses z − w ∉ L and z + w ∉ L in the other order.

### 112, `exists_open_nbhd_section_fiber_isPreirreducible`

The theorem is `GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNbhdSectionFibreIsPreirreducibleStatement`. Its proof rests on 131 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible`.

Let f from X to S be a smooth morphism of schemes with a section e. For every point s of S there are an open U of X containing e(s), opens V₀ ⊆ V of S containing s, and a finite set I of functions on V that all vanish at s. These satisfy the following condition. For every t in V₀ at which all functions of I vanish, the part of the fibre f^{−1}(t) that lies in U is preirreducible, that is, irreducible or empty.

```
∀ s ∈ S, ∃ U ∋ e(s), ∃ V₀ ⊆ V ∋ s, ∃ I ⊆ Γ(V, 𝒪_S) finite with I(s) = 0, ∀ t ∈ V₀ ∩ V(I), U ∩ f^{−1}(t) is preirreducible
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a local statement on the irreducibility of fibres near a section of a smooth morphism, of the kind derived from Grothendieck's constructibility of geometric irreducibility of fibres in EGA IV.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A weak local form of the openness of the union X⁰ of the connected components of the fibres that meet a section of a smooth morphism (EGA IV_3, §15.6, and SGA 3, Exp. VI_B, 3.10 for group schemes), whose fibres are irreducible because smooth fibres are normal. For the relation to that result the check has weaker, the first reader none and the second reader weaker.

The check adds this. Adding members to the existential set I only shrinks the set of fibres that must be preirreducible, so the strongest form takes I empty, and that form follows with U = X⁰ and V₀ = V = S.

### 113, `exists_lift_adicCompletion`

The theorem is `GlobalTheory.TraitLift.exists_lift_adicCompletion` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion`. Its proof rests on 130 declarations, and the five theorems use it.

Let A be a local ring essentially of finite type over ℤ with completion Â at its maximal ideal, and let V be a discrete valuation ring with a ring map from A. Then there are a complete discrete valuation ring V′, a ring map h from V to V′ that sends every uniformizer of V to a uniformizer of V′, and a ring map g from Â to V′. The restriction of g to A equals the composite A → V → V′.

```
∃ V′ complete DVR, ∃ h ∈ Hom(V, V′), ∃ g ∈ Hom(Â, V′), g ∘ (A → Â) = h ∘ (A → V) ∧ h(ϖ) is irreducible for every irreducible ϖ of V
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a lemma that extends a map from an excellent local ring to a discrete valuation ring over the completion of the local ring after an unramified enlargement of the valuation ring.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a lemma that extends a ring map from a local ring essentially of finite type over ℤ to a discrete valuation ring over the completion of the local ring, after an enlargement of the valuation ring to a complete discrete valuation ring that keeps uniformizers. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The map from A to V need not be local, and the content lies in that case, because for a local map the completion of V serves as V′.

### 114, `ferrand_glue_flat_artinian_fibreProduct`

The theorem is `GlobalTheory.T.ferrand_glue_flat_artinian_fibreProduct` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProductStatement`. Its proof rests on 128 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.FerrandGlue.ferrand_glue_artinian`.

Let P = R₁ ×_{R₀} R₂ be a fibre product of commutative rings along surjections R₁ → R₀ and R₂ → R₀, and let P be local and Artinian. Let Y₁ and Y₂ be flat schemes over Spec R₁ and Spec R₂ whose base changes to Spec R₀ are both identified with a scheme Y₀ over Spec R₀. Then there is a flat scheme Y over Spec P with maps from Y₁ and Y₂ that identify them with the base changes of Y to Spec R₁ and Spec R₂. Moreover, Y is the pushout of Y₁ and Y₂ along Y₀ in the category of schemes.

```
Y = Y₁ ⊔_{Y₀} Y₂ is flat over Spec(R₁ ×_{R₀} R₂) and Y ×_{Spec P} Spec R_i ≅ Y_i for i = 1, 2
```

The first reader gives it the kind standard fact and names the published result as follows. Gluing of flat deformations over a fibre product of Artinian rings, Schlessinger's condition for deformations of schemes. Michael Schlessinger, Functors of Artin rings, 1968.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Gluing of flat schemes over a fibre product of Artinian rings, the Schlessinger condition for the deformation functor of a scheme (Schlessinger 1968), together with Ferrand's pinching that makes the glued scheme a pushout. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Surjectivity of R₁ → R₀ and R₂ → R₀ makes P → R₁ and P → R₂ surjective, so all four rings are local Artinian, while Schlessinger's gluing needs only one surjection, and the pushout claim comes from Ferrand's pinching along closed immersions.

### 115, `exists_field_cm_curves_unit_discriminant`

The theorem is `GlobalTheory.exists_field_cm_curves_unit_discriminant` in the module `Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant`. Its proof rests on 127 declarations, and the five theorems use it.

Let K be an imaginary quadratic field with a complex embedding σ. Then there is a number field M ⊆ ℂ containing σ(K) with the following property. For every lattice L ⊂ ℂ that is stable under multiplication by σ(𝒪_K), there is a Weierstrass curve W over 𝒪_M whose discriminant Δ(W) is a unit and whose j-invariant equals j(L). The equality of j-invariants is written as c₄(W)³ (g₂³ − 27g₃²) = 1728 g₂³ Δ(W).

```
∀ K imaginary quadratic, ∃ M ⊂ ℂ number field with σ(K) ⊆ M, ∀ L with σ(𝒪_K)L ⊆ L, ∃ W over 𝒪_M, Δ(W) ∈ 𝒪_M^× ∧ c₄(W)³ (g₂(L)³ − 27g₃(L)²) = 1728 g₂(L)³ Δ(W)
```

The first reader gives it the kind standard fact and names the published result as follows. Potential good reduction everywhere of elliptic curves with complex multiplication, strengthened to a single number field over which every curve with complex multiplication by 𝒪_K has a global Weierstrass model of unit discriminant. Jean-Pierre Serre and John Tate, Good reduction of abelian varieties, 1968.

The second reader gives it the kind technical step and the check the kind standard fact. The check names the published result as follows. Potential good reduction everywhere of elliptic curves with complex multiplication (Deuring, Serre and Tate 1968), strengthened to one number field M over which every curve with complex multiplication by 𝓞_K has a Weierstrass model over 𝓞_M with unit discriminant. For the relation to that result the check has stronger, the first reader stronger and the second reader stronger.

The check adds this. The polynomial identity says j(W) = j(L), because Δ(W) is a unit and g₂³ − 27g₃² ≠ 0, and a model with unit discriminant needs more than good reduction everywhere, namely a trivial class for the minimal discriminant, which an enlargement of M provides.

### 116, `exists_isStandardSmoothOfRelativeDimension_of_isMaximal`

The theorem is `GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_isMaximal` in the module `Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe`. Its proof rests on 126 declarations, and the five theorems use it.

Let o be a Dedekind domain of characteristic zero that is finitely generated over ℤ, and let A be a flat finitely generated o-algebra. Suppose that every irreducible component of the generic fibre Frac(o) ⊗_o A has dimension at least d. Suppose also that r ≤ d for every algebraically closed field C and every ring map from A to the square-zero extension C ⊕ C^r whose C^r-part vanishes on o and spans C^r, which bounds by d the dimension of every relative tangent space of Spec A over o at a geometric point. Then every maximal ideal q of A has an element f outside q such that the localization A_f is standard smooth of relative dimension d over o.

```
(∀ 𝔭 minimal in Frac(o) ⊗ A, dim (Frac(o) ⊗ A)/𝔭 ≥ d) ∧ (∀ x̄, dim T_{x̄}(Spec A / Spec o) ≤ d) ⇒ ∀ q maximal, ∃ f ∉ q, A_f is standard smooth of relative dimension d over o
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a smoothness criterion for flat finitely generated algebras over a Dedekind domain that combines the fibrewise criterion for smoothness with the Jacobian criterion on the fibres.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a smoothness criterion for flat finite-type algebras over a Dedekind domain assembled from the fibrewise criterion for smoothness (EGA IV_4 17.5.1), the tangent-space criterion on geometric fibres and the dimension theory of fibres of flat morphisms. For the relation to that result the check has none, the first reader none and the second reader special case.

The check adds this. The square-zero hypothesis says that dim_C Der_o(A, C) ≤ d at every geometric point, and flatness over the Dedekind base carries the lower bound d from the components of the generic fibre to the components of the closed fibres.

### 117, `exists_theta_division_point_ne_zero`

The theorem is `GlobalTheory.T.exists_theta_division_point_ne_zero` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDivisionPointNeZeroStatement`. Its proof rests on 126 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ThetaDivisionPoints.exists_division_point_ne_zero`.

Let τ be a symmetric complex g × g matrix with positive definite imaginary part, let N ≥ 2, and let β₁, …, β_g be nonzero complex numbers. Let f be a nonzero entire function on ℂ^g with f(z + e_i) = f(z) and f(z + τe_j) = β_j exp(−2πi N z_j) f(z) for all i, j and z. Then there are integer vectors m and n with f((m + τn)/N) ≠ 0, so f does not vanish at every N-division point of the lattice ℤ^g + τℤ^g.

```
f ≢ 0 entire, f(z + e_i) = f(z), f(z + τe_j) = β_j e^{−2πi N z_j} f(z), N ≥ 2 ⇒ ∃ m, n ∈ ℤ^g, f(N^{−1}(m + τn)) ≠ 0
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a statement that no nonzero theta function of level N ≥ 2 vanishes at all N-torsion points, which follows from the irreducibility of Mumford's theta group representation and the base point freeness of the N-th power of a principal polarization.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, the statement that a nonzero theta function of level N ≥ 2 does not vanish at every N-division point, which follows from the irreducibility of the theta group representation and the base point freeness of the N-th power of a principal polarization. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The arbitrary nonzero constants β_j allow every translate of the N-th power of the principal polarization, and the sections that vanish at all N-division points form a subspace stable under the theta group, which is zero by irreducibility and base point freeness.

### 118, `idealCharacterL_continuation_ne_zero_one`

The theorem is `GlobalTheory.idealCharacterL_continuation_ne_zero_one` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne`. Its proof rests on 126 declarations, and the five theorems use it.

Let K be a number field, m a nonzero ideal of 𝒪_K, and X a multiplicative function on ideals with X(0) = 0 that vanishes on ideals not coprime to m and has modulus 1 on nonzero ideals coprime to m. Let φ be a multiplicative function on K ⊗ ℝ that is invariant under positive real scalars and is smooth and of modulus 1 where the norm is nonzero, with X((β)) = φ(β) for every nonzero integer β ≡ 1 mod m, and assume X(J) ≠ 1 for some nonzero J coprime to m. Then for every function c on the primes with |c(P)| ≤ 1 and c(P) = X(P) for P not dividing m, there is a function L that is holomorphic on Re s > 0 with L(1) ≠ 0. For Re s > 1 this L equals the Euler product ∏_P (1 − c(P) N(P)^{−s})^{−1}, written as the exponential of a sum of logarithms.

```
X a nontrivial unitary Grössencharacter mod m with infinity type φ, |c(P)| ≤ 1, c(P) = X(P) for P ∤ m ⇒ ∃ L holomorphic on {Re s > 0}, L(s) = ∏_P (1 − c(P) N(P)^{−s})^{−1} for Re s > 1 ∧ L(1) ≠ 0
```

The first reader gives it the kind named theorem and names the published result as follows. Hecke's theorem on the analytic continuation of L-functions of nontrivial Grössencharacters and their nonvanishing at s = 1. Erich Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen II, 1920.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Hecke's theorem on the analytic continuation of L-functions of nontrivial Grössencharacters, together with their nonvanishing at s = 1. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Invariance of φ under positive real scalars rules out characters of the form N(I)^{it}, whose L-functions have a pole on Re s = 1, and the Euler factors at the primes dividing m may use any c(P) of modulus at most 1.

### 119, `isIso_of_isClosedImmersion`

The theorem is `GlobalTheory.AbMonoIso.isIso_of_isClosedImmersion` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion`. Its proof rests on 125 declarations, and the five theorems use it.

Let S be a locally noetherian scheme and let p from X to S be smooth of relative dimension g′ with geometrically connected fibres. Let f from Y to X be a closed immersion such that the composite Y → S is surjective, flat and smooth of relative dimension g with g′ ≤ g. Then f is an isomorphism.

```
f closed immersion, p smooth of relative dimension g′ with geometrically connected fibres, p ∘ f surjective, flat and smooth of relative dimension g ≥ g′ ⇒ f is an isomorphism
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a fibrewise criterion showing that a closed subscheme that meets every fibre and is smooth over S of no smaller relative dimension fills a smooth scheme with connected fibres.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a criterion that a closed subscheme which is surjective and smooth over S of relative dimension at least that of a smooth S-scheme with geometrically connected fibres is the whole scheme. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The flatness hypothesis follows from smoothness of the composite, and dimension forces g = g′, so f is an étale closed immersion whose image is open and closed in each connected fibre.

### 120, `formalFibre_isReduced_of_field`

The theorem is `GlobalTheory.formalFibre_isReduced_of_field` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsReducedOfField`. Its proof rests on 124 declarations, and the five theorems use it.

Let A be a local ring essentially of finite type over ℤ, and let L be a field with a ring map from A. Then the tensor product over A of the completion of A at its maximal ideal with L is a reduced ring.

```
Â ⊗_A L is reduced for every field L that is an A-algebra
```

The first reader gives it the kind standard fact and names the published result as follows. Geometric reducedness of the formal fibres of an excellent local ring, here for local rings essentially of finite type over ℤ, which Grothendieck proved to be excellent. Alexander Grothendieck, Éléments de géométrie algébrique IV, Seconde partie, 1965.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Geometric reducedness of the formal fibres of an excellent local ring, for local rings essentially of finite type over ℤ, which are excellent (EGA IV_2 7.8.3). For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The field L is arbitrary, so the statement covers every field extension of every residue field of A and says that all formal fibres of A are geometrically reduced.

### 121, `rem_2`

The theorem is `Formalism.MainNotions.CrystallineLiftingInputs.rem_2` in the module `Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool`. Its proof rests on 122 declarations, and the five theorems use it.

Take a commutative ring R, a natural number l ≥ 1, elements π₀, q, u, ε of R, and natural numbers y, X, c with y ≥ 1 and c + ⌊(X − 1)/l⌋ ≤ (l − 1)y. Then the element (π₀ q^{l−1} (u q^l + l ε)^{l−1})^y lies in the ideal of R generated by l^c and π₀ q^X. Here X − 1 is truncated subtraction in ℕ, the quotient is floor division, and l also stands for its image in R.

```
R comm. ring, l ≥ 1, π₀, q, u, ε ∈ R, y ≥ 1, c + ⌊(X ∸ 1)/l⌋ ≤ (l − 1)y ⟹ (π₀ q^{l−1} (u q^l + lε)^{l−1})^y ∈ (l^c, π₀ q^X)
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, an elementary ideal-membership estimate proved by a binomial expansion.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, an elementary ideal-membership estimate proved by a binomial expansion. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The quotient (X − 1)/l is floor division of natural numbers, and the membership is immediate when X ≤ (l − 1)y because the element has the factor π₀q^{(l−1)y}, so the hypothesis does real work only for larger X, where the binomial expansion of (u q^l + lε)^{(l−1)y} is needed.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with l = 2, y = 1, c = 1 and X = 1, although the conclusion is immediate when c = 0, which l = 1 forces, or when l is a unit in R.

### 122, `rem_M`

The theorem is `Formalism.MainNotions.CrystallineLiftingInputs.rem_M` in the module `Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool`. Its proof rests on 122 declarations, and the five theorems use it.

Take a commutative ring R, a natural number l ≥ 1, an element π₀ of R, and natural numbers y, M, η, c with c + η + M ≤ l y. Then the element (π₀ (π₀ + l)^{l−1})^y lies in the ideal of R generated by l^c and π₀^M (π₀ + l)^η. Here l also stands for its image in R.

```
R comm. ring, l ≥ 1, π₀ ∈ R, c + η + M ≤ l y ⟹ (π₀ (π₀ + l)^{l−1})^y ∈ (l^c, π₀^M (π₀ + l)^η)
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, an elementary ideal-membership estimate proved by a binomial expansion.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, an elementary ideal-membership estimate proved by a binomial expansion in π₀ and π₀ + l. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. With t = π₀ + l the element is π₀^y t^{(l−1)y}, whose total degree l·y in π₀ and t is at least c + M + η by the hypothesis, and that degree count is all the statement uses.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with l = 2, y = 1, c = 1, M = 1 and η = 0, although the conclusion is immediate when l = 1 or c = 0, because then l^c = 1.

### 123, `length_coker_le`

The theorem is `Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD.length_coker_le` in the module `Formalism.SharpRestriction.LevelLetterCocycles.LengthCokerLe`. Its proof rests on 122 declarations, and the five theorems use it.

Let O be a discrete valuation ring, QQ an r × r matrix over O, l a nonzero element of O, and V a natural number such that det QQ divides l^V. Then the length of the O-module O^r / QQ·O^r, which is the cokernel of the linear map given by QQ, is at most V times the length of O/(l), with lengths taken in ℕ ∪ {∞}. None of the section variables in scope, such as the period data and the module W, occurs in the statement, and the theorem binds its own ring O.

```
O DVR, QQ ∈ M_r(O), l ≠ 0, det QQ | l^V ⟹ length_O(O^r / QQ O^r) ≤ V · length_O(O/lO)
```

The first reader gives it the kind technical step and names the published result as follows. The formula that the length of the cokernel of an injective endomorphism of O^r over a discrete valuation ring equals the valuation of its determinant. William Fulton, Intersection Theory, 1984, Appendix A.2.

The second reader gives it the kind standard fact and the check the kind technical step. The check names the published result as follows. The formula that over a discrete valuation ring the length of the cokernel of a square matrix with nonzero determinant equals the valuation of the determinant. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The divisibility det QQ ∣ l^V with l ≠ 0 forces det QQ ≠ 0, so the cokernel has finite length equal to the valuation of det QQ, and the bound follows from v(det QQ) ≤ V·v(l), while the section variable W and the period data do not enter the statement.

### 124, `eq_zero_of_forall_sylow_map_eq_zero`

The theorem is `GroundTheory.ProfCoh.eq_zero_of_forall_sylow_map_eq_zero` in the module `GroundTheory.ProfiniteCohomology.GlobalClassFormation.NatCardGroupCohomologyTwoIdeleClassRepDvd`. Its proof rests on 122 declarations, and the five theorems use it.

Let k be a commutative ring, G a finite group, A a k-linear representation of G, and n ≥ 1. Suppose a class x in the group cohomology H^n(G, A) restricts to zero on some Sylow p-subgroup P of G for every prime p dividing |G|. Then x = 0. The restriction here is the map H^n(G, A) → H^n(P, A) induced by the inclusion of P into G and the identity of A.

```
n ≥ 1, x ∈ H^n(G, A), ∀ p | |G| ∃ P ∈ Syl_p(G) with res^G_P x = 0 ⟹ x = 0
```

The first reader gives it the kind standard fact and names the published result as follows. Injectivity of restriction to a Sylow p-subgroup on the p-primary part of H^n(G, A) for n ≥ 1, in its corollary form that a class vanishing on all Sylow subgroups is zero. Kenneth S. Brown, Cohomology of Groups, 1982, Chapter III, Section 10.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Injectivity of restriction to a Sylow p-subgroup on the p-primary part of positive-degree cohomology of a finite group, in the form that a class whose restriction to one Sylow p-subgroup vanishes for every prime p is zero. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The statement concerns ordinary cohomology in degree n ≥ 1 of a representation over any commutative ring k, and the restriction is Mathlib's groupCohomology.map along the inclusion of P with the identity on A.

### 125, `holomorphic_disc_ratio_growth`

The theorem is `GlobalTheory.T.holomorphic_disc_ratio_growth` in the module `Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowthStatement`. Its proof rests on 120 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc`.

Let Ω be a field of characteristic zero and A a finitely generated ℚ-subalgebra of Ω that is smooth over ℚ and such that every element of Ω is a fraction a/b with a, b ∈ A and b ≠ 0, so Ω is the fraction field of A. Let g, h, b ∈ A with h ≠ 0, b ≠ 0 and g/h ∉ A. Then there are a map ψ from ℂ to the set of ring homomorphisms A → ℂ and a real constant C such that z ↦ ψ(z)(a) is holomorphic on the open unit disc for every a ∈ A. Moreover, for every z ≠ 0 in that disc, ψ(z)(b) ≠ 0, ψ(z)(h) ≠ 0 and |ψ(z)(h)| ≤ C|z||ψ(z)(g)|.

```
A ⊆ Ω = Frac A f.g. smooth over ℚ, h, b ≠ 0, g/h ∉ A ⟹ ∃ holomorphic ψ: 𝔻 → (Spec A)(ℂ), ∃ C, ∀ z ∈ 𝔻∖{0}, b(ψ(z)) ≠ 0, h(ψ(z)) ≠ 0, |h(ψ(z))| ≤ C|z||g(ψ(z))|
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a holomorphic-disc witness that a rational function g/h which is not regular on a smooth affine ℚ-variety has a pole, in the spirit of the Riemann extension theorem.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a holomorphic disc that runs into the polar divisor of a rational function g/h which is not regular on a smooth affine ℚ-variety. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. Continuity of ψ at 0 and the bound force ψ(0)(h) = 0, so the disc is centred on the zero set of h where g/h has its pole, and theorem 137 proves the same conclusion for every Noetherian integrally closed finitely generated ℚ-domain, which covers this smooth case.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with Ω = ℚ(t), A = ℚ[t], g = b = 1 and h = t.

### 126, `invariant_isAlgebraic`

The theorem is `GlobalTheory.WeberSplit.invariant_isAlgebraic` in the module `Development.AbelianVarietyTheory.Proofs.HeightProofs.PrimesOneModNSplitCompletelyWeberField`. Its proof rests on 120 declarations, and the five theorems use it.

Let K be a subfield of ℂ of degree 2 over ℚ, and let L be a period pair, which is a basis ω₁, ω₂ of a lattice in ℂ, whose lattice is exactly the image of the ring of integers 𝓞_K. Then g₂³/(g₂³ − 27g₃²) is algebraic over ℚ, where g₂ and g₃ are the Weierstrass invariants of L. This quotient equals j/1728, so the statement says that the j-invariant of the lattice 𝓞_K is algebraic. The lattice hypothesis forces K to be imaginary quadratic.

```
K ⊆ ℂ, [K : ℚ] = 2, Λ_L = 𝓞_K ⟹ g₂(L)³/(g₂(L)³ − 27g₃(L)²) = j(𝓞_K)/1728 ∈ ℚ̄
```

The first reader gives it the kind named theorem and names the published result as follows. Algebraicity of singular moduli, the theorem of complex multiplication that the j-invariant of a lattice with complex multiplication by an order of an imaginary quadratic field is an algebraic integer. David A. Cox, Primes of the Form x² + ny², 1989, Theorem 11.1.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Algebraicity of singular moduli, the part of the theory of complex multiplication that says j(𝓞_K) is an algebraic integer for an imaginary quadratic field K. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The quotient equals j(𝓞_K)/1728 and is a genuine quotient because g₂³ − 27g₃² never vanishes for a lattice, and the statement covers only the lattice 𝓞_K itself, not other orders or ideal classes.

On emptiness the check wrote this. None found, because hL can be met for every imaginary quadratic field K and fails only for real quadratic K, where 𝓞_K lies in ℝ and is no lattice.

### 127, `isIso_of_isClosedImmersion`

The theorem is `GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension`. Its proof rests on 119 declarations, and the five theorems use it.

Let S, X, Y be schemes, let p: X → S be a morphism with geometrically connected fibres, and let f: Y → X be a closed immersion such that the composite p∘f: Y → S is surjective. Suppose that p is smooth of relative dimension g′ and that p∘f is smooth of relative dimension g with g′ ≤ g. Then f is an isomorphism.

```
f: Y ↪ X closed, p: X → S smooth of rel. dim g′ with geometrically connected fibres, p∘f surjective and smooth of rel. dim g ≥ g′ ⟹ f is an isomorphism
```

The first reader gives it the kind technical step and names the published result as follows. No published result known in this form, a fibrewise dimension criterion for a closed immersion of smooth S-schemes to be an isomorphism, of the kind used to show that a monomorphism of abelian schemes of equal dimension is an isomorphism.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a fibrewise dimension criterion for a closed immersion between smooth S-schemes to be an isomorphism. For the relation to that result the check has none, the first reader none and the second reader different.

The check adds this. The proof needs that each fibre X_s is irreducible, which holds because a smooth connected scheme over a field is irreducible, and that Y is flat over S, which lets the fibrewise isomorphism criterion of EGA IV 17.9.5 apply.

On emptiness the check wrote this. None found, although the hypotheses force g = g′, because a nonempty closed subscheme of the irreducible fibre X_s cannot have larger dimension than X_s.

### 128, `exists_dirichletLFunction_zero_gap_near_one`

The theorem is `GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one` in the module `Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOneStatement`. Its proof rests on 118 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ZeroGapNearOne.exists_gap`.

There is a constant c > 0 with the following property. For every modulus q ≥ 1, every complex Dirichlet character χ modulo q, and every complex zero ρ of the Dirichlet L-function L(s, χ) with |Im ρ| ≤ 1, one has 1 − Re ρ ≥ c/(q² log(3q)). The point ρ = 1 is excluded when χ is trivial.

```
∃ c > 0 ∀ q ≥ 1 ∀ χ mod q ∀ ρ ∈ ℂ, (χ ≠ 1 ∨ ρ ≠ 1), L(ρ, χ) = 0, |Im ρ| ≤ 1 ⟹ 1 − Re ρ ≥ c/(q² log 3q)
```

The first reader gives it the kind technical step and names the published result as follows. The classical zero-free region of de la Vallée Poussin for Dirichlet L-functions together with the effective bound 1 − β ≫ q^{−1/2}(log q)^{−2} for a possible exceptional real zero β. Harold Davenport, Multiplicative Number Theory, 2nd edition, 1980, Chapter 14.

The second reader gives it the kind named theorem and the check the kind technical step. The check names the published result as follows. The zero-free region of de la Vallée Poussin for Dirichlet L-functions together with the effective bound 1 − β ≫ q^{−1/2}(log q)^{−2} for a possible exceptional real zero. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The factor q² makes the bound much weaker than the classical bounds c/log(3q) for ordinary zeros and c/(q^{1/2} log² q) for an exceptional zero, and the trivial zeros and the zeros of imprimitive characters on Re s = 0 meet it at once.

### 129, `exists_isStandardSmoothOfRelativeDimension_of_localization`

The theorem is `GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_localization` in the module `Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe`. Its proof rests on 117 declarations, and the five theorems use it.

Let o be a Noetherian ring and V a discrete valuation ring that is the localization of o at a submonoid M, with perfect residue field k and fraction field K. Let A be a flat o-algebra of finite type, and let d be a natural number such that every irreducible component of the generic fibre K ⊗_o A has Krull dimension at least d. Let x be a maximal ideal of the special fibre k ⊗_o A whose cotangent space x/x² has dimension at most d over the residue field. Then some f ∈ A outside the preimage of x in A makes the localization A_f a standard smooth o-algebra of relative dimension d.

```
V = M⁻¹o DVR, k perfect, A flat f.t. over o, dim (K ⊗_o A)/𝔭 ≥ d ∀ minimal 𝔭, x ∈ Max(k ⊗_o A), dim_{κ(x)} x/x² ≤ d ⟹ ∃ f ∉ x ∩ A, A_f standard smooth of rel. dim d over o
```

The first reader gives it the kind technical step and names the published result as follows. The fibrewise criterion for smoothness of a flat morphism of finite presentation, applied at a closed point of the special fibre over a discrete valuation ring where that fibre is regular of the generic dimension and hence smooth over the perfect residue field. Alexander Grothendieck, Éléments de géométrie algébrique IV, quatrième partie, 1967, Théorème 17.5.1.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a smoothness criterion at a closed point of the special fibre of a flat finite-type algebra over a discrete valuation ring, obtained from the fibrewise criterion of EGA IV 17.5.1 and a tangent-space dimension count. For the relation to that result the check has none, the first reader weaker and the second reader different.

The check adds this. Because V is a localization of o, the fields K and ResidueField V are residue fields of points of Spec o, so K ⊗_o A and ResidueField V ⊗_o A are fibres of A over Spec o, and the conclusion asks for smoothness over o itself on a neighbourhood D(f) of the prime under x.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with o = ℤ, V = ℤ_(p), A = ℤ[t], d = 1 and x = (t) in 𝔽_p[t].

### 130, `exists_conductor_adicCompletion_essFiniteType`

The theorem is `GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType` in the module `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteTypeStatement`. Its proof rests on 117 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType`.

Let A be an integrally closed local domain of characteristic zero that is essentially of finite type over ℤ, and let Â be its completion with respect to the maximal ideal. Then there is a nonzero x ∈ A such that x·c lies in Â for every element c of the total ring of fractions of Â that is integral over Â. In other words, the conductor of Â in its integral closure contains a nonzero element of A.

```
A normal local domain, char 0, ess. f.t. over ℤ ⟹ ∃ x ∈ A∖{0} ∀ c ∈ Q(Â) integral over Â, x c ∈ Â
```

The first reader gives it the kind technical step and names the published result as follows. Zariski's theorem on analytic normality in Grothendieck's form, that the completion of an excellent normal local ring is normal, applied to a local ring essentially of finite type over ℤ, which is excellent. Alexander Grothendieck, Éléments de géométrie algébrique IV, seconde partie, 1965, Scholie 7.8.3.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Zariski's analytic normality theorem in Grothendieck's form, that the completion of an excellent normal local ring is normal, applied to a local ring essentially of finite type over ℤ. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The characteristic-zero hypothesis plays no role in the published theorem, because every local ring essentially of finite type over ℤ is excellent.

On emptiness the check wrote this. None found, although x = 1 meets the conclusion once one knows that Â is a normal domain, which is the deep content of the statement.

### 131, `exists_pow_eq_unit_of_continuous_complex_root`

The theorem is `GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root` in the module `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqUnitOfContinuousComplexRootStatement`. Its proof rests on 115 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root`.

Let B be a smooth ℂ-algebra that is a domain, let n > 0, let u be a unit of B, and let ρ be a complex-valued function on the ℂ-algebra homomorphisms B → ℂ, which are the complex points of X = Spec B. Suppose that p ↦ ρ(s(p)) is continuous on V for every open V ⊆ ℂ^m and every map s from ℂ^m to these points whose coordinates p ↦ s(p)(a) are holomorphic on V. Suppose also that ρ(ψ)^n = ψ(u) for every point ψ. Then there is b ∈ B with b^n = u.

```
B smooth ℂ-domain, n > 0, u ∈ B^×, ρ: X(ℂ) → ℂ continuous along holomorphic families, ρ^n = u on X(ℂ) ⟹ ∃ b ∈ B, b^n = u
```

The first reader gives it the kind technical step and names the published result as follows. The Riemann existence theorem in its fully faithful part, which makes continuous sections of the Kummer covering T^n = u over X(ℂ) algebraic, or equivalently the injectivity of B^×/(B^×)^n into H^1(X(ℂ), ℤ/n). Alexander Grothendieck, Revêtements étales et groupe fondamental (SGA 1), 1971, Exposé XII, Théorème 5.1.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. A consequence of the Riemann existence theorem (SGA 1, Exposé XII) for the Kummer covering T^n = u, which says that a continuous n-th root of a unit on a connected smooth complex affine variety is algebraic. For the relation to that result the check has weaker, the first reader weaker and the second reader none.

The check adds this. Continuity of ρ along holomorphic families is equivalent to ordinary continuity on the complex manifold X(ℂ), because the local charts of the smooth variety are holomorphic families, and the proof then needs that X(ℂ) is connected and that a continuous section of the finite étale covering T^n = u is algebraic.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with B = ℂ[t, t⁻¹], n = 2, u = t² and ρ(ψ) = ψ(t).

### 132, `isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective`

The theorem is `GlobalTheory.isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq`. Its proof rests on 113 declarations, and the five theorems use it.

Let V be a discrete valuation ring with perfect residue field and fraction field K, let A be a flat V-algebra of finite type, and let d be a natural number such that every irreducible component of K ⊗_V A has Krull dimension at least d. Let φ: A → B be a surjective ring homomorphism with kernel 𝔪_V A, so B is the special fibre, and let x be a maximal ideal of B whose cotangent space x/x² has dimension at most d over B/x. Then A is smooth over V at the prime φ⁻¹(x), and some f ∉ φ⁻¹(x) makes A_f a standard smooth V-algebra of relative dimension d. Moreover, the local ring B_x is regular of Krull dimension d, and x/x² has dimension exactly d.

```
A flat f.t. over V, dim (K ⊗ A)/𝔭 ≥ d ∀ minimal 𝔭, B = A/𝔪_V A, x ∈ Max B, dim x/x² ≤ d ⟹ A smooth at φ⁻¹x, ∃ f ∉ φ⁻¹x with A_f std. smooth of rel. dim d, B_x regular, dim B_x = dim x/x² = d
```

The first reader gives it the kind technical step and names the published result as follows. The fibrewise criterion for smoothness of a flat morphism of finite presentation, applied at a closed point of the special fibre over a discrete valuation ring where that fibre is regular of the generic dimension and hence smooth over the perfect residue field. Alexander Grothendieck, Éléments de géométrie algébrique IV, quatrième partie, 1967, Théorème 17.5.1.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a smoothness criterion at a closed point of the special fibre of a flat finite-type algebra over a discrete valuation ring, obtained from the fibrewise criterion of EGA IV 17.5.1 and a tangent-space dimension count. For the relation to that result the check has none, the first reader weaker and the second reader different.

The check adds this. The statement does not follow from the fibrewise criterion alone, since it also needs that flatness makes the special fibre at least d-dimensional at x and that a regular closed point over a perfect field is a smooth point, and theorem 135 is the same statement for an arbitrary local ring S that localizes B at x.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with V = ℤ_(p), A = V[t], B = 𝔽_p[t], d = 1 and x = (t).

### 133, `weierstrassP_halfPeriods_ne`

The theorem is `GroundTheory.Global.Elliptic.weierstrassP_halfPeriods_ne` in the module `GroundTheory.GlobalFields.ComplexMultiplication.Uniformization`. Its proof rests on 112 declarations, and the five theorems use it.

For every period pair L, which is a basis ω₁, ω₂ of a lattice in ℂ, the Weierstrass function ℘ of that lattice takes three pairwise different values at the half-periods ω₁/2, ω₂/2 and (ω₁ + ω₂)/2.

```
e₁ = ℘(ω₁/2), e₂ = ℘(ω₂/2), e₃ = ℘((ω₁ + ω₂)/2) ⟹ e₁ ≠ e₂, e₁ ≠ e₃, e₂ ≠ e₃
```

The first reader gives it the kind standard fact and names the published result as follows. Distinctness of the half-period values e₁, e₂, e₃ of the Weierstrass ℘-function. Lars V. Ahlfors, Complex Analysis, 3rd edition, 1979, Chapter 7, Section 3.3.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The distinctness of the half-period values e₁, e₂, e₃ of the Weierstrass ℘-function. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. This statement is the first three conjuncts of theorem 136, and the half-periods are not lattice points, so Mathlib's value of ℘ at its poles plays no role.

### 134, `exists_complete_normal`

The theorem is `PositivityTheory.Xgn.TightHopfOrder.exists_complete_normal` in the module `Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SplitMultiplicativeHopfOrder`. Its proof rests on 112 declarations, and the five theorems use it.

Let V be an integrally closed local domain of characteristic zero, and let p be a prime number that lies in the maximal ideal of V. Assume that V is p-adically complete and Hausdorff and that every element of the maximal ideal has a power in pV. Let R₀ be a Noetherian ring with a ring homomorphism f: R₀ → V, and let s be a finite subset of V. Then there are a Noetherian integrally closed local domain D that is complete for its maximal ideal, a ring homomorphism g: R₀ → D, and an injective local homomorphism h: D → V such that h∘g = f and s lies in the image of h.

```
V normal local domain, char 0, p ∈ 𝔪_V, V p-adically complete, 𝔪_V ⊆ √(pV), f: R₀ → V, R₀ Noetherian, s ⊆ V finite ⟹ ∃ complete Noetherian normal local domain D, g: R₀ → D, local injective h: D → V, h∘g = f, s ⊆ h(D)
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, an approximation statement that exhausts a p-adically complete normal local domain by complete Noetherian normal local subrings containing a given Noetherian image.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, an approximation of a p-adically complete normal local domain by complete Noetherian normal local subrings that contain a given Noetherian image and a given finite set. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. A proof can complete a localization of a finitely generated R₀-algebra that maps onto s, take its image in V and normalize it, and the normalization stays finite by Nagata's theorem on complete local domains and stays inside V because V is integrally closed.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with V = ℤ_p and R₀ = ℤ.

### 135, `isSmoothAt_of_flat_of_finrank_cotangentSpace_le`

The theorem is `GlobalTheory.isSmoothAt_of_flat_of_finrank_cotangentSpace_le` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq`. Its proof rests on 111 declarations, and the five theorems use it.

Let V be a discrete valuation ring with perfect residue field and fraction field K, and let A be a flat V-algebra of finite type whose generic fibre K ⊗_V A has all irreducible components of Krull dimension at least d. Let φ: A → B be a surjection with kernel 𝔪_V A, let x be a maximal ideal of B, and let S be a local ring that is a localization of B at x. Suppose that the cotangent space 𝔪_S/𝔪_S² has dimension at most d over the residue field of S. Then A is smooth over V at φ⁻¹(x), some f ∉ φ⁻¹(x) makes A_f standard smooth of relative dimension d over V, S is a regular local ring of Krull dimension d, and the cotangent space of S has dimension exactly d.

```
A flat f.t. over V, dim (K ⊗ A)/𝔭 ≥ d ∀ minimal 𝔭, B = A/𝔪_V A, S = B_x, dim 𝔪_S/𝔪_S² ≤ d ⟹ A smooth at φ⁻¹x, ∃ f ∉ φ⁻¹x with A_f std. smooth of rel. dim d, S regular, dim S = dim 𝔪_S/𝔪_S² = d
```

The first reader gives it the kind technical step and names the published result as follows. The fibrewise criterion for smoothness of a flat morphism of finite presentation, applied at a closed point of the special fibre over a discrete valuation ring where that fibre is regular of the generic dimension and hence smooth over the perfect residue field. Alexander Grothendieck, Éléments de géométrie algébrique IV, quatrième partie, 1967, Théorème 17.5.1.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a smoothness criterion at a closed point of the special fibre of a flat finite-type algebra over a discrete valuation ring, obtained from the fibrewise criterion of EGA IV 17.5.1 and a tangent-space dimension count. For the relation to that result the check has none, the first reader weaker and the second reader different.

The check adds this. This is theorem 132 with the localization B_x replaced by any local ring S that is a localization of B at x, so the cotangent space of S takes the place of x/x².

On emptiness the check wrote this. None found, since the hypotheses hold for instance with V = ℤ_(p), A = V[t], B = 𝔽_p[t], d = 1, x = (t) and S the localization of 𝔽_p[t] at (t).

### 136, `halfPeriod_facts`

The theorem is `GroundTheory.Global.Elliptic.halfPeriod_facts` in the module `GroundTheory.GlobalFields.ComplexMultiplication.Uniformization`. Its proof rests on 111 declarations, and the five theorems use it.

Let L be a period pair, and let e₁ = ℘(ω₁/2), e₂ = ℘(ω₂/2) and e₃ = ℘((ω₁ + ω₂)/2) be the values of its Weierstrass function at the half-periods. Then the three values are pairwise different, e₁ + e₂ + e₃ = 0, 4(e₁² + e₁e₂ + e₂²) = g₂, and g₃ = 4e₁³ − g₂e₁, where g₂ and g₃ are the Weierstrass invariants of the lattice.

```
e₁, e₂, e₃ pairwise distinct, e₁ + e₂ + e₃ = 0, 4(e₁² + e₁e₂ + e₂²) = g₂, g₃ = 4e₁³ − g₂e₁
```

The first reader gives it the kind standard fact and names the published result as follows. The factorization 4x³ − g₂x − g₃ = 4(x − e₁)(x − e₂)(x − e₃) with distinct roots at the half-period values. Lars V. Ahlfors, Complex Analysis, 3rd edition, 1979, Chapter 7, Section 3.3.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The factorization 4x³ − g₂x − g₃ = 4(x − e₁)(x − e₂)(x − e₃) with distinct roots at the half-period values of ℘. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The three relations e₁ + e₂ + e₃ = 0, 4(e₁² + e₁e₂ + e₂²) = g₂ and g₃ = 4e₁³ − g₂e₁ are together equivalent to the factorization, and the first three conjuncts repeat theorem 133.

### 137, `disc_of_pole`

The theorem is `GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.disc_of_pole` in the module `Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowth`. Its proof rests on 110 declarations, and the five theorems use it.

Let R be a Noetherian integrally closed domain that is a finitely generated ℚ-algebra, with fraction field K, and let g, h, b ∈ R with h ≠ 0, b ≠ 0 and g/h ∉ R. Then there are a map ψ from ℂ to the set of ring homomorphisms R → ℂ and a real constant C such that z ↦ ψ(z)(a) is holomorphic on the open unit disc for every a ∈ R. Moreover, for every z ≠ 0 in that disc, ψ(z)(b) ≠ 0, ψ(z)(h) ≠ 0 and |ψ(z)(h)| ≤ C|z||ψ(z)(g)|.

```
R normal f.g. ℚ-domain, h, b ≠ 0, g/h ∉ R ⟹ ∃ holomorphic ψ: 𝔻 → (Spec R)(ℂ), ∃ C, ∀ z ∈ 𝔻∖{0}, b(ψ(z)) ≠ 0, h(ψ(z)) ≠ 0, |h(ψ(z))| ≤ C|z||g(ψ(z))|
```

The first reader gives it the kind technical step and names the published result as follows. No published result known, a holomorphic-disc witness that a rational function which is not regular on a normal affine ℚ-variety has a pole, in the spirit of the Riemann extension theorem on normal complex spaces.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known, a holomorphic disc that runs into the polar divisor of a rational function g/h which is not regular on a normal affine ℚ-variety. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. Theorem 125 is the special case in which the ring is smooth over ℚ and sits in its fraction field, because a smooth finitely generated ℚ-domain is Noetherian and integrally closed.

On emptiness the check wrote this. None found, since the hypotheses hold for instance with R = ℚ[t], g = b = 1 and h = t.

### 138, `exists_entire_sub_one_mul_euler_exp_ne_zero_one`

The theorem is `GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one` in the module `Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZeroStatement`. Its proof rests on 110 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero`.

For every number field K there is an entire function Z: ℂ → ℂ with Z(1) ≠ 0 such that Z(s) = (s − 1)·exp(Σ_P −log(1 − N(P)^{−s})) for Re s > 1, where the sum runs over the nonzero prime ideals P of the ring of integers 𝓞_K. For Re s > 1 the exponential equals the Euler product ∏_P (1 − N(P)^{−s})^{−1} = ζ_K(s). The statement therefore says that (s − 1)ζ_K(s) extends to an entire function that does not vanish at s = 1.

```
∀ K number field ∃ Z entire, Z(1) ≠ 0, Z(s) = (s − 1) ∏_𝔭 (1 − N𝔭^{−s})^{−1} = (s − 1) ζ_K(s) for Re s > 1
```

The first reader gives it the kind named theorem and names the published result as follows. Hecke's theorem that the Dedekind zeta function continues meromorphically to ℂ with a single simple pole at s = 1, whose residue is nonzero by the analytic class number formula. Jürgen Neukirch, Algebraic Number Theory, 1999, Chapter VII, Corollary 5.11.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Hecke's theorem that the Dedekind zeta function continues meromorphically to ℂ with a single simple pole at s = 1. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. For Re s > 1 the exponential of the sum of −log(1 − N(P)^{−s}) equals the Euler product of ζ_K(s), the factor 1 in front of N(P)^{−s} changes nothing, and the statement leaves out the functional equation and the value of the residue.

### 139, `differentiable_discr_cpow_mul_gamma_inv`

The theorem is `GroundTheory.Global.differentiable_discr_cpow_mul_gamma_inv` in the module `GroundTheory.GlobalFields.TateThesis.DedekindContinuation`. Its proof rests on 110 declarations, and the five theorems use it.

Let K be a number field with discriminant d_K, r₁ real places and r₂ complex places. Then the function s ↦ |d_K|^{−s/2}·(Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂})^{−1} is complex differentiable on all of ℂ, where Γ_ℝ(s) = π^{−s/2}Γ(s/2) and Γ_ℂ(s) = 2(2π)^{−s}Γ(s). Mathlib sets Γ equal to 0 at its poles and inverts 0 to 0, so the expression agrees at every point with the entire function |d_K|^{−s/2}/(Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}).

```
s ↦ |d_K|^{−s/2} (Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂})^{−1} is entire
```

The first reader gives it the kind technical step and names the published result as follows. The fact that the reciprocal Gamma function 1/Γ is entire, applied to the archimedean factor of the completed Dedekind zeta function. Lars V. Ahlfors, Complex Analysis, 3rd edition, 1979, Chapter 5, Section 2.4.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The entireness of the reciprocal Gamma function 1/Γ, applied to the archimedean factor of the completed Dedekind zeta function. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Mathlib gives Γ the value 0 at its poles and inverts 0 to 0, so the Lean expression agrees at every point with the entire function |d_K|^{−s/2}/(Γ_ℝ(s)^{r₁}Γ_ℂ(s)^{r₂}).

On emptiness the check wrote this. None found, although the conclusion follows quickly from the entireness of 1/Γ and of s ↦ |d_K|^{−s/2}.

### 140, `formalFibre_isRegularRing_essFiniteType_int`

The theorem is `GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeIntStatement`. Its proof rests on 109 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.formalFibre_isRegularRing_of_essFiniteType_int`.

Let R be a local ring essentially of finite type over ℤ, with maximal ideal 𝔪 and 𝔪-adic completion R̂, and let K be a field that is an R-algebra essentially of finite type over R. Then the ring R̂ ⊗_R K is regular. Let 𝔮 be the kernel of R → K. Then K is a finitely generated field extension of κ(𝔮) and R̂ ⊗_R K = (R̂ ⊗_R κ(𝔮)) ⊗_{κ(𝔮)} K, so the statement says that the formal fibres of R are geometrically regular.

```
R local ess. f.t. over ℤ, K field ess. f.t. over R ⟹ R̂ ⊗_R K is regular
```

The first reader gives it the kind standard fact and names the published result as follows. Grothendieck's theorem that rings essentially of finite type over ℤ are excellent, in its part that the formal fibres of such a local ring are geometrically regular. Alexander Grothendieck, Éléments de géométrie algébrique IV, seconde partie, 1965, Scholie 7.8.3.

The second reader gives it the kind named theorem and the check the kind standard fact. The check names the published result as follows. The excellence of rings essentially of finite type over ℤ (EGA IV 7.8.3), in its part that the formal fibres of such a local ring are geometrically regular. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. Because each such K is a finitely generated field extension of the residue field at the kernel of R → K, regularity of R̂ ⊗_R K for all such K is equivalent to geometric regularity of the formal fibres of R, which is the G-ring part of excellence.

### 141, `exists_zero_fderiv_ne_zero`

The theorem is `GlobalTheory.ThetaGauss.exists_zero_fderiv_ne_zero` in the module `Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableFderivApply`. Its proof rests on 109 declarations, and the five theorems use it.

For every natural number g, every positive definite Hermitian matrix H in M_g(ℂ) and every discrete additive subgroup Λ of ℂ^g such that a vector v lies in Λ exactly when Im(v*Ha) is an integer for every a in Λ, the following holds for all functions χ and θ from ℂ^g to ℂ. If θ is holomorphic and not identically zero, |χ(a)| = 1 for every a in Λ, and θ(z + a) = χ(a)·exp(π·a*Hz + (π/2)·a*Ha)·θ(z) for every a in Λ and every z, then every nonzero vector v has a point a with θ(a) = 0 and dθ(a)(v) ≠ 0. The self-duality condition makes Λ a full lattice on which E = Im H is integral and unimodular, so θ is a theta function of a principal polarization on the torus ℂ^g/Λ. The conclusion says that no nonzero direction is tangent to the zero set of θ at every one of its zeros.

```
∀g ∀H ≻ 0 ∀Λ ≤ ℂ^g discrete with Λ = {v | Im(v*Ha) ∈ ℤ ∀a ∈ Λ}, ∀χ ∀θ entire, θ ≠ 0, |χ| = 1 on Λ, θ(z+a) = χ(a)e^{π a*Hz + (π/2) a*Ha}θ(z) ⟹ ∀v ≠ 0 ∃a, θ(a) = 0 ∧ dθ(a)v ≠ 0
```

The first reader gives it the kind standard fact and names the published result as follows. Nondegeneracy of the Gauss map of the theta divisor of a principally polarized abelian variety. The tangent hyperplanes of a reduced ample divisor at its smooth points have no nonzero vector in common, and this is applied here to the reduced theta divisor. Christina Birkenhake and Herbert Lange, Complex Abelian Varieties, 2nd edition, 2004 (Section 4.4 on the Gauss map).

The second reader gives it the kind technical step and the check the kind standard fact. The check names the published result as follows. Nondegeneracy of the Gauss map of the theta divisor of a principally polarized abelian variety, which says that the tangent hyperplanes of the reduced theta divisor at its smooth points have no nonzero direction in common (Birkenhake and Lange, Complex Abelian Varieties, Section 4.4 on the Gauss map). For the relation to that result the check has special case, the first reader special case and the second reader weaker.

The check adds this. The self-duality of Λ under Im H forces Λ to be a full lattice carrying a principal polarization, and the proof needs the reducedness of the theta divisor in addition to the ampleness of the polarization, since a zero of order two or more has a vanishing derivative in every direction.

On emptiness the check wrote this. The case g = 0 holds vacuously because ℂ^0 has no nonzero vector, and for every g ≥ 1 the Riemann theta function of a principal polarization meets all hypotheses, so no other emptiness was found.

### 142, `isReduced_coordinateRing`

The theorem is `GlobalTheory.WeierstrassCurve.isReduced_coordinateRing` in the module `Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian`. Its proof rests on 109 declarations, and the five theorems use it.

For every reduced commutative ring R and every Weierstrass curve W over R, the affine coordinate ring R[X, Y]/(Y² + a₁XY + a₃Y − X³ − a₂X² − a₄X − a₆) is a reduced ring. The declaration is an instance. Its displayed proof gets reducedness from two facts, that the coordinate ring is geometrically reduced over R, checked through pullback squares over every field, and that it is free as an R-module.

```
R reduced ⟹ R[X,Y]/(Y² + a₁XY + a₃Y − X³ − a₂X² − a₄X − a₆) reduced
```

The first reader gives it the kind standard fact and names the published result as follows. No published result known. It is a reducedness property of the coordinate ring of an affine Weierstrass curve over an arbitrary reduced base ring.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. No published result known. It is the reducedness of the affine coordinate ring of an arbitrary Weierstrass curve over a reduced base ring, which follows from the freeness of that ring over the base and the integrality of the Weierstrass cubic over every field. For the relation to that result the check has none, the first reader none and the second reader special case.

The check adds this. The instance needs no condition on the discriminant, so it covers singular Weierstrass curves too, and the proof shown in the dossier goes through geometric reducedness over every field and freeness over R.

### 143, `sub_mem_or_add_mem_of_weierstrassP_eq`

The theorem is `GroundTheory.Global.Elliptic.sub_mem_or_add_mem_of_weierstrassP_eq` in the module `GroundTheory.GlobalFields.ComplexMultiplication.Uniformization`. Its proof rests on 109 declarations, and the five theorems use it.

Let L be the lattice spanned by a pair of ℝ-linearly independent complex periods, and let ℘ be its Weierstrass function. For complex numbers z and w that both lie outside the lattice, ℘(z) = ℘(w) implies that z − w or z + w lies in the lattice.

```
z, w ∉ L, ℘_L(z) = ℘_L(w) ⟹ z − w ∈ L ∨ z + w ∈ L
```

The first reader gives it the kind standard fact and names the published result as follows. The Weierstrass ℘-function is an even elliptic function of order 2, so ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo the lattice. Joseph H. Silverman, The Arithmetic of Elliptic Curves, 2nd edition, 2009 (Chapter VI).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. One direction of the description of the fibres of the Weierstrass function, which says that ℘(z) = ℘(w) holds exactly when z ≡ ±w modulo the lattice because ℘ is an even elliptic function of order 2. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The converse direction, that z ≡ ±w modulo the lattice gives ℘(z) = ℘(w), follows from evenness and periodicity and is not part of the statement.

### 144, `two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero`

The theorem is `GroundTheory.Global.Elliptic.two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero` in the module `GroundTheory.GlobalFields.ComplexMultiplication.Uniformization`. Its proof rests on 109 declarations, and the five theorems use it.

Let L be a period lattice and w a complex number outside L. Then 2w lies in L if and only if the derivative ℘′ of the Weierstrass function of L vanishes at w.

```
w ∉ L ⟹ (2w ∈ L ⟺ ℘′_L(w) = 0)
```

The first reader gives it the kind standard fact and names the published result as follows. The zeros of ℘′ are exactly the three nonzero half-periods modulo the lattice. Joseph H. Silverman, The Arithmetic of Elliptic Curves, 2nd edition, 2009 (Chapter VI).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The zeros of ℘′ are exactly the three nonzero half-periods modulo the lattice. For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The point w has to lie outside the lattice because ℘′ has its poles at the lattice points, where 2w ∈ L holds trivially.

### 145, `isPreconnected_points_over`

The theorem is `GlobalTheory.GeomConn.isPreconnected_points_over` in the module `Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure`. Its proof rests on 108 declarations, and the five theorems use it.

Let K be a field of characteristic zero, A a finitely generated commutative K-algebra, and Ω a field over K in which every element algebraic over K already lies in K. Let j be an injective K-algebra map from A to Ω and σ a ring embedding of K into ℂ. Then the set of ring homomorphisms ρ from A to ℂ with ρ restricted to K equal to σ is preconnected, viewed as a set of functions from A to ℂ with the product topology. Geometrically, Spec A is a geometrically integral affine K-variety, and the claim is that the complex points of its base change along σ form a connected space in the classical topology.

```
{ρ ∈ Hom_ring(A, ℂ) | ρ ∘ (K → A) = σ} ⊆ ℂ^A is preconnected
```

The first reader gives it the kind named theorem and names the published result as follows. An irreducible complex algebraic variety is connected in the classical topology. Igor R. Shafarevich, Basic Algebraic Geometry 2, 2nd edition, 1994 (Chapter VII, Section 2).

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Connectedness of an irreducible complex algebraic variety in the classical topology (Shafarevich, Basic Algebraic Geometry 2, Chapter VII, Section 2), applied to the base change along σ of a geometrically integral affine variety over K. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The product topology on functions from A to ℂ agrees on this set with the classical topology of the complex points, because a homomorphism is determined by its values on finitely many generators of A.

### 146, `isZero_tateCohomology_of_index`

The theorem is `GroundTheory.GroupCoh.isZero_tateCohomology_of_index` in the module `GroundTheory.TateCohomology.CohTrivial`. Its proof rests on 107 declarations, and the five theorems use it.

Let k be a commutative ring, G a finite group, A a k-linear representation of G, and n an integer. Suppose that for every prime p dividing the order of G there is a subgroup P of G whose index is prime to p and for which the n-th Tate cohomology of P with coefficients in the restriction of A is zero. Then the n-th Tate cohomology of G with coefficients in A is zero.

```
(∀p prime, p | #G ⟹ ∃P ≤ G, p ∤ [G : P] ∧ Ĥⁿ(P, Res A) = 0) ⟹ Ĥⁿ(G, A) = 0
```

The first reader gives it the kind standard fact and names the published result as follows. The Sylow criterion for the vanishing of Tate cohomology. It rests on the fact that restriction to a subgroup of index prime to p is injective on the p-primary component. Michael F. Atiyah and C. T. C. Wall, Cohomology of Groups, in J. W. S. Cassels and A. Fröhlich (eds.), Algebraic Number Theory, 1967.

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The Sylow criterion for the vanishing of Tate cohomology, which rests on restriction followed by corestriction being multiplication by the index (Atiyah and Wall in Cassels and Fröhlich, Algebraic Number Theory, Chapter IV), here with any subgroup of index prime to p in place of a Sylow p-subgroup. For the relation to that result the check has stronger, the first reader stronger and the second reader stronger.

The check adds this. The vanishing is assumed only in the single degree n and only for one subgroup per prime, and a Sylow p-subgroup is one admissible choice among the subgroups of index prime to p.

### 147, `isRegularRing_formalFibre_of_essFiniteType`

The theorem is `GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingOfEssFiniteTypeStatement`. Its proof rests on 106 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.formalFibre_isRegularRing_of_essFiniteType`.

Let Λ be a regular integral domain whose fraction field is perfect, R a local ring that is essentially of finite type over Λ, and K a field that is essentially of finite type over R, with the composite map from Λ to K injective. Then R̂ ⊗_R K is a regular ring, where R̂ is the completion of R at its maximal ideal. Write 𝔭 for the kernel of R → K, a prime lying over the generic point of Spec Λ. The claim is that the formal fibre of R at 𝔭 stays regular after base change to the finitely generated field extension K of κ(𝔭).

```
Λ regular domain, Frac Λ perfect, R local ess. f.t. over Λ, K field ess. f.t. over R, Λ ↪ K ⟹ R̂_𝔪 ⊗_R K regular
```

The first reader gives it the kind technical step and names the published result as follows. No published result known. It is a regularity statement for formal fibres lying over the generic point of a regular base, of the kind that excellence of the base would supply.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known. It is a regularity statement for the formal fibres of a local ring essentially of finite type over a regular domain at primes over the generic point of that domain, related to Grothendieck's theorem that rings essentially of finite type over an excellent ring have geometrically regular formal fibres (EGA IV 7.8.3). For the relation to that result the check has none, the first reader none and the second reader different.

The check adds this. Excellence of Λ is not assumed, and the claim is confined to fibres over the generic point of Λ, where the generic formal fibre of a regular local ring is a localization of its regular completion and the perfect fraction field keeps that regularity under the finitely generated field extension.

On emptiness the check wrote this. None found, although in positive characteristic a regular domain with perfect fraction field is itself a perfect field, so the hypothesis has real content only when the fraction field has characteristic zero.

### 148, `dedekindZeta_eulerProduct_mul_sub_one_entire`

The theorem is `GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire`. Its proof rests on 106 declarations, and the five theorems use it.

For every number field K there is an entire function Z with the following property. For every complex s with real part greater than 1, Z(s) equals (s − 1) times the exponential of the sum, over the nonzero prime ideals P of the ring of integers, of −log(1 − 1·N(P)^{−s}). That exponential is the Euler product of the Dedekind zeta function, so the statement says that (s − 1)ζ_K(s) extends from the half-plane Re s > 1 to an entire function.

```
∃Z entire, ∀s with Re s > 1, Z(s) = (s − 1)·exp(∑_P −log(1 − 1·N(P)^{−s})) = (s − 1)ζ_K(s)
```

The first reader gives it the kind named theorem and names the published result as follows. Hecke's theorem on the continuation of the Dedekind zeta function to the whole plane with at most a simple pole at s = 1. Erich Hecke, Über die Zetafunktion beliebiger algebraischer Zahlkörper, 1917.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Hecke's theorem on the analytic continuation of the Dedekind zeta function to a meromorphic function on ℂ whose only pole is a simple pole at s = 1. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The statement does not say that Z(1) is nonzero, so neither the existence of the pole nor its residue from the class number formula is part of it, and the functional equation is left out as well.

### 149, `function_field_class_group_powers`

The theorem is `GlobalTheory.T.function_field_class_group_powers` in the module `Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowersStatement`. Its proof rests on 105 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.exists_class_group_mk0_eq_mul_pow`.

Let k be an algebraically closed field of characteristic zero, and let A be a Dedekind domain that is an algebra over k and over k[X], compatibly, and is finite and free as a k[X]-module. Take an integer N ≥ 2 and a nonzero maximal ideal P₀ of A. Then there is a nonzero element a of A such that the class of every nonzero maximal ideal P not containing a equals the class of P₀ times an N-th power in the class group of A.

```
∀N ≥ 2 ∀P₀ maximal ∃a ≠ 0 ∀P maximal with a ∉ P ∃d ∈ Cl(A), [P] = [P₀]·d^N
```

The first reader gives it the kind technical step and names the published result as follows. Divisibility of the divisor class group of a smooth affine curve over an algebraically closed field, which follows from the divisibility of the group of points of its Jacobian. David Mumford, Abelian Varieties, 1970.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. Divisibility of the ideal class group of a smooth affine curve over an algebraically closed field, a quotient of the divisible group of points of the Jacobian of the complete curve. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The hypothesis of characteristic zero is not needed, since the group of points of an abelian variety over an algebraically closed field is divisible in every characteristic.

On emptiness the check wrote this. No hypothesis is impossible, but a = 1 already meets the existential claim because the class group is divisible, so the condition that P avoids a does no work.

### 150, `exists_basis_unique_min_and_sums_separated`

The theorem is `GlobalTheory.exists_basis_unique_min_and_sums_separated` in the module `Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinAndSumsSeparated`. Its proof rests on 105 declarations, and the five theorems use it.

Let X be a free abelian group of finite rank d and q a real-valued quadratic map on X that tends to infinity along the cofinite filter, which makes q positive definite. Let g, N, N′ and D be natural numbers with d ≤ g, 1 + 2g·2^{g/2} < N and 2D·(g·(3/2)^g·2^{g/2−1})·N < N′. Then X has a basis e₁,…,e_d such that each e_i and each −e_i is the unique strict minimizer of q in its coset modulo NX. In addition, for every k ≤ D and all families α₁,…,α_k and β₁,…,β_k whose members minimize q in their cosets modulo NX, an equation ∑α_j = ∑β_j + N′w forces w = 0.

```
∃ basis e, ∀i ∀μ ≠ 0, q(±e_i) < q(±e_i + Nμ), and ∀k ≤ D ∀α, β ∈ X^k with q(α_j) ≤ q(α_j + Nw), q(β_j) ≤ q(β_j + Nw) ∀j ∀w, ∑α_j = ∑β_j + N′w ⟹ w = 0
```

The first reader gives it the kind technical step and names the published result as follows. No published result known. It is a lattice reduction lemma with explicit constants that separates the coset minimizers of a positive definite quadratic form.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known. It is a lattice reduction lemma with explicit constants that makes basis vectors unique coset minimizers of a positive definite quadratic form and separates sums of coset minimizers. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The sum clause does not involve the basis and follows in a few lines from the bound |polar q (α_j) w| ≤ N·q(w) that every coset minimizer satisfies, which gives w = 0 as soon as N′ > D·N, far below the stated bound on N′.

On emptiness the check wrote this. None found, although the clause on −e_i repeats the clause on e_i because q(−x) = q(x).

### 151, `exists_basis_unique_min_pair_sums`

The theorem is `GlobalTheory.exists_basis_unique_min_pair_sums` in the module `Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinPairSums`. Its proof rests on 104 declarations, and the five theorems use it.

Let X be a free abelian group of finite rank d and q a real-valued quadratic map on X that tends to infinity along the cofinite filter. If d ≤ g and 1 + 4g·2^{g/2} < N, then X has a basis e₁,…,e_d such that q(e_i) < q(e_i + Nμ) and q(e_i + e_j) < q(e_i + e_j + Nμ) for all indices i and j and every nonzero μ in X. So each basis vector and each sum of two basis vectors, 2e_i included, is the unique strict minimizer of q in its coset modulo NX.

```
d ≤ g, 1 + 4g·2^{g/2} < N ⟹ ∃ basis e, ∀i, j ∀μ ≠ 0, q(e_i) < q(e_i + Nμ) ∧ q(e_i + e_j) < q(e_i + e_j + Nμ)
```

The first reader gives it the kind technical step and names the published result as follows. No published result known. It is a lattice reduction lemma with explicit constants that makes basis vectors and their pairwise sums unique coset minimizers of a positive definite quadratic form.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known. It is a lattice reduction lemma with explicit constants that makes basis vectors and their pairwise sums unique coset minimizers of a positive definite quadratic form. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. Positive definiteness of q is not stated as a hypothesis but follows from the condition that q tends to infinity along the cofinite filter.

### 152, `adic_completion_reduced_of_jacobson`

The theorem is `GlobalTheory.T.adic_completion_reduced_of_jacobson` in the module `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionReducedOfJacobsonStatement`. Its proof rests on 103 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.CompletionReduced.isReduced_adicCompletion`.

Let D be an integral domain that is essentially of finite type over ℤ, and let J be an ideal of D contained in the Jacobson radical of D. Then the J-adic completion of D is a reduced ring.

```
D domain ess. f.t. over ℤ, J ⊆ Jac(D) ⟹ lim_n D/Jⁿ is reduced
```

The first reader gives it the kind standard fact and names the published result as follows. The completion of a reduced excellent ring is reduced. Here it is applied to domains essentially of finite type over ℤ, which are excellent. Alexander Grothendieck and Jean Dieudonné, Éléments de géométrie algébrique IV, seconde partie, 1965 (Scholie 7.8.3).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Reducedness of the completion of a reduced excellent ring (EGA IV, Scholie 7.8.3, and Matsumura, Commutative Ring Theory, Section 32), applied to domains essentially of finite type over ℤ, which are excellent. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The condition that J lies in the Jacobson radical makes the completion map faithfully flat, so the reducedness comes from the regularity of the completion map of an excellent ring.

On emptiness the check wrote this. None found, although for a domain of finite type over ℤ the Jacobson radical is zero, so J = 0 and the completion is D itself, and the content lies in localizations such as ℤ localized at (p).

### 153, `schwartzSubmodule_eq_top_of_gaussian_mem_derivStable`

The theorem is `GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable` in the module `Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStableStatement`. Its proof rests on 103 declarations, and the five theorems use it. Lean found the same statement in 1 other theorem, `GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem`.

Let V be a finite-dimensional real normed space, N a complex linear subspace of the Schwartz space S(V, ℂ), and Q a continuous real-bilinear complex-valued form on V with c‖x‖² ≤ Re Q(x, x) for some c > 0. Suppose that N contains the Schwartz function g(x) = exp(−Q(x, x)), contains the directional derivative of each of its members in each direction v, and contains ℓ(x)f(x) for each of its members f and each real linear functional ℓ. Then N is dense in the Schwartz space.

```
e^{−Q(x,x)} ∈ N, ∂_v N ⊆ N, ℓ·N ⊆ N ⟹ closure(N) = S(V, ℂ)
```

The first reader gives it the kind technical step and names the published result as follows. Density of the Hermite functions, the polynomial multiples of a Gaussian, in the Schwartz space. Michael Reed and Barry Simon, Methods of Modern Mathematical Physics I. Functional Analysis, revised edition, 1980 (Section V.3).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. Density of the Hermite functions, the polynomial multiples of a Gaussian, in the Schwartz space, here with a complex Gaussian whose real part is positive definite. For the relation to that result the check has stronger, the first reader stronger and the second reader stronger.

The check adds this. The hypothesis of closure under directional derivatives is superfluous, because closure under multiplication by linear functionals already puts every polynomial multiple of the Gaussian into N, and these multiples are dense also for a complex Gaussian with positive definite real part.

### 154, `idealCharacter_LSeries_continuation`

The theorem is `GlobalTheory.idealCharacter_LSeries_continuation` in the module `Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation`. Its proof rests on 103 declarations, and the five theorems use it.

Let K be a number field and 𝔪 a nonzero ideal of its ring of integers. Let X be a multiplicative function on ideals that vanishes on the zero ideal and on every ideal not coprime to 𝔪 and has modulus 1 on every nonzero ideal coprime to 𝔪. Let φ be a multiplicative function on the mixed space ℝ^{r₁} × ℂ^{r₂} that is invariant under positive real scaling and is smooth and of modulus 1 where the norm is nonzero, and assume X((β)) = φ(β) for every nonzero integer β with β − 1 in 𝔪. Then there is an entire function Z with Z(s) = (s − 1)∑_I X(I)N(I)^{−s} for Re s > 1, and Z(1) = 0 whenever X takes a value other than 1 on some nonzero ideal coprime to 𝔪.

```
X unitary Hecke character mod 𝔪 with infinity type φ ⟹ ∃Z entire, Z(s) = (s − 1)L(s, X) for Re s > 1, and (∃J ≠ 0, J + 𝔪 = 𝒪_K, X(J) ≠ 1) ⟹ Z(1) = 0
```

The first reader gives it the kind named theorem and names the published result as follows. Hecke's theorem on the analytic continuation of L-functions of Hecke characters (Größencharaktere), which are entire for nontrivial characters. Erich Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen (Zweite Mitteilung), 1920.

The second reader gives it the kind named theorem and the check the kind named theorem. The check names the published result as follows. Hecke's theorem on the analytic continuation of the L-functions of Hecke characters (Größencharaktere), which are entire for a nontrivial character and have at most a simple pole at s = 1 for the trivial one. For the relation to that result the check has weaker, the first reader weaker and the second reader weaker.

The check adds this. The scaling invariance of φ excludes the twists by N(I)^{it}, whose L-series has its pole at 1 + it, and the functional equation is not part of the statement.

### 155, `index_range_powMonoidHom_adicCompletion_mul_norm`

The theorem is `GroundTheory.Global.index_range_powMonoidHom_adicCompletion_mul_norm` in the module `GroundTheory.GlobalFields.ExistenceTheorem.IndexRangePowMonoidHomAdicCompletionMulNorm`. Its proof rests on 103 declarations, and the five theorems use it.

Let K be a number field and n a positive integer such that K contains a primitive n-th root of unity, and let v be a finite place of K with completion K_v. Then the index of the subgroup of n-th powers in K_v^×, times the norm of n in K_v, equals n². The norm on K_v has to be the normalized absolute value for this equation to hold.

```
[K_v^× : (K_v^×)^n]·|n|_v = n²
```

The first reader gives it the kind standard fact and names the published result as follows. The index formula for n-th powers in a p-adic field, [F^× : F^{×n}] = n·#μ_n(F)/|n|_F, in the case where the n-th roots of unity lie in the field. Jürgen Neukirch, Algebraic Number Theory, 1999 (Chapter II, Section 5).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The index formula for n-th powers in a nonarchimedean local field F, which says that the index of F^{×n} in F^× is n·#μ_n(F)/|n|_F (Neukirch, Algebraic Number Theory, Chapter II, Section 5), in the case where the n-th roots of unity lie in K. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. Because the formula is proved, the norm that Mathlib puts on the completion must be the normalized absolute value, for which the norm of n is the absolute norm of v raised to minus the valuation of n.

### 156, `index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity`

The theorem is `GroundTheory.Global.index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity` in the module `GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace`. Its proof rests on 103 declarations, and the five theorems use it.

Let K be a number field, v a finite place of K, and n a positive integer such that the completion K_v contains a primitive n-th root of unity. Then the index of the subgroup of n-th powers in K_v^× equals n² divided by the norm of n in K_v.

```
μ_n ⊆ K_v ⟹ [K_v^× : (K_v^×)^n] = n²/|n|_v
```

The first reader gives it the kind standard fact and names the published result as follows. The index formula for n-th powers in a p-adic field, [F^× : F^{×n}] = n·#μ_n(F)/|n|_F, in the case where the n-th roots of unity lie in the field. Jürgen Neukirch, Algebraic Number Theory, 1999 (Chapter II, Section 5).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The index formula for n-th powers in a nonarchimedean local field F, which says that the index of F^{×n} in F^× is n·#μ_n(F)/|n|_F (Neukirch, Algebraic Number Theory, Chapter II, Section 5), in the case where the n-th roots of unity lie in the completion. For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The roots of unity are required only in the completion K_v, so this hypothesis is weaker than asking for them in K.

### 157, `index_range_powMonoidHom_adicCompletion`

The theorem is `GroundTheory.Global.index_range_powMonoidHom_adicCompletion` in the module `GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace`. Its proof rests on 102 declarations, and the five theorems use it.

Let K be a number field, v a finite place of K with completion K_v, and n a nonzero natural number. Then the index of the subgroup of n-th powers in K_v^× equals n times the number of n-th roots of unity in K_v, divided by the norm of n in K_v.

```
n ≠ 0 ⟹ [K_v^× : (K_v^×)^n] = n·#μ_n(K_v)/|n|_v
```

The first reader gives it the kind standard fact and names the published result as follows. The index formula for n-th powers in a p-adic field. Jürgen Neukirch, Algebraic Number Theory, 1999 (Chapter II, Section 5).

The second reader gives it the kind standard fact and the check the kind standard fact. The check names the published result as follows. The index formula for n-th powers in a nonarchimedean local field F, which says that the index of F^{×n} in F^× is n·#μ_n(F)/|n|_F (Neukirch, Algebraic Number Theory, Chapter II, Section 5). For the relation to that result the check has same, the first reader same and the second reader same.

The check adds this. The index is a natural number cast to ℝ that Mathlib sets to zero for an infinite index, so the formula also shows that the index is finite.

### 158, `primitive_derivation_pairing`

The theorem is `GlobalTheory.T.primitive_derivation_pairing` in the module `Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairingStatement`. Its proof rests on 101 declarations, and the five theorems use it.

Let k be an algebraically closed field of prime characteristic p, and let A be a finite-dimensional commutative and cocommutative Hopf algebra over k, which is the coordinate ring of a finite commutative group scheme over k. Let P be a subspace of A made of primitive elements, those f with Δf = f ⊗ 1 + 1 ⊗ f. Let W be a subspace of the dual of A made of functionals v with v(fg) = v(f)ε(g) + ε(f)v(g), which are elements of the Lie algebra of the group scheme. If every element of W vanishes on every element of P, then p^{dim P + dim W} divides dim_k A.

```
P ⊆ Prim(A), W ⊆ Der_ε(A, k), W(P) = 0 ⟹ p^{dim P + dim W} | dim_k A
```

The first reader gives it the kind technical step and names the published result as follows. No published result known. It is a divisibility bound for the order of a finite commutative group scheme in terms of an orthogonal pair of subspaces, one of primitive elements and one of Lie algebra elements.

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. No published result known. It is a divisibility bound for the order of a finite commutative group scheme over an algebraically closed field of characteristic p in terms of an orthogonal pair of subspaces of the Lie algebra of the group scheme and of the Lie algebra of its Cartier dual. For the relation to that result the check has none, the first reader none and the second reader none.

The check adds this. The orthogonality hypothesis is needed, as α_p shows, where the primitive element x and the derivation at the counit pair to 1 and the sum of dimensions 2 would give p² dividing p.

### 159, `htPres`

The theorem is `UpperTheory.V.J.htPres` in the module `Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtPres`. Its proof rests on 101 declarations, and the five theorems use it.

Let O be a discrete valuation ring that is complete for its maximal ideal, N and N′ natural numbers, R a commutative ring, and p a surjective ring homomorphism from the power series ring O[[x₁,…,x_N]] onto R whose kernel is generated by N′ power series f₁,…,f_{N′}. Then every prime ideal Q of R satisfies two relations for its preimage 𝔮 = p⁻¹(Q). The height of 𝔮 plus the Krull dimension of R/Q equals N + 1, and the height of 𝔮 is at most the height of Q plus N′.

```
∀Q ∈ Spec R, ht(p⁻¹Q) + dim(R/Q) = N + 1 ∧ ht(p⁻¹Q) ≤ ht(Q) + N′
```

The first reader gives it the kind technical step and names the published result as follows. The dimension formula ht 𝔮 + dim A/𝔮 = dim A in a Cohen–Macaulay local ring, combined with the consequence of Krull's height theorem that dividing by r elements lowers the dimension by at most r, both applied to A = O[[x₁,…,x_N]]. Hideyuki Matsumura, Commutative Ring Theory, 1986 (Theorems 13.6 and 17.4).

The second reader gives it the kind technical step and the check the kind technical step. The check names the published result as follows. The dimension formula ht 𝔮 + dim B/𝔮 = dim B in the regular local ring B = O[[x₁,…,x_N]] of dimension N + 1, combined with Krull's height theorem in the form that dividing by N′ elements lowers the height by at most N′ (Matsumura, Commutative Ring Theory, Theorems 13.6 and 17.4). For the relation to that result the check has special case, the first reader special case and the second reader special case.

The check adds this. The first relation uses only that O[[x₁,…,x_N]] is a regular local ring of dimension N + 1, and the generators of the kernel enter only the second relation.
