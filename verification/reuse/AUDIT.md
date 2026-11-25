# The propositions from the literature, compared with the theorems they are named after

The Lean source in [`src`](../../src) labels 361 propositions as results from the literature.
For 70 of them the source holds a proof, the five theorems of
[`Main.lean`](../../src/Main.lean) depend on the proposition, and the proposition is written
with at most 20 definitions of the project. This document says for each of the 70 what its Lean
text states and how that statement relates to the published theorem that its name points to.
By the check described below, 18 state the same as the published theorem, 34 state a special
case of it, 14 state something weaker, 2 something stronger and 1 something different, and 1
stays undecided. No reading found an empty proposition, which would be one whose hypotheses
nothing can meet or whose conclusion holds for a trivial reason.

A language model, Claude, wrote the readings on 25 November 2026, and a further run of the same
model checked them. The readers stated each published theorem from the model's own knowledge of
the literature and opened no source. No mathematician has checked the comparison. A relation
given here is a pointer for a specialist, who can settle it from the entry and the Lean text.

The comparison serves two uses, each only as far as a specialist confirms the relation. The
first is to let a proposition stand in for its published theorem in another Lean development,
which [`README.md`](README.md) describes. A proposition that states the same can do that, and
a special case or a weaker statement can do it only where the narrower form is enough. The
second use is to check the main proof. Each of the 70 propositions is used, directly or through
other declarations, by at least one of the five theorems, so a reader of the main proof can
look up here how a step with the name of a published theorem compares with that theorem.

## Words used here

- A proposition is a definition of the project of type `Prop` that stands for a claim. The 70
  propositions are those among the 361 that meet three conditions. The five theorems reach the
  proposition, which means that a chain of mentions leads from one of the five theorems to it.
  The source holds a theorem with no hypotheses whose statement is the proposition. And the
  vocabulary of the proposition has at most 20 definitions.
- The vocabulary of a proposition is the set of definitions of the project that occur in it or
  in a definition that it uses, and so on. [`README.md`](README.md) gives the exact rule.
- A proof rests on the declarations of the project that it uses, directly or through other
  declarations, the theorem itself included.
- The published theorem of a proposition is the theorem that its name points to. Each reader
  named that theorem itself, and the table prints the name that the first reader gave.
- The relation of a proposition to its published theorem is one of six words. Same means that
  the two say the same up to the way of writing, and the check also uses it when the part
  left out follows at once, as a converse does. A special case is the published theorem for a
  narrower kind of object. Weaker means that the Lean statement follows from the published
  theorem and claims less. Stronger means that it claims more. Different means that it is
  another statement, and cannot tell leaves the relation open. The briefs give no rule for a
  proposition whose differences point in more than one direction, so each reader and the check
  chose the word that it found to fit best. The list of differences is the firmer part of an
  entry.
- A difference is a hypothesis that one side has and the other lacks, a narrower or wider kind
  of object, a weaker or stronger conclusion, or a definition of the project that differs from
  the usual notion of its name.
- A proposition is empty when a hypothesis is impossible to meet, when a definition makes a
  condition hold for every input, or when the conclusion follows at once from the hypotheses.

## What the comparison found

| Relation | First reader | Second reader | Check |
|---|---:|---:|---:|
| same | 17 | 19 | 18 |
| special case | 36 | 34 | 34 |
| weaker | 15 | 12 | 14 |
| stronger | 1 | 4 | 2 |
| different | 1 | 1 | 1 |
| cannot tell | 0 | 0 | 1 |

The two readers and the check give the same relation for 54 of the 70 propositions, and the
two readers agree with each other on 55. The check confirmed 272 differences from the Lean
text, between none and eight for a proposition. It found four errors in the first reader's
accounts of the Lean text, one in each of four propositions, and one error in an account of the
second reader. The entry of a proposition prints the errors of the first reader.

Both readers and the check looked for emptiness in every proposition. For 62 propositions the
check wrote that it found none. For the other eight it added a remark, and each of the eight
remarks ends in the finding that the proposition keeps its content. An entry prints the remark.

These examples give the check's judgement and the differences that it confirmed.

- `HasseNorm` is taken for the same statement as the Hasse norm theorem. It states that an
  element that is a local norm at every place is a global norm, for a cyclic extension of number
  fields, and leaves out the converse, which is immediate.
- `StoneVonNeumann` is taken for the same statement as the Stone-von Neumann theorem for the
  Heisenberg group over a p-adic field, in its form for smooth representations. The original
  theorem of Stone and von Neumann concerns unitary representations of the real Heisenberg
  group, and the proposition does not state that theorem.
- `FerreroWashington` is taken for a special case of the Ferrero-Washington theorem. It bounds
  the l-rank of the class groups in place of stating that the μ-invariant vanishes, and it
  covers the abelian fields that hold a primitive l-th root of unity, or a primitive fourth
  root when l = 2.
- `GreenCuspidal` and `GreenRegularCharacters` are taken for special cases of Green's
  classification of the cuspidal characters of the general linear groups over finite fields.
  Both treat the prime fields only, and both give the values of a character at the identity
  and at the elements with an irreducible characteristic polynomial only.
- `Linnik` is taken for weaker than Linnik's theorem. It bounds the infimum of the primes in a
  residue class, which is 0 for an empty set, so on its own it does not say that such a prime
  exists. Together with Dirichlet's theorem it gives Linnik's theorem in full.
- `ChebotarevDegreeOne` is taken for weaker than the Chebotarev density theorem. It states that
  a prime with a given Frobenius element exists outside every finite set, and it states no
  density.
- `ResolutionCharZero` is taken for weaker than Hironaka's resolution of singularities in its
  strong form. Each blow-up of its sequence may have any ideal sheaf as its centre, where
  Hironaka's theorem blows up smooth centres over the singular locus.
- `GlobalArtinReciprocity` is taken for weaker than the Artin reciprocity law. It states that a
  map with the listed properties exists and states no uniqueness, and it gives the
  compatibility with the local fields through the images of the units, of the uniformizers
  and of the local multiplicative groups only.
- `AdmissibleClosure` is taken for a different statement from Harish-Chandra's correspondence
  between closed invariant subspaces and submodules of the K-finite vectors. It keeps one
  direction of the correspondence and puts the hypothesis of finite multiplicities on the
  subspace in place of the whole representation.
- `DualAbelianScheme` stays undecided. The check could not settle from memory whether the
  published theorem gives the dual as a scheme over every base, as the proposition states.

## How the comparison was made

1. [`audit.py`](audit.py) wrote a dossier for each of the 70 propositions. A dossier holds the
   whole Lean text of the proposition and of every definition of its vocabulary, with the
   `variable` lines in scope. Six propositions also use instances that the source declares
   without a name, 18 in all, and their dossiers hold the text of those instances. Nothing is
   cut. The 70 dossiers hold 359,491 characters.
2. A first reader wrote, from the dossier alone, what the Lean text states and the statement in
   ordinary notation. It then named the published theorem, stated it from its own knowledge
   with one reference, judged the relation, listed the differences and looked for emptiness.
3. A second reader did the same from the same dossier without seeing the first.
4. A check compared both accounts with the Lean text. It kept a difference when the Lean text
   shows it, dropped one that the Lean text contradicts, and gave its own relation.

The first reader, the second reader and the check are runs of the command line tool Claude
Code. The 70 dossiers were split into seven batches of ten, in the order of the table. Each run
was started in a folder that held only the ten dossiers of one batch and, for the check, the
two readings of that batch. The briefs of the three roles are in
[`briefs/`](briefs/).

Propositions 68 and 69 were read twice. Their first dossiers showed a named instance of the
project without its value, and the check remarked that it could not see a topology and a
measurable structure. The dossiers were written again with the values, both readers and the
check ran again on the two, and the entries print that second round. The relations stayed as
they were.

## Limits

- The two readers and the check are the same language model, so they can share a blind spot
  that the check does not find. A model of another maker has not repeated the check.
- The published theorems come from the model's memory of the literature. The reference that an
  entry names was not opened, and a relation can be wrong because the published theorem was
  remembered in a narrower or a wider form than it has.
- A dossier opens the definitions of the project. A name of Mathlib is taken with the meaning
  that Mathlib gives it, and no definition of Mathlib was opened.
- The comparison is of statements. No proof was read, and the compiled files that count the
  declarations come from the build cache of the repository.
- Of the other 291 propositions, 136 meet the first two conditions and have a vocabulary of
  more than 20 definitions. The five theorems do not reach 69, and 86 are reached without a
  theorem with no hypotheses that states them. None of the 291 was compared.
- The six words are coarse. A special case can be the one case that the main proof needs, and
  a weaker statement can still carry the step that it is used for.

## Files

| File | Content |
|---|---|
| `audit.py` | writes the dossiers into `data/audit`, which git ignores, collects the answers and writes the entries below |
| `briefs/` | the briefs of the first reader, the second reader and the check |
| `audit.json` | for each of the 70 propositions the two readings and the answer of the check |

## How to read the table and the entries

The table has one row for each proposition, in the order of the size of its vocabulary. A cell
that ends in three dots is cut. The three columns after the published theorem give the relation
by the first reader, the second reader and the check. An entry prints the first reader's
account of the Lean text and its statement in ordinary notation, the published theorem as the
first reader stated it, the three relations, the differences that the check confirmed, the
check's reason where the readers disagree, its remark on emptiness and the errors that it
found in the first reader's account. An entry ends with the confidence that the first reader
gave for its relation, high, medium or low, and the reason that it gave.

<!-- entries -->

## The propositions at a glance

| No. | Proposition | Theorem that the name points to | First reader | Second reader | Check | Vocabulary | The proof rests on |
|---:|---|---|---|---|---|---:|---:|
| 1 | `ChevalleyUnits` | Chevalley's theorem on units (congruence subgroup property of the … | special case | stronger | special case | 0 | 250 |
| 2 | `HasseNorm` | Hasse norm theorem | same | same | same | 0 | 410 |
| 3 | `HasseNormSt` | Hasse norm theorem for quadratic extensions | special case | special case | special case | 0 | 183 |
| 4 | `IdentityComponentOpen` | Openness of the identity component of a smooth group scheme | same | weaker | same | 0 | 177 |
| 5 | `SchurOrthogonalitySquareIntegrable` | Schur orthogonality relations for square-integrable representations … | same | weaker | weaker | 0 | 14 |
| 6 | `FerreroWashington` | Ferrero–Washington theorem | special case | special case | special case | 0 | 5,560 |
| 7 | `BrauerDegreeZero` | Brauer's induction theorem in degree-zero form | special case | same | same | 1 | 113 |
| 8 | `AbMulNSt` | Structure of the n-torsion of an abelian variety | weaker | same | same | 2 | 2,048 |
| 9 | `HermitianHassePrinciple` | Landherr's theorem (Hasse principle for Hermitian forms) | same | same | same | 2 | 278 |
| 10 | `Linnik` | Linnik's theorem on the least prime in an arithmetic progression | weaker | weaker | weaker | 2 | 511 |
| 11 | `PartialZetaFunctionalEquation` | Hecke's functional equation for partial zeta functions of ideal … | special case | special case | special case | 2 | 1,246 |
| 12 | `DefQuatExists` | Existence of quaternion algebras with prescribed ramification (Hasse, … | special case | special case | special case | 2 | 357 |
| 13 | `CanonicalExtensionRankOne` | Deligne's canonical extension of a flat bundle with logarithmic poles | special case | different | weaker | 3 | 42 |
| 14 | `CuspidalExists` | Existence of cuspidal representations of GL_n over a finite field … | same | same | same | 3 | 403 |
| 15 | `FinitenessOfHermitianClasses` | Finiteness of class numbers for Hermitian lattices (Borel, Borel and … | special case | special case | special case | 3 | 25 |
| 16 | `HermitianLocalGlobal` | Local classification of Hermitian forms and Landherr's Hasse principle | special case | special case | special case | 3 | 303 |
| 17 | `IdealInvariantsOneOrbitSt` | Main theorem of complex multiplication for j-invariants (Weber, Hasse) | weaker | same | same | 3 | 6,593 |
| 18 | `StoneVonNeumann` | Stone–von Neumann theorem for the Heisenberg group over a p-adic field | same | same | same | 3 | 49 |
| 19 | `AbelianUnobstructed` | Grothendieck's theorem on infinitesimal lifting of abelian schemes | special case | same | same | 4 | 5,678 |
| 20 | `DixmierMalliavinFactorisation` | Dixmier–Malliavin factorisation theorem | stronger | special case | special case | 4 | 266 |
| 21 | `IrreducibleAdmissibleGL` | Admissibility of irreducible smooth representations of GL_n over a … | same | same | same | 4 | 1,431 |
| 22 | `MetaplecticRepresentation` | Existence of the metaplectic representation (Segal, Shale, Weil) | weaker | stronger | stronger | 4 | 313 |
| 23 | `SiegelKlingen` | Siegel–Klingen theorem | same | same | same | 4 | 302 |
| 24 | `ComplexMultiplicationJSt` | Main theorem of complex multiplication for the j-invariant (Weber, … | same | same | same | 5 | 6,574 |
| 25 | `HilbertClassFieldJ` | Weber's theorem that j(𝓞_K) generates the Hilbert class field (Weber, … | same | same | same | 5 | 6,590 |
| 26 | `CMCurveGoodOutsidePrimeSt` | Gross's elliptic curve A(p) (B. H. Gross) | weaker | weaker | weaker | 6 | 7,348 |
| 27 | `ChebotarevDegreeOne` | Chebotarev density theorem | weaker | weaker | weaker | 6 | 236 |
| 28 | `ChowFormExists` | Existence and uniqueness of the Chow form (Cayley, Chow and van der … | special case | special case | special case | 6 | 295 |
| 29 | `ChowFormIntExists` | Existence and uniqueness of the Chow form of a homogeneous prime … | special case | special case | special case | 6 | 289 |
| 30 | `RadfordShufflePolynomial` | Radford's theorem | same | same | same | 6 | 59 |
| 31 | `ResolutionCharZero` | Hironaka's resolution of singularities in its strong form | weaker | weaker | weaker | 7 | 7,699 |
| 32 | `RayClassFieldSt` | Existence theorem for ray class fields (Takagi) | special case | special case | special case | 7 | 3,873 |
| 33 | `FreeQuotientScheme` | Quotient of a scheme by a finite locally free group scheme (SGA 3, … | weaker | same | special case | 8 | 136 |
| 34 | `CMPotentialGoodReductionSt` | Serre–Tate theorem on potential good reduction of abelian varieties … | special case | special case | special case | 8 | 9,632 |
| 35 | `ChowFormHyperplaneSection` | Chow form of a hyperplane section | special case | special case | special case | 8 | 427 |
| 36 | `DeligneRibet` | Deligne–Ribet integrality theorem for partial zeta values of totally … | special case | special case | special case | 8 | 4,444 |
| 37 | `RayClassFieldMaximalSt` | Maximality of the ray class field in class field theory | special case | special case | special case | 8 | 62 |
| 38 | `WeberRayFieldSt` | Weber–Hasse theorem on ray class fields of imaginary quadratic fields … | special case | special case | special case | 8 | 7,141 |
| 39 | `KStability` | Homological stability for general linear groups (van der Kallen) | weaker | weaker | weaker | 8 | 345 |
| 40 | `PrincipalisationCharZero` | Principalisation of ideal sheaves (Hironaka, in the algorithmic form … | weaker | weaker | weaker | 9 | 6,159 |
| 41 | `SemiAbelianHomExtension` | Extension of homomorphisms of semi-abelian schemes over a normal base … | same | same | same | 9 | 2,424 |
| 42 | `CubeTheorem` | Theorem of the cube for abelian schemes | same | same | same | 10 | 2,459 |
| 43 | `GreenRegularCharacters` | Green's parametrisation of the cuspidal characters of GL_n(F_q) | special case | special case | special case | 10 | 1,169 |
| 44 | `KFiniteAnalyticUJ` | Harish-Chandra's theorem that K-finite vectors are analytic | special case | special case | special case | 10 | 838 |
| 45 | `Principalisation` | Hironaka's principalisation of ideals, in Kollár's formulation | special case | special case | special case | 10 | 6,583 |
| 46 | `RealMetaplecticRepresentation` | Segal–Shale–Weil theorem on the metaplectic (oscillator) … | weaker | same | weaker | 10 | 259 |
| 47 | `TameQuotient` | Iwasawa's structure theorem for the tame Galois group of a local … | weaker | weaker | weaker | 10 | 157 |
| 48 | `InducedSimpleLowestAlcove` | Simplicity of induced modules for weights in the closure of the … | special case | special case | special case | 11 | 523 |
| 49 | `CuspidalRestrictsToInduced` | Gelfand's theorem on the restriction of cuspidal representations of … | same | same | same | 13 | 313 |
| 50 | `DepthZeroJacquetInjective` | Moy–Prasad compatibility of depth-zero invariants with Jacquet … | weaker | weaker | weaker | 13 | 156 |
| 51 | `KudlaSplittingSplitUnitary` | Kudla's splitting of the metaplectic cover over unitary groups | special case | special case | special case | 13 | 1,737 |
| 52 | `AdmissibleCoefficientsAnalytic` | Harish-Chandra's theorem that K-finite vectors of admissible … | special case | special case | special case | 14 | 939 |
| 53 | `CuspidalMirabolic` | Gelfand's theorem on the mirabolic restriction of cuspidal … | same | stronger | stronger | 15 | 708 |
| 54 | `InfinitesimalEquivalence` | Harish-Chandra's theorem that infinitesimal equivalence implies … | special case | special case | special case | 15 | 1,227 |
| 55 | `GreenCuspidal` | Green's classification of the cuspidal characters of GL_n(F_q) | special case | special case | special case | 16 | 601 |
| 56 | `QuadraticClassFieldTheory` | Global class field theory for quadratic extensions (Hasse norm … | special case | special case | special case | 16 | 436 |
| 57 | `GlobalArtinReciprocity` | Artin reciprocity law of global class field theory | weaker | weaker | weaker | 17 | 3,761 |
| 58 | `KernelFiniteFlatSt` | Finiteness and flatness of K(L) for a relatively ample line bundle on … | special case | special case | special case | 17 | 3,378 |
| 59 | `LeviSubmoduleDense` | Harish-Chandra's density theorem for Harish-Chandra modules of … | special case | special case | special case | 17 | 547 |
| 60 | `PotentialGoodReductionSt` | Serre–Tate criterion for potential good reduction | special case | special case | special case | 17 | 9,253 |
| 61 | `AdmissibleClosure` | Harish-Chandra's correspondence between closed invariant subspaces … | different | special case | different | 18 | 661 |
| 62 | `L2ExtensionLogCanonical` | Ohsawa–Takegoshi L² extension theorem for log canonical centres in … | special case | special case | weaker | 18 | 1,297 |
| 63 | `MoyPrasadJacquetIso` | Moy–Prasad theorem on Jacquet functors and fixed vectors of the … | special case | special case | special case | 18 | 205 |
| 64 | `NeronOggShafarevichSt` | Néron–Ogg–Shafarevich criterion (Serre–Tate) | special case | special case | special case | 18 | 9,201 |
| 65 | `CasselmanWallach` | Casselman–Wallach theorem | special case | special case | special case | 19 | 1,832 |
| 66 | `DualAbelianScheme` | Existence of the dual abelian scheme and biduality | same | stronger | cannot tell | 19 | 7,912 |
| 67 | `KFiniteVectorsUnitary` | Harish-Chandra's admissibility theorem and the Harish-Chandra module … | special case | special case | special case | 19 | 964 |
| 68 | `UnitaryIrreducibleAdmissible` | Bernstein's theorem that irreducible unitary representations of … | special case | special case | special case | 19 | 1,354 |
| 69 | `DiscreteSeriesUpqExists` | Harish-Chandra's theorem on the discrete series, with the lowest … | weaker | weaker | weaker | 20 | 5,265 |
| 70 | `FormalAlgebraisation` | Grothendieck's existence theorem (formal GAGA), for morphisms and for … | same | same | same | 20 | 4,382 |

## The propositions

### 1, `ChevalleyUnits`

The proposition is `GlobalTheory.Published.ChevalleyUnits`. Its vocabulary has 0 definitions of the project, and the proof of the theorem `GlobalTheory.Published.chevalleyUnits'` that states it rests on 250 declarations.

For every number field E and all natural numbers m > 0 and b > 0, the text asserts that there is a natural number a > 0 that is coprime to b and has the following property. Every unit u of the ring of integers of E such that a divides u − 1 in that ring is the m-th power of a unit v of the same ring. The modulus a is a rational integer and may depend on E, m and b.

```
∀ number field E, ∀ m, b ≥ 1, ∃ a ≥ 1 with gcd(a, b) = 1 such that every u ∈ O_E^× with u ≡ 1 (mod a·O_E) lies in (O_E^×)^m
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be a number field, S a finite set of places of K containing the archimedean ones, and n ≥ 1 an integer. Then there is an integral ideal 𝔪 prime to S such that every S-unit congruent to 1 modulo 𝔪 is the n-th power of an S-unit, so every subgroup of finite index in the S-units contains a congruence subgroup. The reference is C. Chevalley, Deux théorèmes d'arithmétique, Journal of the Mathematical Society of Japan 3, 1951.

The first reader takes the proposition for a special case and the second reader for a stronger statement. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text concerns only the units of the ring of integers of E, while Chevalley's theorem in its published S-unit form concerns the S-units for any finite set S of places that contains the infinite ones.
- The Lean text requires the modulus a to be coprime to an arbitrary positive integer b, which is what the S-unit form gives when S contains the primes above b, and which claims more than the unit form that allows any modulus.
- The modulus is a positive rational integer a rather than an ideal, which loses nothing because the positive generator of the intersection with ℤ of an ideal prime to the primes above b is coprime to b.
- Only the subgroup of m-th powers of units appears, which loses nothing against the form with arbitrary subgroups of finite index, because a subgroup of index k in the abelian unit group contains every k-th power.

The check gives this reason for its judgement. The coprimality of the modulus to an arbitrary b is what Chevalley's S-unit theorem gives when S contains the primes above b, so the Lean text is that theorem restricted to units, and it is stronger only against the narrower unit form with a free modulus that B compares it with.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. Published formulations differ between a unit version with an unrestricted modulus, against which the Lean text is stronger, and an S-unit version with a modulus prime to S, of which the Lean text is a special case.

### 2, `HasseNorm`

The proposition is `GlobalTheory.Published.HasseNorm`. Its vocabulary has 0 definitions of the project, and the proof of the theorem `GlobalTheory.CNorm.hasseNorm` that states it rests on 410 declarations.

For all number fields K and L with L a Galois extension of K whose Galois group is cyclic, and for every nonzero a ∈ K, the text makes two assumptions. At every finite place v of K some element z of K_v ⊗_K L has norm a over the completion K_v, and at every infinite place v of K some element z of K_v ⊗_K L has norm a over K_v. The conclusion is that a = N_{L/K}(x) for some x ∈ L.

```
L/K cyclic, a ∈ K^×, (∀ places v of K, a ∈ N_{K_v ⊗_K L / K_v}(K_v ⊗_K L)) ⟹ ∃ x ∈ L with N_{L/K}(x) = a
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let L/K be a cyclic extension of number fields. An element a ∈ K^× is the norm of an element of L^× if and only if, for every place v of K and a place w of L above v, it is the norm of an element of L_w^×. The reference is H. Hasse, Beweis eines Satzes und Widerlegung einer Vermutung über das allgemeine Normenrestsymbol, Nachrichten der Gesellschaft der Wissenschaften zu Göttingen, 1931.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The local condition is a norm from the algebra K_v ⊗_K L over K_v, which is the product of the completions L_w over the places w above v, and because these completions are isomorphic over K_v for a Galois extension and a is nonzero, the condition says exactly that a is a norm from L_w.
- The Lean text states only that a local norm at every place is a global norm, and it leaves out the converse direction of the published equivalence, which is immediate.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The norm from K_v ⊗_K L is the product of the norms from the completions L_w above v, and since L/K is Galois a norm from one L_w already gives a norm from the product, so the local hypotheses and the global conclusion match Hasse's theorem.

### 3, `HasseNormSt`

The proposition is `GlobalTheory.Published.HasseNormSt`. Its vocabulary has 0 definitions of the project, and the proof of the theorem `GlobalTheory.QNorm.hasseNormSt` that states it rests on 183 declarations.

For every number field F and all nonzero δ, x ∈ F, the text makes two assumptions. For every real embedding σ of F there are real numbers a, b with σ(x) = a² − σ(δ)b², and for every finite place v of F there are a, b in the completion F_v with x = a² − δb² in F_v. The conclusion is that x = a² − δb² for some a, b ∈ F. The complex places carry no condition, and none is needed because every complex number has this form.

```
δ, x ∈ F^×, (∀ real σ, ∃ a, b ∈ ℝ with σ(x) = a² − σ(δ)b²) ∧ (∀ finite v, ∃ a, b ∈ F_v with x = a² − δb²) ⟹ ∃ a, b ∈ F with x = a² − δb²
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let F be a number field and δ ∈ F^× a non-square. An element x ∈ F^× is a norm from F(√δ), that is x = a² − δb² with a, b ∈ F, if and only if it is a norm from F_v(√δ) in every completion F_v. This is the case of degree 2 of Hasse's norm theorem and is equivalent to the Hasse–Minkowski theorem for the ternary form X² − δY² − xZ². The reference is H. Hasse, Beweis eines Satzes und Widerlegung einer Vermutung über das allgemeine Normenrestsymbol, Nachrichten der Gesellschaft der Wissenschaften zu Göttingen, 1931.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text covers only the extensions F(√δ)/F of degree at most 2 with norm form a² − δb², while Hasse's norm theorem covers every cyclic extension of number fields.
- The complex places carry no condition, which loses nothing because every complex number has the form a² − δb² over ℂ.
- The Lean text admits a δ that is a square in F, and in that case the conclusion holds for every x.
- The Lean text states only the direction from local norms to a global norm, and the converse direction is immediate.

On emptiness the check wrote this. No hypothesis is impossible to meet, and only in the subcase where δ is a square in F does the conclusion hold at once, so the statement keeps its full content for every non-square δ.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The expression a² − δb² is the norm form of F(√δ) over F and over each completion, and the real and finite places listed are exactly the places where the local norm condition can fail.

### 4, `IdentityComponentOpen`

The proposition is `GlobalTheory.Published.IdentityComponentOpen`. Its vocabulary has 0 definitions of the project, and the proof of the theorem `GlobalTheory.identityComponentOpen` that states it rests on 177 declarations.

For every scheme S and every group scheme G over S whose structure morphism f is smooth, the text asserts that there is a group scheme G₀ over S and a homomorphism j from G₀ to G of group schemes over S whose underlying morphism of schemes is an open immersion. The image of j is exactly the set of points x of G that lie in the connected component of the unit point e(s) inside the fibre f⁻¹(s) over s = f(x), where the fibre carries the subspace topology. So j identifies G₀ with the open subgroup scheme formed by the identity components of all fibres.

```
G → S smooth group scheme ⟹ ∃ group scheme G₀ over S and an open immersion homomorphism j from G₀ to G with j(G₀) = ⋃_{s ∈ S} (G_s)⁰, where (G_s)⁰ is the connected component of e(s) in f⁻¹(s)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a group scheme over a scheme S that is smooth over S. Then the union G⁰ of the identity components of the fibres G_s is an open subset of G, and with its open subscheme structure it is a subgroup scheme of G with connected fibres. The reference is M. Demazure and A. Grothendieck, Schémas en groupes I (SGA 3), Exposé VI_B, Théorème 3.10, 1970.

The first reader takes the proposition for the same statement and the second reader for a weaker statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text asserts only that G₀ and j exist and states no uniqueness, but uniqueness follows because j is an open immersion whose image the condition on points fixes, and j is a monomorphism of group objects.
- The fibre is the set of points of G over s with the subspace topology rather than the scheme G_s, which changes nothing because the two spaces are homeomorphic.
- The Lean text assumes that the structure morphism G → S is smooth, which is the hypothesis of the usual statement of the theorem.
- Only schemes in universe 0 are covered.

The check gives this reason for its judgement. The condition on points fixes the open set G⁰ as the union of the identity components of the fibres, and j makes this set an open subgroup scheme, which is the published conclusion for a smooth group scheme, while the uniqueness that B counts as missing follows from that condition, so the Lean text is not weaker.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The image condition fixes the open set G⁰ point by point, an open subscheme is determined by its open set, and the topological fibre f⁻¹(s) is homeomorphic to the scheme-theoretic fibre G_s, so the Lean text says exactly that G⁰ is an open subgroup scheme.

### 5, `SchurOrthogonalitySquareIntegrable`

The proposition is `GlobalTheory.Published.SchurOrthogonalitySquareIntegrable`. Its vocabulary has 0 definitions of the project, and the proof of the theorem `GlobalTheory.Published.schurOrthogonalitySquareIntegrable'` that states it rests on 14 declarations.

Let G be a locally compact Hausdorff group with its Borel σ-algebra and a regular Haar measure μ that is both left and right invariant, and let π be a homomorphism from G into the bounded operators on a complex Hilbert space H. Assume that every π(g) is isometric, that every map g ↦ π(g)v is continuous, that the only closed invariant subspaces are 0 and H, and that some matrix coefficient g ↦ ⟨w₀, π(g)v₀⟩ with v₀ ≠ 0 and w₀ ≠ 0 lies in L²(μ). Then every matrix coefficient lies in L²(μ), and there is a real d > 0 such that for all v, w, v', w' the function ⟨w, π(g)v⟩·conj⟨w', π(g)v'⟩ is integrable with integral ⟨v', v⟩⟨w, w'⟩/d. The inner product here is conjugate linear in its first argument.

```
π irreducible unitary, ∃ v₀, w₀ ≠ 0 with ⟨w₀, π(·)v₀⟩ ∈ L²(μ) ⟹ ∀ v, w, ⟨w, π(·)v⟩ ∈ L²(μ) and ∃ d > 0 with ∫_G ⟨w, π(g)v⟩ conj⟨w', π(g)v'⟩ dμ(g) = ⟨v', v⟩⟨w, w'⟩/d
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a unimodular locally compact group and π an irreducible unitary representation of G on H. If one nonzero matrix coefficient g ↦ (π(g)u, v) is square integrable, then all of them are, and there is a constant d_π > 0, the formal degree, with ∫_G (π(g)u₁, v₁) conj(π(g)u₂, v₂) dg = d_π⁻¹ (u₁, u₂) conj(v₁, v₂) for all vectors. The reference is R. Godement, Sur les relations d'orthogonalité de V. Bargmann, Comptes Rendus de l'Académie des Sciences de Paris 225, 1947.

The first reader takes the proposition for the same statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text treats a single representation π and leaves out the second orthogonality relation, which says that the matrix coefficients of two inequivalent square-integrable irreducible representations are orthogonal in L²(G).
- The Haar measure is required to be both left and right invariant, which confines G to unimodular groups, the setting of Godement's theorem.
- Unitarity is expressed as norm preservation of every π g, which is equivalent because π g has the inverse π g⁻¹.
- With the inner product conjugate linear in its first argument, the right side ⟪v', v⟫ · ⟪w, w'⟫ / d equals the published d⁻¹ (v, v') conj(w, w') with the inner product linear in its first argument, so the formulas agree.

The check gives this reason for its judgement. The Lean text has only one representation and so cannot express the orthogonality of the coefficients of inequivalent representations that the Schur orthogonality relations of Godement also assert, which makes it one of the two published relations and therefore weaker, while A compared it with the first relation alone.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. After translating the inner product convention, with (x, y) in the classical notation equal to ⟨y, x⟩ in the Lean notation, the hypotheses and the orthogonality formula coincide term by term with Godement's theorem.

### 6, `FerreroWashington`

The proposition is `UpperTheory.V.Published.FerreroWashington`. Its vocabulary has 0 definitions of the project, and the proof of the theorem `UpperTheory.V.FW.ferreroWashington` that states it rests on 5,560 declarations.

For every prime l and every number field K that is abelian over ℚ and contains a primitive l-th root of unity, or a primitive fourth root of unity when l = 2, the text asserts that there is a natural number r with the following property. For every n and every field K' generated over K by a primitive l^n-th root of unity, the quotient of the class group of K' by its subgroup of l-th powers has at most l^r elements. So the l-rank of the class groups along the tower K(μ_{l^n}) is bounded independently of n.

```
∀ l prime, ∀ K/ℚ abelian with μ_l ⊂ K (μ_4 ⊂ K if l = 2), ∃ r, ∀ n ≥ 0, |Cl(K(μ_{l^n})) / Cl(K(μ_{l^n}))^l| ≤ l^r
```

The theorem that the name points to, as the first reader states it from its own knowledge. For every abelian number field K and every prime p, the Iwasawa μ-invariant of the cyclotomic ℤ_p-extension of K vanishes. By Iwasawa's theorem on the growth of class groups this is equivalent to the boundedness of the p-rank of the class groups of the layers of that extension. The reference is B. Ferrero and L. C. Washington, The Iwasawa invariant μ_p vanishes for abelian number fields, Annals of Mathematics 109, 1979.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text bounds the l-rank of the class groups through the order of their quotient by l-th powers instead of stating that the μ-invariant vanishes, and the two are equivalent by Iwasawa's theory of class groups in ℤ_l-extensions.
- The Lean text covers only abelian fields K that contain a primitive l-th root of unity, or a primitive fourth root of unity when l = 2, while the published theorem covers every abelian number field.
- Under that root-of-unity hypothesis the fields K(μ_{l^n}) are the layers of the cyclotomic ℤ_l-extension of K, with a shift of numbering and repetitions for small n.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The relation rests on the standard equivalence between bounded l-rank and μ = 0 and on the standard reduction to fields containing μ_l, which are not part of the published statement itself.

### 7, `BrauerDegreeZero`

The proposition is `GlobalTheory.Published.BrauerDegreeZero`. Its vocabulary has 1 definitions of the project, and the proof of the theorem `GlobalTheory.BrauerZero.brauerDegreeZero` that states it rests on 113 declarations.

For every finite group G and every finite-dimensional complex representation ρ of G on V, the text asserts that there are finitely many subgroups H_1, …, H_r of G, homomorphisms χ_i from H_i to ℂ^× and integers c_i such that tr ρ(g) − dim V = Σ_i c_i (Ind_{H_i}^G χ_i(g) − Ind_{H_i}^G 1(g)) for every g ∈ G. The project's induced function is the usual one, Ind_H^G f(g) = |H|⁻¹ Σ f(x⁻¹gx) over the x ∈ G with x⁻¹gx ∈ H. So the virtual character χ_ρ − (dim ρ)·1_G of degree zero is an integral combination of the virtual characters Ind_H^G(χ − 1_H) with χ linear.

```
χ_ρ − (dim ρ)·1_G = Σ_{i=1}^r c_i Ind_{H_i}^G(χ_i − 1_{H_i}) with H_i ≤ G, χ_i ∈ Hom(H_i, ℂ^×), c_i ∈ ℤ
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a finite group G, every virtual character of degree zero is a ℤ-linear combination of virtual characters Ind_H^G(λ − 1_H), where H runs over subgroups of G, which may even be taken elementary, and λ over one-dimensional characters of H. It is a corollary of Brauer's theorem that every character is an integral combination of characters induced from linear characters of elementary subgroups. The reference is J. Martinet, Character theory and Artin L-functions, in A. Fröhlich (ed.), Algebraic Number Fields, Academic Press, 1977.

The first reader takes the proposition for a special case and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text treats the degree-zero virtual characters χ_ρ − dim ρ of genuine representations, and since every virtual character of degree zero is a difference of two of these, the general degree-zero statement follows by subtraction.
- The Lean text allows arbitrary subgroups H_i and does not claim the sharper form in which the subgroups are elementary.
- The project's indFun is the usual formula for the induced class function, |H|⁻¹ times the sum of f(x⁻¹gx) over the x in G with x⁻¹gx in H.

The check gives this reason for its judgement. The restriction to genuine representations loses nothing because subtraction recovers every virtual character of degree zero, so the Lean text is equivalent to the degree-zero form of Brauer's theorem with arbitrary subgroups that both readers name, and only the refinement to elementary subgroups is absent.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The induction formula in the dossier is the standard one, and the statement is the degree-zero corollary of Brauer's theorem restricted to characters of representations.

### 8, `AbMulNSt`

The proposition is `GlobalTheory.Published.AbMulNSt`. Its vocabulary has 2 definitions of the project, and the proof of the theorem `GlobalTheory.abMulN_holds` that states it rests on 2,048 declarations.

For every algebraically closed field k, every group scheme B over Spec k that is an abelian scheme in the project's sense, meaning commutative, smooth, proper and geometrically connected, and smooth of relative dimension g, and every natural number n that is nonzero in k, the text asserts that the k-points x of B with x^n = 1 number exactly n^{2g}. The k-points are the sections Spec k → B with their group structure. The condition that n is nonzero in k means that n ≥ 1 and the characteristic of k does not divide n.

```
A/k abelian variety of dimension g, k algebraically closed, char k ∤ n ⟹ #A[n](k) = n^{2g}
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let A be an abelian variety of dimension g over an algebraically closed field k and n an integer not divisible by the characteristic of k. Then multiplication by n is a separable isogeny of degree n^{2g}, and the group A[n] of n-torsion points is isomorphic to (ℤ/nℤ)^{2g}. The reference is D. Mumford, Abelian Varieties, Oxford University Press, 1970, §4 and §6.

The first reader takes the proposition for a weaker statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text gives for each n only the number n^{2g} of k-points x with x^n = 1, and the group structure (ℤ/nℤ)^{2g} follows because the count holds for every n prime to the characteristic.
- The Lean text says nothing about multiplication by n as an isogeny of degree n^{2g} or about its separability, which Mumford states together with the structure of the n-torsion.
- Commutativity of the group law is among the hypotheses through the project's IsAbelianScheme, which excludes no abelian variety because every abelian variety is commutative.
- Only fields and schemes in universe 0 are covered.

The check gives this reason for its judgement. A finite abelian group with ℓ^{2g} elements killed by a prime ℓ and ℓ^{2ge} elements killed by ℓ^e must be (ℤ/ℓ^eℤ)^{2g}, so the counts for every n prime to the characteristic give the structure of the n-torsion that both readers name, and A's judgement weaker overlooks this.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Over an algebraically closed field the project's abelian scheme of relative dimension g is an abelian variety of dimension g, and the count n^{2g} is the cardinality part of Mumford's description of A[n].

### 9, `HermitianHassePrinciple`

The proposition is `GlobalTheory.Published.HermitianHassePrinciple`. Its vocabulary has 2 definitions of the project, and the proof of the theorem `GlobalTheory.Published.hermitianHassePrinciple_holds` that states it rests on 278 declarations.

Let E/F be a quadratic extension of number fields with nontrivial automorphism σ, and let G and G' be r×r matrices over E with nonzero determinant that are σ-Hermitian, meaning σ(G_ab) = G_ba. Assume that for every finite place and every infinite place v of F there is a matrix P over F_v ⊗_F E with invertible determinant and G' = Pᵀ G σ_v(P), where σ_v applies σ to the factor E. Then there is a matrix P over E with nonzero determinant and G' = Pᵀ G σ(P). So two nondegenerate Hermitian forms that are isometric at every place of F are isometric over E.

```
G, G' ∈ GL_r(E) σ-Hermitian, (∀ places v of F, ∃ P ∈ GL_r(F_v ⊗_F E) with G' = Pᵀ G σ(P)) ⟹ ∃ P ∈ GL_r(E) with G' = Pᵀ G σ(P)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let E/F be a quadratic extension of number fields with nontrivial automorphism σ. Two nondegenerate σ-Hermitian forms over E are isometric if and only if they are isometric over F_v ⊗_F E for every place v of F, and equivalently such forms are classified by rank, determinant modulo norms and the signatures at the real places of F that do not split in E. The reference is W. Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg 11, 1935.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The local condition is also imposed at the places of F that split in E and at the complex places, where F_v ⊗_F E is F_v × F_v and the condition holds automatically, so it adds no requirement.
- A hermitian matrix is written as σ(G_ab) = G_ba and an isometry as G' = Pᵀ G σ(P), which matches the usual form G' = Q* G Q with Q = σ(P).
- The Lean text states only that isometry at every place gives isometry over E, and it leaves out the immediate converse and the equivalent classification by rank, determinant modulo norms and signatures.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The congruence G' = Pᵀ G σ(P) is exactly isometry of the forms x ↦ xᵀ G σ(y), and the local conditions run over all places of F through F_v ⊗_F E, which covers split, inert and ramified places as in the classical statement.

### 10, `Linnik`

The proposition is `GlobalTheory.Published.Linnik`. Its vocabulary has 2 definitions of the project, and the proof of the theorem `UpperTheory.Lit.linnik` that states it rests on 511 declarations.

There exist real constants C > 0 and L > 0 such that for all natural numbers a ≥ 1 and q ≥ 1 with gcd(a, q) = 1 the number leastPrimeMod(a, q) is at most C·q^L. The project defines leastPrimeMod(a, q) as the infimum in ℕ of the set of primes p ≡ a (mod q). By the convention of Lean this infimum is 0 when the set is empty.

```
∃ C, L > 0, ∀ a, q ≥ 1 with gcd(a, q) = 1, inf{p prime | p ≡ a (mod q)} ≤ C·q^L, with inf ∅ = 0
```

The theorem that the name points to, as the first reader states it from its own knowledge. There are absolute constants C and L such that for all integers q ≥ 1 and a coprime to q the least prime p ≡ a (mod q) satisfies p ≤ C·q^L. The reference is Yu. V. Linnik, On the least prime in an arithmetic progression I. The basic theorem, Matematicheskii Sbornik 15 (57), 1944.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text bounds the infimum in ℕ of the set of primes p ≡ a mod q, which is 0 for an empty set, so unlike Linnik's theorem it does not assert that such a prime exists.
- Together with Dirichlet's theorem, which makes the set nonempty for coprime a and q, the Lean text gives Linnik's theorem in full.
- Requiring 1 ≤ a loses no residue class, and the case q = 1 is included and covered by the constant C.

On emptiness the check wrote this. The convention that the infimum of the empty set in ℕ is 0 would make the bound hold at once for a progression without primes, but Dirichlet's theorem shows that no progression with coprime a and q is empty, so the statement keeps its content.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Apart from the empty-set convention, which Dirichlet's theorem makes harmless, the quantifiers and the bound C·q^L match Linnik's theorem exactly.

### 11, `PartialZetaFunctionalEquation`

The proposition is `GlobalTheory.Published.PartialZetaFunctionalEquation`. Its vocabulary has 2 definitions of the project, and the proof of the theorem `PositivityTheory.Prw.partialZetaFunctionalEquation_holds` that states it rests on 1,246 declarations.

For every totally real number field F of degree n over ℚ, all ideal classes C and C′ of its ring of integers O_F and the nonzero ideal D equal to the different of O_F, the text assumes that C·C′ is the class of D. It then claims that there are functions Z and Z′ from ℂ to ℂ such that Z is holomorphic on ℂ∖{1} and equals the sum of N(J)^(−s) over the nonzero integral ideals J in the class C whenever Re s > 1, and Z′ has the same two properties for C′. Because ℂ∖{1} is connected, these two properties fix Z as the analytic continuation of the partial zeta function ζ(s, C), with a free value at s = 1. Finally the text claims d_F^(s/2) Γ_ℝ(s)^n Z(s) = d_F^((1−s)/2) Γ_ℝ(1−s)^n Z′(1−s) for every s with s ∉ {0, −2, −4, …} and 1 − s ∉ {0, −2, −4, …}, where d_F is the absolute value of the discriminant of F and Γ_ℝ(s) = π^(−s/2) Γ(s/2).

```
∀ F totally real of degree n, ∀ C, C′ ∈ Cl(O_F) with C·C′ = [𝔡_F], ∃ Z, Z′ holomorphic on ℂ∖{1} with Z(s) = Σ_{[J]=C} N(J)^(−s) and Z′(s) = Σ_{[J]=C′} N(J)^(−s) for Re s > 1, such that |d_F|^(s/2) Γ_ℝ(s)^n Z(s) = |d_F|^((1−s)/2) Γ_ℝ(1−s)^n Z′(1−s) for all s ∉ {0, −2, −4, …} ∪ {1, 3, 5, …}
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a number field K with r₁ real and r₂ complex places and an ideal class 𝔎 of K, the partial zeta function ζ(𝔎, s), the sum of N(𝔞)^(−s) over the integral ideals 𝔞 in 𝔎, continues meromorphically to ℂ with a single simple pole at s = 1. The completed function Z(𝔎, s) = |d_K|^(s/2) Γ_ℝ(s)^(r₁) Γ_ℂ(s)^(r₂) ζ(𝔎, s) satisfies Z(𝔎, s) = Z(𝔎′, 1 − s), where 𝔎𝔎′ is the class of the different of K. The reference is J. Neukirch, Algebraic Number Theory, Springer 1999, Chapter VII, §5.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only totally real fields, so its gamma factor is Γ_ℝ(s) raised to the degree of F, while the published theorem holds for every number field and carries a factor Γ_ℂ(s) for each complex place.
- The Lean text asserts the identity only for s outside {0, −2, −4, …} and {1, 3, 5, …}, which keeps it away from the poles of the gamma factors, where Mathlib gives Gamma the value 0, and from the free values Z(1) and Z′(1), while the published identity holds between meromorphic functions, and the identity theorem makes the two forms equivalent.
- The Lean text says nothing about the simple pole of the partial zeta function at s = 1 or its residue, which the published theorem also determines.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The dossier's definitions of the partial zeta function and of d_F match the classical objects, the class relation C·C′ = [𝔡] is the classical one, and the only excluded points are the poles of the Gamma factors.

### 12, `DefQuatExists`

The proposition is `UpperTheory.V.Published.DefQuatExists`. Its vocabulary has 2 definitions of the project, and the proof of the theorem `UpperTheory.V.Af.defQuatExists` that states it rests on 357 declarations.

For every totally real number field F whose degree over ℚ is even, the text claims that the structure type DefQuat F has an element. Such an element consists of a division ring D that is a central F-algebra of dimension 4, so a quaternion division algebra over F, such that ℝ ⊗_F D has no zero divisors for every ring embedding τ of F into ℝ. It also contains an F-algebra map j_f from D to the 2×2 matrices over the finite adele ring 𝔸_{F,f} whose 𝔸_{F,f}-linear extension 𝔸_{F,f} ⊗_F D → M₂(𝔸_{F,f}) is bijective, and for each infinite place v a ring map from D to M₂(ℂ) that sends each x in F to the scalar matrix of its image under the complex embedding of v. The condition on ℝ ⊗_F D says that D is ramified at every real place, and the condition on j_f says that D splits at every finite place.

```
∀ F totally real with dim_ℚ F even, ∃ D central division F-algebra with dim_F D = 4, ℝ ⊗_{F,τ} D ≅ ℍ for every real embedding τ, 𝔸_{F,f} ⊗_F D ≅ M₂(𝔸_{F,f}), and ring maps D → M₂(ℂ) over each infinite place
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a number field F and a finite set S of real and finite places of F, there is a quaternion algebra over F ramified exactly at S if and only if S has even cardinality, and this algebra is unique up to isomorphism. For a totally real field of even degree, the set of all real places therefore gives a totally definite quaternion algebra that splits at every finite place. The reference is J. Voight, Quaternion Algebras, Graduate Texts in Mathematics 288, Springer 2021, Chapter 14.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text takes only totally real fields of even degree and only the ramification set made of all real places, while the published theorem gives a quaternion algebra over any number field for any finite set of real and finite places of even size.
- The Lean text claims existence only and leaves out the uniqueness of the algebra up to isomorphism and the converse that a field of odd degree has no quaternion algebra ramified exactly at its real places.
- The Lean text writes ramification at every real place as the absence of zero divisors in ℝ ⊗_F D for each real embedding, and splitting at every finite place as one bijective map from 𝔸_f ⊗_F D onto M₂(𝔸_f), and both encodings are equivalent to the usual local conditions.
- The structure DefQuat also carries, for each infinite place, a ring map from D into M₂(ℂ) that sends each element of F to the scalar matrix of its image under that place, and every quaternion algebra has such maps, so they add no condition.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Each field of the structure translates directly into a standard condition on a quaternion algebra, and the existence follows from the classification of quaternion algebras by their ramification sets.

### 13, `CanonicalExtensionRankOne`

The proposition is `GlobalTheory.Published.CanonicalExtensionRankOne`. Its vocabulary has 3 definitions of the project, and the proof of the theorem `GlobalTheory.Published.canonicalExtensionRankOne_holds` that states it rests on 42 declarations.

Take any n, an open set U ⊆ ℂⁿ, a set S of coordinate indices, functions a₁, …, aₙ on ℂⁿ and a function f on ℂⁿ, and write U° for the set of points of U whose coordinates z_i with i ∈ S are all nonzero. The text assumes that every a_i is holomorphic on U, that a_i vanishes on U ∩ {z_i = 0} for each i ∈ S, and that f is holomorphic and nowhere zero on U° and satisfies there z_i ∂f/∂z_i + a_i f = 0 for i ∈ S and ∂f/∂z_i + a_i f = 0 for i ∉ S. It claims that some function F agrees with f on U°, is holomorphic and nowhere zero on all of U and satisfies the same equations on U, and that every function continuous on U that agrees with f on U° agrees with F on U. Geometrically, f is a nowhere vanishing flat section, off the divisor D = ⋃_{i∈S} {z_i = 0}, of the logarithmic connection d + Σ_{i∈S} a_i dz_i/z_i + Σ_{i∉S} a_i dz_i on the trivial line bundle, the vanishing of a_i on {z_i = 0} says that the residues of this connection along D are zero, and the claim is that the flat section extends across D.

```
U ⊆ ℂⁿ open, D = ⋃_{i∈S} {z_i = 0}, a_i ∈ 𝒪(U) with a_i = 0 on D_i for i ∈ S, f ∈ 𝒪(U∖D)^× with z_i ∂_i f + a_i f = 0 (i ∈ S) and ∂_i f + a_i f = 0 (i ∉ S) on U∖D ⇒ ∃ F ∈ 𝒪(U)^× with F = f on U∖D, the same equations on U, and G = F on U for every continuous G on U with G = f on U∖D
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let X be a complex manifold, D ⊂ X a divisor with normal crossings and (V, ∇) a holomorphic vector bundle with integrable connection on X∖D. For a chosen set of representatives of ℂ/ℤ, for instance the numbers with real part in [0, 1), the pair (V, ∇) extends to a vector bundle on X with a connection having logarithmic poles along D whose residues have eigenvalues in that set, and this extension is unique up to a unique isomorphism that is the identity on X∖D. The reference is P. Deligne, Équations différentielles à points singuliers réguliers, Lecture Notes in Mathematics 163, Springer 1970, Chapter II, Proposition 5.4.

The first reader takes the proposition for a special case and the second reader for a different statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text works on an open subset U of ℂⁿ whose divisor is a union of coordinate hyperplanes, while the published theorem works on any complex manifold with a normal crossing divisor.
- The Lean text treats only the trivial line bundle with the connection d + Σ_{i∈S} a_i dz_i/z_i + Σ_{i∉S} a_i dz_i, while the published theorem treats vector bundles of any rank.
- The Lean text assumes that each a_i with i in S vanishes on U ∩ {z_i = 0}, so every residue is zero and a_i/z_i is holomorphic, which means that the connection has no actual pole along the divisor.
- The Lean text assumes a nowhere vanishing flat section f on the complement of the divisor, so the local system there is trivial, while the published theorem starts from any local system.
- The Lean text concludes only that this flat section extends to a nowhere vanishing flat section F on U, which follows from the uniqueness half of the published theorem, and it states nothing about the existence of an extension.
- The Lean text adds that every function continuous on U that agrees with f off the divisor equals F on U, which follows at once from the density of the complement of the divisor in U.

The check gives this reason for its judgement. I judge it weaker because the Lean claim follows from the uniqueness half of Deligne's theorem applied to a zero-residue extension of a trivial rank-one local system, yet it is no instance of the theorem's statement, since it asserts no existence of an extension and its hypotheses exclude every case in which the canonical extension differs from the naive one.

On emptiness the check wrote this. None found, although the hypothesis that each a_i with i in S vanishes on its hyperplane makes the connection holomorphic across the divisor, so the claim reduces to extending a flat section of a holomorphic connection over small polydiscs.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean text is true and fits the case of the canonical extension with zero residues and trivial monodromy, but tying it to Deligne's proposition is my reading of the name rather than an exact match of statements.

### 14, `CuspidalExists`

The proposition is `GlobalTheory.Published.CuspidalExists`. Its vocabulary has 3 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds` that states it rests on 403 declarations.

For every finite field k and every natural number n, the text claims that there are a dimension d and a representation ρ of GL_{n+1}(k) on ℂ^d that is irreducible and cuspidal. The project defines cuspidal by asking, for every monotone and nonconstant function b from the index set {0, …, n} to ℕ, that the only vector fixed by every u ∈ GL_{n+1}(k) with (u − 1)_{ij} = 0 whenever b_j ≤ b_i is the zero vector. For monotone b these elements u form the unipotent radical N_P of the standard parabolic subgroup P whose diagonal blocks are the level sets of b, and the nonconstant b give exactly the proper standard parabolic subgroups. The definition therefore says that ρ has no nonzero N_P-invariant vector for any proper standard parabolic subgroup P.

```
∀ k finite field, ∀ n ∈ ℕ, ∃ d and an irreducible ρ ∈ Hom(GL_{n+1}(k), GL_d(ℂ)) with (ℂ^d)^{N_P} = 0 for every proper standard parabolic subgroup P = M_P N_P of GL_{n+1}
```

The theorem that the name points to, as the first reader states it from its own knowledge. For every finite field F_q and every n ≥ 1, the group GL_n(F_q) has irreducible complex cuspidal representations, those with no nonzero vector fixed by the unipotent radical of any proper parabolic subgroup. Green's character theory attaches such a representation to each Frobenius orbit of regular characters of F_{q^n}^×, and regular characters exist for every n. The reference is J. A. Green, The characters of the finite general linear groups, Transactions of the American Mathematical Society 80, 1955.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean definition of cuspidal tests only the unipotent radicals of the proper standard parabolic subgroups, one for each monotone and nonconstant block function b, and this agrees with the usual definition because every parabolic subgroup is conjugate to a standard one.

On emptiness the check wrote this. None found, and for n = 0 the cuspidality condition holds for every representation because every function on a one-element index set is constant, which matches the convention that every irreducible representation of GL₁ is cuspidal.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The project's unipotent radicals are exactly those of the proper standard parabolic subgroups, and the existence of irreducible cuspidal representations of GL_n(F_q) for every n is a standard result.

### 15, `FinitenessOfHermitianClasses`

The proposition is `GlobalTheory.Published.FinitenessOfHermitianClasses`. Its vocabulary has 3 definitions of the project, and the proof of the theorem `GlobalTheory.Published.finitenessOfHermitianClasses_holds` that states it rests on 25 declarations.

Fix a CM field E with complex conjugation x ↦ x̄, a number r, an r×r matrix G over E with G_ba = Ḡ_ab and det G ≠ 0, a nonzero fractional ideal c, a nonzero integral ideal 𝔪 and a finite index set ι, and let h(y, z) = Σ_{a,b} y_a G_ab z̄_b be the Hermitian form of G on E^r. The text considers any set 𝓛 of pairs (L, x) where L is an O_E-lattice in E^r, meaning a finitely generated O_E-submodule that spans E^r, and x = (x_i)_{i∈ι} is a family of vectors of L, and it assumes that for every pair the set {y ∈ E^r | h(y, z) ∈ O_E for all z ∈ L} equals cL. It claims that 𝓛 has a finite subset S such that every (L, x) in 𝓛 is carried to some (L′, x′) in S by a γ ∈ GL_r(E) that preserves h, maps L onto L′ and satisfies γx_i ≡ x′_i modulo 𝔪L′ for every i.

```
E CM, G = Ḡᵀ ∈ GL_r(E), c ≠ 0, 𝔪 ≠ 0, ι finite, 𝓛 ⊆ {(L, x) | L lattice in E^r with L^# = cL, x ∈ L^ι} ⇒ ∃ S ⊆ 𝓛 finite, ∀ (L, x) ∈ 𝓛, ∃ (L′, x′) ∈ S, ∃ γ ∈ U(G)(E) with γL = L′ and γx_i ≡ x′_i mod 𝔪L′ for all i
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a reductive group 𝐆 over a number field F and an open compact subgroup K of 𝐆(𝔸_f), the double coset space 𝐆(F)∖𝐆(𝔸_f)/K is finite. Applied to the unitary group of a Hermitian space over a CM field, this says that every genus of Hermitian lattices, also with a level structure, contains finitely many isometry classes, and the local classification of Hermitian lattices shows that the lattices with a fixed dual relation L^# = cL form finitely many genera. The reference is A. Borel, Some finiteness properties of adele groups over number fields, Publications Mathématiques de l'IHÉS 16, 1963.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text concerns only Hermitian forms over CM fields with their complex conjugation, while Borel's finiteness theorem holds for every reductive group over a number field and the finiteness of Hermitian class numbers holds over every quadratic extension of number fields.
- The Lean family 𝓛 is cut out by the dual condition L^# = cL for one fixed fractional ideal c, measured with the O_E-valued form h_G itself, and such a family can meet several genera, so the Lean claim also needs the finiteness of the number of local isometry classes of such lattices.
- The Lean text adds a level structure, a finite family of vectors of L compared modulo 𝔪L, which corresponds to a smaller open compact subgroup and adds only finitely many choices per class because L/𝔪L is finite.
- The Lean text takes the representatives from the given set 𝓛, which is equivalent to the finiteness of the classes that 𝓛 meets.

On emptiness the check wrote this. None found, since the identity matrix with c = O_E and the lattice O_E^r meets every hypothesis.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean claim is true and follows from Borel's finiteness theorem together with the local finiteness of genera, but it is a corollary of that theorem rather than a published statement of the same shape.

### 16, `HermitianLocalGlobal`

The proposition is `GlobalTheory.Published.HermitianLocalGlobal`. Its vocabulary has 3 definitions of the project, and the proof of the theorem `PositivityTheory.Stage1.PM.hermitianLocalGlobal` that states it rests on 303 declarations.

The text is the conjunction of a local claim and a global claim, and in both a nonsingular matrix G′ is called congruent to G when G′ = Pᵀ G P̄ for some invertible P, with the bar standing for the nontrivial automorphism. The local claim says that for every nonarchimedean local field K with 2 ≠ 0, every quadratic extension L of K with a nontrivial K-automorphism σ, and all nonsingular r×r matrices G, G′ over L with σ(G_ab) = G_ba and σ(G′_ab) = G′_ba, the matrix G′ is congruent to G if and only if det G / det G′ equals x·σ(x) for some x ∈ L. The global claim says that for every CM field E with maximal real subfield F and all nonsingular Hermitian r×r matrices G, G′ over E, if G′ is congruent to G over F_v ⊗_F E for every finite place v of F, with an invertible P over that ring, and if for every embedding τ of E into ℂ the complex Hermitian matrix G′^τ equals Qᵀ G^τ Q̄ for some invertible complex Q, then G′ is congruent to G over E.

```
(∀ K nonarchimedean local with 2 ≠ 0, ∀ L/K quadratic with Gal(L/K) = {1, σ}, ∀ nonsingular σ-Hermitian G, G′ ∈ M_r(L), G′ ≅ G ⇔ det G / det G′ ∈ N_{L/K}(L^×)) ∧ (∀ E CM with F = E⁺, ∀ nonsingular Hermitian G, G′ ∈ M_r(E), [G′ ≅ G over F_v ⊗_F E for all finite v and G′^τ ≅ G^τ over ℂ for all τ] ⇒ G′ ≅ G over E), where G′ ≅ G means G′ = Pᵀ G P̄ for an invertible P
```

The theorem that the name points to, as the first reader states it from its own knowledge. Over a nonarchimedean local field K of characteristic different from 2 and a quadratic extension L of K, two nondegenerate Hermitian forms are isometric if and only if they have the same dimension and their determinants agree modulo norms from L. Landherr's theorem says that two nondegenerate Hermitian forms over a quadratic extension of number fields are isometric if and only if they are isometric at every place of the base field, so they are classified by dimension, determinant and the signatures at the real places that do not split. The reference is W. Scharlau, Quadratic and Hermitian Forms, Grundlehren der mathematischen Wissenschaften 270, Springer 1985, Chapter 10.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The global part is stated only for a CM field over its maximal real subfield, while Landherr's Hasse principle holds for every quadratic extension of number fields.
- The global part states only the direction from local congruence to global congruence and leaves out the easy converse and the resulting classification by dimension, determinant and signatures.
- The archimedean condition is written as a congruence G′^τ = Qᵀ G^τ Q̄ over ℂ for each embedding τ of E, which by Sylvester's law of inertia amounts to equal signatures at every real place of the maximal real subfield.
- The finite local conditions are written over F_v ⊗_F E with a matrix P of unit determinant, so a split place enters through F_v × F_v, where Hermitian forms of equal rank are always congruent.
- The local part covers every nonarchimedean local field with 2 ≠ 0, which includes the local fields of odd positive characteristic, where the same classification by determinant holds.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Both parts translate directly into the standard local classification and Landherr's theorem, and the restriction to CM fields is the only narrowing.

### 17, `IdealInvariantsOneOrbitSt`

The proposition is `GlobalTheory.Published.IdealInvariantsOneOrbitSt`. Its vocabulary has 3 definitions of the project, and the proof of the theorem `PositivityTheory.Prw.idealInvariantsOneOrbitSt_holds` that states it rests on 6,593 declarations.

For every imaginary quadratic field K, written as a totally complex number field of degree 2 with a chosen embedding of K into ℂ, every nonzero fractional ideal 𝔞 of O_K and every lattice Λ ⊂ ℂ given by a period pair whose point set is the image of 𝔞, the text makes two claims about the j-invariant of the curve y² = x³ − (g₂(Λ)/4)x − g₃(Λ)/4. The first claim is that j(Λ) = 1728 g₂³/(g₂³ − 27g₃²) is algebraic over K. The second claim is that the orbit of j(Λ) under all field automorphisms of ℂ that fix K equals the set of j-invariants of all lattices that are images of nonzero fractional ideals of O_K. Mathlib's j-invariant presupposes that the discriminant g₂³ − 27g₃² is invertible, and the dossier does not show the instance that supplies this, but the discriminant of a lattice is never zero, so the Lean j agrees with the classical one.

```
K imaginary quadratic, K ↪ ℂ, 𝔞 a nonzero fractional ideal of O_K, Λ = 𝔞 ⊂ ℂ ⇒ j(Λ) algebraic over K and {σ(j(Λ)) | σ ∈ Aut(ℂ/K)} = {j(𝔟) | 𝔟 a nonzero fractional ideal of O_K}
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be an imaginary quadratic field and E an elliptic curve over ℂ with endomorphism ring O_K, for example ℂ/𝔞 for a fractional ideal 𝔞 of O_K. Then j(E) is an algebraic integer, K(j(E)) is the Hilbert class field of K, the degree of K(j(E)) over K is the class number h_K, and the conjugates of j(E) over K are exactly the numbers j(ℂ/𝔟) for 𝔟 running over the ideal classes of K. The reference is J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic Curves, Graduate Texts in Mathematics 151, Springer 1994, Chapter II, Theorems 4.3 and 6.1.

The first reader takes the proposition for a weaker statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text claims only that j(𝔞) is algebraic over K and leaves out that j(𝔞) is an algebraic integer and that K(j(𝔞)) is the Hilbert class field of K, which are separate parts of the main theorem of complex multiplication.
- The Lean text describes the conjugates of j(𝔞) as its orbit under the automorphisms of ℂ over K instead of under Gal(K̄/K), which gives the same set for an algebraic number because every K-embedding of K(j(𝔞)) into ℂ extends to an automorphism of ℂ.
- The Lean set idealInvariants K runs over all invertible fractional ideals rather than over representatives of the ideal classes, which gives the same set because ideals in one class give homothetic lattices with the same j-invariant.
- The Lean curve y² = x³ − (g₂/4)x − g₃/4 is isomorphic to y² = 4x³ − g₂x − g₃, and its j-invariant is the classical 1728 g₂³/(g₂³ − 27g₃²).

The check gives this reason for its judgement. I judge it the same because the name and the Lean text both target the statement that the j-invariants of the ideal classes of K form one Galois orbit over K, which the Lean text states exactly, while integrality and the Hilbert class field, on which A bases its verdict of weaker, are separate parts of the main theorem of complex multiplication.

The check found no emptiness.

The check found these errors in the first reader's account of the Lean text, and the account above is printed as the reader wrote it.

- A says that the Lean text does not claim that the degree of K(j(𝔞)) over K equals the class number, but the Lean equality MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j = idealInvariants K fixes that degree as the number of distinct values in idealInvariants K, which is the class number because ideals give the same j-invariant exactly when they lie in the same class.

The first reader's confidence is high. The dossier's definitions give the standard lattice j-invariant and the standard set of j-invariants with complex multiplication by O_K, and the orbit claim is part (c) of Silverman's Theorem II.4.3.

### 18, `StoneVonNeumann`

The proposition is `GlobalTheory.Published.StoneVonNeumann`. Its vocabulary has 3 definitions of the project, and the proof of the theorem `PositivityTheory.Stage1.PM.stoneVonNeumann` that states it rests on 49 declarations.

Fix a nonarchimedean local field F with 2 ≠ 0, a finite-dimensional F-vector space W with its natural topology, a nondegenerate alternating bilinear form B on W and a continuous nontrivial additive character ψ of F with values in ℂ^×. The text makes two claims about the Heisenberg group H = W × F with product (w, t)(w′, t′) = (w + w′, t + t′ + B(w, w′)/2) and the product topology. The first claim is that some complex representation of H is smooth, meaning that every vector has an open stabiliser, is algebraically irreducible and has central character ψ, meaning that (0, t) acts as multiplication by ψ(t). The second claim is that any two such representations are isomorphic.

```
∀ F nonarchimedean local with 2 ≠ 0, ∀ (W, B) finite-dimensional symplectic over F, ∀ ψ nontrivial continuous character of F, ∃! (up to isomorphism) smooth irreducible ρ of H(W, B) with ρ(0, t) = ψ(t)·id
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let F be a nonarchimedean local field of characteristic different from 2, W a symplectic space over F and H(W) its Heisenberg group. For each nontrivial character ψ of F there is, up to isomorphism, exactly one smooth irreducible representation of H(W) with central character ψ, and it is admissible and realised by the Schrödinger model. The reference is C. Mœglin, M.-F. Vignéras and J.-L. Waldspurger, Correspondances de Howe sur un corps p-adique, Lecture Notes in Mathematics 1291, Springer 1987, Chapter 2.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text states the smooth version over a nonarchimedean local field with 2 ≠ 0, which is the theorem in Mœglin, Vignéras and Waldspurger, and not the original theorem of Stone and von Neumann about unitary representations of the real Heisenberg group on Hilbert spaces.
- The Lean text allows any continuous nontrivial character ψ of F with complex values, which agrees with the unitary characters of the published theorem because F is a union of compact open subgroups, so every continuous character of F is unitary.
- The Lean text leaves out the admissibility of the representation and its explicit Schrödinger model.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The project's Heisenberg group, smoothness condition and central character condition are the standard ones, and the existence and uniqueness claims match the p-adic theorem.

### 19, `AbelianUnobstructed`

The proposition is `GlobalTheory.Published.AbelianUnobstructed`. Its vocabulary has 4 definitions of the project, and the proof of the theorem `GlobalTheory.UnobTop.abelianUnobstructed` that states it rests on 5,678 declarations.

For every commutative ring R with an ideal I such that I² = 0, every commutative ring R₀ with a surjective ring map π from R to R₀ whose kernel is I, and every group scheme A₀ over Spec R₀ that is an abelian scheme, the text claims that there are a group scheme A over Spec R and a morphism i from A₀ to A with three properties. The square formed by i, the two structure maps and Spec π is a pullback, so A₀ is the base change of A to Spec R₀, the map i respects the group laws on points with values in every scheme over Spec R₀, and A is an abelian scheme. The project defines an abelian scheme as a group object in schemes over the base that is commutative, smooth, proper and geometrically connected. In words, every abelian scheme over R₀ lifts to an abelian scheme over the square-zero thickening R.

```
∀ R, ∀ I ⊆ R with I² = 0, R₀ = R/I, ∀ A₀ abelian scheme over Spec R₀, ∃ A abelian scheme over Spec R with A ×_{Spec R} Spec R₀ ≅ A₀ as group schemes
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let R be a ring, I ⊆ R a nilpotent ideal and A₀ an abelian scheme over R/I. Then there is an abelian scheme A over R with A ×_{Spec R} Spec(R/I) ≅ A₀, so the deformation theory of abelian schemes over affine bases is unobstructed. The reference is F. Oort, Finite group schemes, local moduli for abelian varieties, and lifting problems, Compositio Mathematica 23, 1971, where the result is credited to Grothendieck.

The first reader takes the proposition for a special case and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text assumes I² = 0, while some published versions allow any nilpotent ideal, and the nilpotent case follows from the square-zero case by lifting along the quotients R/I^(k+1) → R/I^k one step at a time.
- The Lean definition of an abelian scheme lists commutativity as an axiom, which for smooth proper group schemes with geometrically connected fibres follows from the other conditions.
- The Lean text expresses that A₀ is the base change of A as a group scheme by a pullback square together with the compatibility of i with the group laws on points, which is equivalent to an isomorphism A ×_{Spec R} Spec R₀ ≅ A₀ of group schemes.
- The Lean text asserts only the existence of a lift and says nothing about the set of all lifts.

The check gives this reason for its judgement. I judge it the same because unobstructedness is classically stated for square-zero thickenings, and the version for a nilpotent ideal, on which A bases its verdict of special case, follows from the square-zero version by lifting one step at a time, so the two forms are equivalent.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean definitions match the usual notions of abelian scheme and of base change of group schemes, but I am less certain of the exact form and source of Grothendieck's lifting theorem over arbitrary affine bases.

### 20, `DixmierMalliavinFactorisation`

The proposition is `GlobalTheory.Published.DixmierMalliavinFactorisation`. Its vocabulary has 4 definitions of the project, and the proof of the theorem `GlobalTheory.dixmierMalliavinFactorisation_fromLibrary` that states it rests on 266 declarations.

Fix a topological group G with its Borel σ-algebra, a finite index set n, a group homomorphism ι from G into the n×n complex matrices that is a closed embedding of G into GL_n(ℂ), a left Haar measure μ, a neighbourhood V of the identity and a function f in CcMat ι. The project defines CcMat ι as the space of compactly supported functions on G of the form Φ∘ι with Φ a real-smooth function on the matrix space, which for this closed linear group is the space C_c^∞(G). The text claims that there are N and functions g₁, …, g_N, h₁, …, h_N in CcMat ι such that the closed support of each g_i lies in V, the closed support of each h_i lies in the closed support of f, and f = Σ g_i * h_i with (g * h)(y) = ∫ g(x) h(x⁻¹y) dμ(x).

```
G ≅ closed subgroup of GL_n(ℂ), μ left Haar measure, V ∈ 𝒩(1), f ∈ C_c^∞(G) ⇒ ∃ N, g_i, h_i ∈ C_c^∞(G) with supp g_i ⊆ V, supp h_i ⊆ supp f and f = Σ_{i=1}^N g_i * h_i
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a real Lie group G, every function in C_c^∞(G) is a finite sum of convolutions g * h with g, h ∈ C_c^∞(G), and for a continuous representation of G on a Fréchet space every smooth vector is a finite sum of vectors π(g)v with g ∈ C_c^∞(G) and v smooth. The reference is J. Dixmier and P. Malliavin, Factorisations de fonctions et de vecteurs indéfiniment différentiables, Bulletin des Sciences Mathématiques 102, 1978.

The first reader takes the proposition for a stronger statement and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text covers only groups with a closed embedding into GL_n(ℂ), while the published theorem covers every Lie group, including groups with no faithful finite-dimensional representation such as the universal cover of SL₂(ℝ).
- The Lean text describes the smooth functions on G as the compactly supported functions of the form Φ∘ι with Φ real-smooth on the matrix space, which for a closed subgroup of GL_n(ℂ) gives exactly the compactly supported smooth functions on the Lie group.
- The Lean text requires each g_i to have closed support in a prescribed neighbourhood V of the identity, a refinement that also follows from the bare theorem by a partition of unity and a left translation of each term.
- The Lean text requires each h_i to have closed support inside the closed support of f, which the bare published statement does not mention but the Dixmier–Malliavin construction yields, because there the h_i arise from f through differential operators that do not enlarge supports.
- The Lean text leaves out the version for smooth vectors of Fréchet representations.

The check gives this reason for its judgement. I judge it a special case because the Lean text covers only closed linear groups, so it cannot be stronger than a theorem for all Lie groups as A says, and its two support conditions are supplied by a partition of unity and by the Dixmier–Malliavin construction itself.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The core factorisation is the Dixmier–Malliavin theorem, but I am not certain whether the published statement already includes the two support conditions, which decides between stronger and special case, and the Lean text is in any case narrower in its class of groups.

### 21, `IrreducibleAdmissibleGL`

The proposition is `GlobalTheory.Published.IrreducibleAdmissibleGL`. Its vocabulary has 4 definitions of the project, and the proof of the theorem `GlobalTheory.FourClauses.irreducibleAdmissibleGL` that states it rests on 1,431 declarations.

For every non-archimedean local field k with its valuation topology, every natural number n and every complex vector space V carrying a representation π of the group GL_n(k), the text assumes that π is smooth and irreducible. Smooth means that the stabilizer of every vector of V is an open subset of GL_n(k), where GL_n(k) carries the topology that Mathlib gives to units of the matrix ring, which is the usual topology from the matrix entries. Irreducible is Mathlib's algebraic notion, so V is nonzero and has no invariant subspaces other than 0 and V. The conclusion is that π is admissible, which the project defines as smooth together with the condition that for every compact open subgroup K of GL_n(k) the space of K-fixed vectors is finite-dimensional over ℂ.

```
∀ k non-archimedean local field, ∀ n ∈ ℕ, ∀ (π, V) complex representation of GL_n(k), (π smooth ∧ π irreducible) ⇒ (π smooth ∧ ∀ K ≤ GL_n(k) compact open, dim_ℂ V^K < ∞)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Every irreducible smooth complex representation of GL_n(F), for F a non-archimedean local field, is admissible, and Bernstein extended the result to every reductive group over F. Reference I. N. Bernstein and A. V. Zelevinsky, Representations of the group GL(n,F) where F is a local non-archimedean field, Russian Mathematical Surveys 31, 1976.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The project's notions of smooth vector stabilizers, fixed vectors and admissibility agree with the textbook notions, and the topology on GL_n(k) is the standard one.

### 22, `MetaplecticRepresentation`

The proposition is `GlobalTheory.Published.MetaplecticRepresentation`. Its vocabulary has 4 definitions of the project, and the proof of the theorem `GlobalTheory.metaplecticRepresentation_holds` that states it rests on 313 declarations.

For every finite index set ι with n elements, the text asserts that there exist a topological group G, a group homomorphism pr from G to Mathlib's real symplectic group Sp(2n,ℝ) acting on ℝ^ι × ℝ^ι, a homomorphism Ω from G to the bounded operators on L²(ℝ^ι), a homomorphism ω from G to the continuous linear operators on the Schwartz space 𝓢(ℝ^ι), and a Schwartz function φ₀ with the properties listed next. The map pr is surjective, is a covering map and has a kernel of exactly two elements, every Ω(g) preserves the L² norm, g ↦ Ω(g)f is continuous for each f, Ω(g) agrees with ω(g) on Schwartz functions, and (g, φ) ↦ ω(g)φ is jointly continuous on G × 𝓢. Each ω(g) satisfies ω(g)ρ(w) = ρ(pr(g)w)ω(g) for the Heisenberg operators ρ(a,b)φ(x) = e^{2πi(x·b + a·b/2)}φ(x + a), and the nontrivial element of the kernel acts on 𝓢 as −1. The function φ₀ is the Gaussian e^{−π x·x}, and for every g the square of ⟨ω(g)φ₀, φ₀⟩ times det P(pr g) equals ⟨φ₀, φ₀⟩², where P(h) = ((A + D) + i(C − B))/2 for the blocks A, B, C, D of h. When pr(g) is orthogonal, ω(g)φ₀ = cφ₀ for some c with c² det P(pr g) = 1.

```
∀ finite ι, ∃ G topological group, ∃ pr ∈ Hom(G, Sp(2n,ℝ)) surjective covering with |ker pr| = 2, ∃ Ω ∈ Hom(G, U(L²(ℝⁿ))) strongly continuous, ∃ ω ∈ Hom(G, GL(𝓢(ℝⁿ))) jointly continuous with Ω(g)|_𝓢 = ω(g), ω(g)ρ(w)ω(g)⁻¹ = ρ(pr(g)w), ω(z) = −1 for 1 ≠ z ∈ ker pr, ⟨ω(g)φ₀,φ₀⟩² det P(pr g) = ⟨φ₀,φ₀⟩², and pr(g) ∈ O(2n) ⇒ ω(g)φ₀ = cφ₀ with c² det P(pr g) = 1, where φ₀(x) = e^{−π|x|²}
```

The theorem that the name points to, as the first reader states it from its own knowledge. The real symplectic group Sp(2n,ℝ) has a connected double cover Mp(2n,ℝ) that carries a unique strongly continuous unitary representation μ on L²(ℝⁿ) with μ(g)ρ(w)μ(g)⁻¹ = ρ(gw) for the Schrödinger representation ρ of the Heisenberg group, and μ does not factor through Sp(2n,ℝ). The operators μ(g) preserve the Schwartz space, the inverse image of the maximal compact subgroup U(n) acts on the Gaussian by a square root of the inverse determinant, and the Gaussian matrix coefficient is a square root of det P(g)⁻¹ up to the normalization of the Gaussian. Reference G. B. Folland, Harmonic Analysis in Phase Space, Annals of Mathematics Studies 122, 1989, Chapter 4.

The first reader takes the proposition for a weaker statement and the second reader for a stronger statement. The check takes it for a stronger statement.

The check confirmed these differences from the Lean text.

- The Lean text asserts only the existence of G, pr, Ω, ω and φ₀ and states no uniqueness of the representation.
- The Lean text does not name Mp(2n,ℝ) or state that G is connected and asks only for a topological group with a surjective covering homomorphism onto symplecticGroup ι ℝ whose kernel has two elements, although for nonempty ι the covariance and continuity clauses force G to be the connected double cover.
- The Lean text adds that each Ω g restricts on Schwartz functions to a continuous operator ω g of the Schwartz space and that (g, φ) ↦ ω g φ is jointly continuous, which are known properties of the metaplectic representation that its usual statement leaves out.
- The Lean text adds two Gaussian normalizations, namely that ⟨ω(g)φ₀, φ₀⟩² times det((A + D + i(C − B))/2) equals ⟨φ₀, φ₀⟩² and that every lift of an orthogonal element sends φ₀ to cφ₀ with c² det((A + D + i(C − B))/2) = 1, and both clauses fix only squares and so leave a sign free.
- The Lean text fixes the Heisenberg operators as ρ(a,b)φ(x) = e^{2πi(x·b + a·b/2)}φ(x + a), whose commutator form a·b′ − a′·b is preserved by Mathlib's symplectic group, so its convention is consistent with the matrix action act.
- The Lean text leaves out the splitting of the representation into its even and odd irreducible parts.

The check gives this reason for its judgement. The Lean text implies the Segal–Shale–Weil statement, a strongly continuous unitary representation of a double cover of Sp(2n,ℝ) that intertwines the Schrödinger operators and does not factor through Sp(2n,ℝ), and it adds the Schwartz-space and Gaussian clauses, while the uniqueness it omits follows from its own clauses by the Stone–von Neumann theorem and the perfectness of Mp(2n,ℝ), so I side with B.

The check found no emptiness.

The check found these errors in the first reader's account of the Lean text, and the account above is printed as the reader wrote it.

- A says that "its kernel clause together with ω(z) = −1 rules out the trivial double cover Sp(2n,ℝ) × ℤ/2", but these two clauses alone leave room for G = Sp(2n,ℝ) × ℤ/2 with ω(g, ε) = ε·U(g), and for nonempty ι the trivial cover is excluded by the covariance clause ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ) together with the continuity clauses, because Sp(2n,ℝ) itself has no continuous representation U that meets the covariance clause.

The first reader's confidence is medium. The clauses match the known properties of the metaplectic representation, which I checked for rotations and diagonal elements when n = 1, but the Lean text mixes core and auxiliary properties, so the choice between weaker and same depends on which published package one takes as the theorem.

### 23, `SiegelKlingen`

The proposition is `GlobalTheory.Published.SiegelKlingen`. Its vocabulary has 4 definitions of the project, and the proof of the theorem `PositivityTheory.Prw.siegelKlingen_holds` that states it rests on 302 declarations.

For every totally real number field F, every nonzero ideal 𝔣 of its ring of integers and every rational-valued function ε on ideals that takes equal values on ideals coprime to 𝔣 in the same narrow ray class modulo 𝔣, the text asserts that some function L on ℂ has two properties. L is holomorphic on ℂ ∖ {1} and, whenever Re s > 1, equals the unconditionally convergent sum of ε(I)N(I)^{−s} over all nonzero ideals I coprime to 𝔣. Moreover L(1 − k) is a rational number for every integer k ≥ 1. Two ideals I and J coprime to 𝔣 lie in the same narrow ray class when (a)I = (b)J for nonzero totally positive integers a, b with a ≡ b ≡ 1 mod 𝔣.

```
∀ F totally real, ∀ 𝔣 ≠ 0, ∀ ε ∈ ℚ^{Cl⁺(𝔣)}, ∃ L holomorphic on ℂ ∖ {1} with L(s) = Σ_{I+𝔣=1} ε(I) N(I)^{−s} for Re s > 1 and L(1 − k) ∈ ℚ for all k ≥ 1
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a totally real number field F, a nonzero integral ideal 𝔣 and a narrow ray class C modulo 𝔣, the partial zeta function ζ(C, s), the sum of N(I)^{−s} over the integral ideals I in C, continues meromorphically to ℂ with at most a simple pole at s = 1, and ζ(C, 1 − k) is rational for every integer k ≥ 1. Klingen proved the case of the Dedekind zeta function in 1962 and Siegel the case of partial zeta functions. Reference C. L. Siegel, Über die Fourierschen Koeffizienten von Modulformen, Nachrichten der Akademie der Wissenschaften in Göttingen, 1970.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text treats every ℚ-valued function ε that is constant on the narrow ray classes of ideals coprime to 𝔣 in place of a single partial zeta function, which is equivalent because the indicator of one class is such an ε and the values are linear in ε.
- The Lean text asks only that L be complex differentiable on ℂ ∖ {1} and says nothing about the pole at 1, which leaves the values L(1 − k) unaffected because the identity theorem makes L unique on the connected set ℂ ∖ {1}.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The ray relation, the coprimality condition and the Dirichlet series in the dossier match the standard narrow ray class partial zeta functions, and uniqueness of continuation makes the existential form equivalent to the published one.

### 24, `ComplexMultiplicationJSt`

The proposition is `GlobalTheory.Published.ComplexMultiplicationJSt`. Its vocabulary has 5 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.Published.complexMultiplicationJ` that states it rests on 6,574 declarations.

For every imaginary quadratic field K, given as a totally complex number field of degree 2 over ℚ with a fixed embedding into ℂ, the text asserts that there are a subfield H of ℂ containing K and a group isomorphism art from the ideal class group of K onto Gal(H/K) with four properties. H is a finite abelian extension of K in which every nonzero prime is unramified and contains every other such extension inside ℂ, and art sends the class of every nonzero prime 𝔭 to an arithmetic Frobenius element at every prime of H above 𝔭. For every invertible fractional ideal 𝔞 and every lattice L in ℂ equal to the image of 𝔞, the field K(j(L)) equals H, where j(L) = 1728 g₂³/(g₂³ − 27g₃²) is the j-invariant of the curve y² = x³ − (g₂/4)x − g₃/4. For all fractional ideals 𝔞 and 𝔟 and lattices L and L′ equal to the images of 𝔞 and 𝔟⁻¹𝔞, the automorphism art([𝔟]) sends j(L) to j(L′).

```
∀ K ⊂ ℂ imaginary quadratic, ∃ H ⊂ ℂ, ∃ art ∈ Iso(Cl(K), Gal(H/K)), H = Hilbert class field of K ∧ art([𝔭]) = Frob_𝔭 ∧ ∀ 𝔞, K(j(𝔞)) = H ∧ ∀ 𝔞 𝔟, art([𝔟])(j(𝔞)) = j(𝔟⁻¹𝔞)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be an imaginary quadratic field with Hilbert class field H and Artin isomorphism 𝔟 ↦ σ_𝔟 from Cl(K) onto Gal(H/K). For every fractional ideal 𝔞 of K the number j(𝔞) is algebraic, H = K(j(𝔞)), and j(𝔞)^{σ_𝔟} = j(𝔟⁻¹𝔞) for every fractional ideal 𝔟. Reference J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic Curves, 1994, Chapter II, Section 4.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text asserts the existence of the Hilbert class field H inside ℂ and of an isomorphism from the class group onto Gal(H/K) that sends the classes of primes to Frobenius elements, which the published theorem takes from class field theory.
- The project's IsUnramifiedAbelian asks for unramifiedness only at the nonzero primes of 𝓞 M, which agrees with the usual Hilbert class field because the imaginary quadratic field K has no real places.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Each project definition, namely the Hilbert class field, the Artin map through arithmetic Frobenius, the ideal lattice and the Weierstrass model built from g₂ and g₃, matches the standard notion, and the action formula is the standard one.

### 25, `HilbertClassFieldJ`

The proposition is `GlobalTheory.Published.HilbertClassFieldJ`. Its vocabulary has 5 definitions of the project, and the proof of the theorem `GlobalTheory.Laid.hcfj_holds` that states it rests on 6,590 declarations.

For every imaginary quadratic field K with a fixed embedding into ℂ and every lattice L₀ equal to the image of the ring of integers 𝓞_K, the text asserts five statements about j₀ = j(L₀), the j-invariant of y² = x³ − (g₂/4)x − g₃/4. The field K(j₀) is the Hilbert class field of K in the project's sense, namely the largest finite abelian extension of K inside ℂ unramified at every nonzero prime, and its degree over K is the class number h_K. For fractional ideals 𝔞 and 𝔟 with lattices L and L′ equal to their images, j(L) = j(L′) holds exactly when 𝔞 and 𝔟 lie in the same ideal class. The set of j-invariants of all fractional-ideal lattices has exactly h_K elements and equals the set of images of j₀ under the K-automorphisms of K(j₀).

```
∀ K ⊂ ℂ imaginary quadratic, K(j(𝓞_K)) = H_K ∧ dim_K K(j(𝓞_K)) = h_K ∧ (j(𝔞) = j(𝔟) ⇔ [𝔞] = [𝔟]) ∧ #{j(𝔞)} = h_K ∧ Gal(K(j(𝓞_K))/K)·j(𝓞_K) = {j(𝔞)}
```

The theorem that the name points to, as the first reader states it from its own knowledge. For an imaginary quadratic field K, the field K(j(𝓞_K)) is the Hilbert class field of K and its degree over K equals the class number h_K. The values j(𝔞) for 𝔞 running over representatives of the h_K ideal classes are distinct and form the complete set of conjugates of j(𝓞_K) over K. Reference J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic Curves, 1994, Chapter II, Theorem 4.3.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text states the field and degree clauses only for the lattice of 𝓞_K, which is equivalent to the published form for every curve with complex multiplication by 𝓞_K because the conjugacy clause makes every j(𝔞) a conjugate of j(𝓞_K) over K and K(j(𝓞_K)) is normal over K.
- The Lean text does not state that j(𝓞_K) is an algebraic integer.
- The Lean text does not state that the degree of ℚ(j(𝓞_K)) over ℚ equals h_K, which follows from its degree clause over K because j(𝓞_K) is real, so that K(j(𝓞_K)) has degree 2 over ℚ(j(𝓞_K)).
- The project's notion of an unramified extension looks only at the nonzero primes, which is harmless because K has no real places.
- The Lean text gives the Galois conjugates of j(𝓞_K) only as a set and leaves the explicit Artin action on the values j(𝔞) out.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The clauses reproduce the standard statement item by item, and the project definitions match the usual notions.

### 26, `CMCurveGoodOutsidePrimeSt`

The proposition is `GlobalTheory.Published.CMCurveGoodOutsidePrimeSt`. Its vocabulary has 6 definitions of the project, and the proof of the theorem `GlobalTheory.Published.cmCurveGoodOutsidePrime` that states it rests on 7,348 declarations.

For every prime p with p ≡ 3 mod 4 and p > 3, the text asserts that there are a subfield F of ℂ that is a number field and a Weierstrass curve A over F with the properties listed next. A is nonsingular, F = ℚ(j(L)) for the lattice L of algebraic integers in K = ℚ(√−p), and the j-invariant of A equals j(L), so that A has complex multiplication by 𝓞_K over ℂ. At every prime v of 𝓞_F that does not contain p, some change of coordinates over F gives A good reduction at v. At every prime v of 𝓞_F, some change of coordinates gives a v-minimal model whose discriminant is −p³ times a v-adic unit, so the minimal discriminant ideal of A is (p³).

```
∀ p prime with p ≡ 3 (mod 4) and p > 3, ∃ F = ℚ(j(𝓞_{ℚ(√−p)})) ⊂ ℂ, ∃ A/F elliptic with j(A) = j(𝓞_{ℚ(√−p)}), A good at every v ∤ p, and minimal discriminant ideal 𝔇(A/F) = (−p³)
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a prime p > 3 with p ≡ 3 mod 4, let K = ℚ(√−p) and F = ℚ(j(𝓞_K)). Gross constructed an elliptic curve A(p) over F with complex multiplication by 𝓞_K, minimal discriminant (−p³) and good reduction at every prime not dividing p, and showed that it is a ℚ-curve, that is, isogenous over the Hilbert class field to all its Galois conjugates. Reference B. H. Gross, Arithmetic on Elliptic Curves with Complex Multiplication, Lecture Notes in Mathematics 776, 1980.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text asserts only the existence of such a curve and leaves out the uniqueness by which Gross characterizes A(p) and his further results, such as A(p) being isogenous to all its Galois conjugates.
- The Lean text records complex multiplication only through the equality of A.j with j(latticeCurve L) for the lattice of integers of ℚ(√−p), which over ℂ is equivalent to complex multiplication by 𝓞_K.
- HasMinimalDiscriminant fixes the discriminant only up to a unit of each local valuation ring, so the Lean text determines the minimal discriminant ideal (p³) and says nothing about a global model with discriminant exactly −p³.
- The clause HasGoodReductionOutside p A follows from the minimal-discriminant clause, because at a place v that does not contain p the local minimal model has discriminant −p³ times a unit, which is itself a unit.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The properties match Gross's curve, as the case p = 7 with F = ℚ and the curve y² + xy = x³ − x² − 2x − 1 of discriminant −7³ and j-invariant −3375 illustrates, but my memory of the exact form of Gross's statement, including any uniqueness claim, is not precise.

### 27, `ChebotarevDegreeOne`

The proposition is `GlobalTheory.Published.ChebotarevDegreeOne`. Its vocabulary has 6 definitions of the project, and the proof of the theorem `GlobalTheory.Published.chebotarevDegreeOne'` that states it rests on 236 declarations.

For every number field F with algebraic closure Ω, every finite Galois extension L of F inside Ω, every g ∈ Gal(L/F) and every finite set S of nonzero primes of 𝓞_F, the text asserts that there is a nonzero prime v of 𝓞_F outside S with residue degree 1 over ℚ. Moreover there is a valuation ring B of Ω lying over v whose inertia group in Gal(Ω/F) fixes L pointwise, so that v is unramified in L at the place below B. Finally some σ ∈ Gal(Ω/F) lies in the decomposition group of B, satisfies σ(x) ≡ x^{N(v)} modulo the maximal ideal of B for every x in B, and restricts to g on L.

```
∀ F number field, ∀ L/F finite Galois inside F̄, ∀ g ∈ Gal(L/F), ∀ S finite, ∃ v ∉ S with f(v|p) = 1, ∃ B | v in F̄ with I_B ⊆ Gal(F̄/L), ∃ σ = Frob_B ∈ Gal(F̄/F) with σ|_L = g
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a finite Galois extension L/F of number fields with group G and a conjugacy class C of G, the set of primes of F unramified in L whose Frobenius class is C has Dirichlet density, and in fact natural density, |C|/|G|. Reference J. Neukirch, Algebraic Number Theory, 1999, Chapter VII, Theorem 13.4.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text claims only that a suitable prime exists outside every finite set S, hence that there are infinitely many, and not that the primes with Frobenius class C have density |C|/|G|.
- The Lean text asks for primes of residue degree 1 over ℚ, which the density theorem also yields because the primes of higher residue degree have density zero.
- The Lean text makes g itself the Frobenius at a suitable place B above v, which the published theorem gives once the place above v is chosen within the conjugacy class.
- The Lean text describes places by valuation subrings of Ω and the inertia group and Frobenius by elements of Gal(Ω/F), and IsPlaceOver B v forces B to lie over the local ring of F at v, so this matches the usual description by primes of L.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The project's definitions of place, inertia group and Frobenius element agree with the usual ones, and the conclusion is a standard corollary of the density theorem.

### 28, `ChowFormExists`

The proposition is `GlobalTheory.Published.ChowFormExists`. Its vocabulary has 6 definitions of the project, and the proof of the theorem `GlobalTheory.Published.chowFormExists_holds` that states it rests on 295 declarations.

For every field k of characteristic zero, all natural numbers N and D, and every homogeneous ideal I of k[x_0, …, x_{N−1}] whose extension to k̄[x] is prime and for which k[x]/I has Krull dimension D + 1, the text asserts that a Chow form of I exists and is unique up to a nonzero factor in k. A Chow form here is a polynomial f over k in D + 1 blocks of N variables u_{i,j} that is homogeneous of degree d in each block, is irreducible over k̄, and vanishes at u ∈ k̄^{(D+1)×N} exactly when some nonzero point y of the zero set of I in k̄^N satisfies Σ_j u_{i,j}y_j = 0 for every i. The degree d is the floor of (deg P)! times the leading coefficient of the Hilbert polynomial P of k[x]/I, which is the degree of the projective variety V(I) of dimension D. Uniqueness means that every polynomial with these three properties equals cf for some nonzero c ∈ k.

```
∀ k with char k = 0, ∀ I ⊂ k[x_0..x_{N−1}] homogeneous with I·k̄[x] prime and dim k[x]/I = D + 1, ∃! up to k^× f ∈ k[u_{i,j}] (i ≤ D, j < N) multihomogeneous of degree deg V(I) in each u_i, irreducible over k̄, with f(u) = 0 ⇔ ∃ y ∈ V(I)(k̄) ∖ {0}, u_i·y = 0 for all i
```

The theorem that the name points to, as the first reader states it from its own knowledge. For an irreducible projective variety X ⊂ ℙ^{N−1} of dimension D and degree d, the (D + 1)-tuples of hyperplanes that meet X form an irreducible hypersurface in the product of dual spaces, cut out by an irreducible form that is multihomogeneous of degree d in each block and unique up to a scalar. When X is defined over a field k, the form can be taken with coefficients in k. Reference W.-L. Chow and B. L. van der Waerden, Zur algebraischen Geometrie IX. Über zugeordnete Formen und algebraische Systeme von algebraischen Mannigfaltigkeiten, Mathematische Annalen 113, 1937.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text assumes CharZero k, while the published theorem holds over every field.
- The Lean text treats only homogeneous ideals of k[x] that stay prime over the algebraic closure, which are the geometrically irreducible varieties defined over k, and its conclusion includes that the Chow form has coefficients in k.
- The Lean text takes the block degree from the Hilbert polynomial of k[x]/I as hilbertDegree I, which equals the usual degree of the variety.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The three defining clauses are the textbook characterization of the Chow form, and the Hilbert-polynomial normalization gives the usual degree.

### 29, `ChowFormIntExists`

The proposition is `GlobalTheory.Published.ChowFormIntExists`. Its vocabulary has 6 definitions of the project, and the proof of the theorem `GlobalTheory.Published.chowFormIntExists_holds` that states it rests on 289 declarations.

For every field k of characteristic zero, all natural numbers N and e, and every homogeneous prime ideal P of k[x_0, …, x_{N−1}] for which k[x]/P has Krull dimension e + 1, the text asserts that there is a polynomial f over k, unique up to a nonzero factor in k, with three properties. The polynomial f in e + 1 blocks of N variables is homogeneous of degree d in each block, where d is the floor of (deg Q)! times the leading coefficient of the Hilbert polynomial Q of k[x]/P. It is irreducible in k[u], and it vanishes at u ∈ k̄^{(e+1)×N} exactly when some nonzero point of the zero set of P in k̄^N lies on all e + 1 hyperplanes u_i. The ideal P need not stay prime after extension to k̄, so its zero set over k̄ may consist of several Galois-conjugate components.

```
∀ k with char k = 0, ∀ P ⊂ k[x_0..x_{N−1}] homogeneous prime with dim k[x]/P = e + 1, ∃! up to k^× f ∈ k[u_{i,j}] (i ≤ e, j < N) multihomogeneous of degree deg V(P) in each u_i, irreducible over k, with f(u) = 0 ⇔ ∃ y ∈ V(P)(k̄) ∖ {0}, u_i·y = 0 for all i
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a homogeneous prime ideal 𝔭 of k[x_0, …, x_n] of dimension r + 1 over a field k, there is a form F_𝔭 with coefficients in k, irreducible over k, multihomogeneous of degree deg 𝔭 in each of r + 1 blocks of variables and unique up to a factor in k^×, which vanishes exactly at the tuples of hyperplanes that meet the zero set of 𝔭 over k̄. Over k̄ this form is the product of the Chow forms of the conjugate components of that zero set. Reference Yu. V. Nesterenko and P. Philippon (editors), Introduction to Algebraic Independence Theory, Lecture Notes in Mathematics 1752, 2001.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text assumes CharZero k, while the Chow form of a homogeneous prime ideal exists over every field.
- The Lean text takes the block degree from the Hilbert polynomial of k[x]/P as hilbertDegree P, which equals the degree of P.
- The Lean text does not state that f factors over the algebraic closure into the Chow forms of the Galois-conjugate components of the zero set of P.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The clauses match the standard characterization of the Chow form of a prime ideal, but references differ on whether they state it only in characteristic zero, which decides between same and special case.

### 30, `RadfordShufflePolynomial`

The proposition is `GlobalTheory.Published.RadfordShufflePolynomial`. Its vocabulary has 6 definitions of the project, and the proof of the theorem `GlobalTheory.Published.radfordShufflePolynomial_holds` that states it rests on 59 declarations.

For every field K of characteristic zero and every linearly ordered set A, the text considers the shuffle algebra over K on the alphabet A, which is the vector space with basis all finite words over A, with the shuffle product and the empty word as unit, and the polynomial ring over K with one variable for each Lyndon word. A Lyndon word is a nonempty word that is strictly smaller in the lexicographic order than each of its proper nonempty suffixes. The text asserts that the K-algebra homomorphism sending the variable of each Lyndon word w to the word w itself is bijective.

```
∀ K with char K = 0, ∀ (A, <) totally ordered, the K-algebra map K[X_w | w Lyndon over A] → Sh_K(A), X_w ↦ w, is an isomorphism
```

The theorem that the name points to, as the first reader states it from its own knowledge. Over a field of characteristic zero, the shuffle algebra on a totally ordered alphabet is a polynomial algebra on the Lyndon words. Reference D. E. Radford, A natural ring basis for the shuffle algebra and an application to group schemes, Journal of Algebra 58, 1979.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The dossier's definitions of Lyndon word, shuffle product and shuffle algebra are the standard ones, and the map is the standard map from the polynomial ring on Lyndon words.

### 31, `ResolutionCharZero`

The proposition is `GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero`. Its vocabulary has 7 definitions of the project, and the proof of the theorem `PositivityTheory.Resplug.ResolutionBlowup.resolutionCharZero` that states it rests on 7,699 declarations.

For every field k of characteristic zero and every reduced scheme X with a morphism g to Spec k that is locally of finite type, quasi-compact and separated, the statement asserts that there are a scheme X' and a morphism s from X' to X with four properties. The morphism s is a finite composite of blowups, each defined by the universal property of blowing up an arbitrary quasi-coherent ideal sheaf on the previous scheme, with no condition on the centres. The composite of s with g is smooth, so X' is smooth over k, and s restricts to an isomorphism over the open locus where g is smooth. The reduced ideal sheaf of the preimage under s of the non-smooth locus of g is a strict normal crossings divisor, in the sense that near every point of X' it is generated on an affine neighbourhood by a product of some members of one regular system of parameters at that point.

```
∀ k with char k = 0, ∀ X reduced, separated and of finite type over k, ∃ s = π_1 ∘ ⋯ ∘ π_r from X' to X with each π_j a blowup along some ideal sheaf, X' smooth over k, s an isomorphism over X_sm, and (s^{-1}(X ∖ X_sm))_red an snc divisor
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let X be a reduced scheme of finite type over a field of characteristic zero. Then there is a finite sequence of blowups X' = X_r → ⋯ → X_0 = X along smooth centres lying over the singular locus such that X' is smooth, the composite is an isomorphism over the smooth locus of X, and the preimage of the singular locus is a divisor with simple normal crossings. Reference is H. Hironaka, Resolution of singularities of an algebraic variety over a field of characteristic zero I, II, Annals of Mathematics 79, 1964.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean statement lets each blowup in IsBlowupSeq have an arbitrary ideal sheaf as its centre, while Hironaka's theorem blows up smooth centres that lie over the singular locus.
- The Lean statement records no condition that a centre has simple normal crossings with the exceptional divisors of the earlier blowups, which the inductive form of the published theorem provides.
- The Lean statement adds the hypothesis that g is separated, which the general published versions for reduced schemes of finite type over a field of characteristic zero do not need.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Every clause of the Lean conclusion is a clause of the strong resolution theorem once the project's blowup and snc definitions are unwound, and the only change is that the smoothness of the centres is dropped.

### 32, `RayClassFieldSt`

The proposition is `GlobalTheory.Published.RayClassFieldSt`. Its vocabulary has 7 definitions of the project, and the proof of the theorem `PositivityTheory.Stage1.PM.rayClassFieldSt` that states it rests on 3,873 declarations.

For every number field K and every nonzero ideal 𝔮 of its ring of integers, the statement asserts that there is a finite abelian Galois extension L of K with three properties. Every prime of K that does not divide 𝔮 is unramified in L, which the project expresses by saying that every Galois element acting trivially modulo some prime above it is the identity. The Frobenius elements at the primes not dividing 𝔮 generate Gal(L/K). For every nonzero integral ideal I coprime to 𝔮, every character of Gal(L/K) takes the value 1 on the Artin symbol of I exactly when I·(β) = (α) for nonzero integers α and β of K that are coprime to 𝔮, satisfy α ≡ β mod 𝔮 and have a quotient α/β that is positive at every real embedding.

```
∀ K, ∀ 𝔮 ≠ 0, ∃ L/K finite abelian with 𝔭 unramified for all 𝔭 ∤ 𝔮, ⟨Frob_𝔭 | 𝔭 ∤ 𝔮⟩ = Gal(L/K), and for every integral I ≠ 0 prime to 𝔮, Art_{L/K}(I) = 1 ⟺ I = (α/β) with α, β ∈ O_K prime to 𝔮, α ≡ β mod 𝔮, α/β ≫ 0
```

The theorem that the name points to, as the first reader states it from its own knowledge. For every modulus 𝔪 of a number field K, made of a nonzero integral ideal and a set of real places, there is an abelian extension K_𝔪 of K that is unramified outside 𝔪 and for which the Artin map induces an isomorphism from the ray class group I^𝔪/P_{𝔪,1} onto Gal(K_𝔪/K). Reference is J. Neukirch, Algebraic Number Theory, 1999, Chapter VI, Section 6.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement treats only the modulus 𝔮 times all real places, because RayPair asks that φ(α)φ(β) be positive for every real embedding φ, so it gives the narrow ray class field and leaves out moduli with some or none of the real places.
- The Lean statement asserts only that such a field L exists and does not state that it is unique.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Unwinding the definitions shows that the third clause identifies the kernel of the Artin map on ideals prime to 𝔮 with the narrow ray group modulo 𝔮, which together with the first two clauses is the defining property of the ray class field for the modulus 𝔮 times all real places.

### 33, `FreeQuotientScheme`

The proposition is `GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme_holds` that states it rests on 136 declarations.

For every scheme S, every group scheme G over S and every S-scheme X with an action of G, the statement assumes that G is finite, flat and locally of finite presentation over S, that G(T) acts freely on X(T) for every S-scheme T, and that the set-theoretic orbit of every point of X lies in an affine open subscheme. It concludes that there are an S-scheme Y and a G-invariant S-morphism q from X to Y such that the induced map from the presheaf T ↦ X(T)/G(T) to the functor of points of Y is locally injective and locally surjective for the fppf topology over S, so Y represents the fppf quotient sheaf. It also concludes that q is an fppf G-torsor, which here means that the map from G ×_S X to X ×_Y X given by the action and the projection is an isomorphism and that q has sections over some jointly surjective family of flat morphisms of finite presentation into Y.

```
G finite locally free over S, G acting freely on X, every orbit inside an affine open ⟹ ∃ Y over S and a G-invariant q ∈ Hom_S(X, Y) with h_Y = (X/G)^fppf, (γ, pr_2) an isomorphism G ×_S X → X ×_Y X, and q split over an fppf cover of Y
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a finite locally free group scheme over S acting on an S-scheme X such that the orbit of every point lies in an affine open subset. Then the quotient Y = X/G exists as a scheme and as a quotient in ringed spaces, and the map from X to Y is integral, surjective and G-invariant. If G acts freely, the map from X to Y is finite locally free, the map from G ×_S X to X ×_Y X is an isomorphism, X is a G-torsor over Y, and Y represents the fppf quotient sheaf. Reference is M. Demazure and A. Grothendieck, Schémas en groupes I (SGA 3), Lecture Notes in Mathematics 151, 1970.

The first reader takes the proposition for a weaker statement and the second reader for the same statement. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement adds the hypothesis IsFreeAction, while SGA 3, Exposé V, Théorème 4.1 also constructs the quotient for actions that are not free.
- The Lean conclusion does not state that q is finite locally free and surjective or that Y is the quotient in ringed spaces, but these properties follow by fppf descent from the cartesian square and the fppf-local sections that IsFppfTorsor states.
- The Lean statement works over an arbitrary base scheme S, which is the setting of SGA 3 and is more general than Mumford's version over a field.

The check gives this reason for its judgement. The Lean hypotheses are those of SGA 3, Exposé V, Théorème 4.1 together with freeness, and the Lean conclusions imply every conclusion that the theorem gives for a free action, so the Lean text is the free case of the theorem, which is a special case rather than the weaker statement that A sees, and it is the same statement only if the published theorem is taken to be its free clause alone, as B takes it.

The check found no emptiness.

The check found these errors in the first reader's account of the Lean text, and the account above is printed as the reader wrote it.

- A writes that q has sections over "flat morphisms of finite presentation", while IsFppfTorsor in the Lean text asks only for Flat (f i) and LocallyOfFinitePresentation (f i), so the morphisms need not be quasi-compact.

The first reader's confidence is medium. The hypotheses coincide with those of SGA 3 and the conclusion is visibly part of its free case, but the fppf topology on the slice category and the action structures are Mathlib notions whose exact form the dossier does not show.

### 34, `CMPotentialGoodReductionSt`

The proposition is `GlobalTheory.Published.CMPotentialGoodReductionSt`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `UpperTheory.Lit.cmPotentialGoodReduction` that states it rests on 9,632 declarations.

For every discrete valuation ring R with finite residue field and fraction field K, and every abelian scheme A over Spec K, meaning a commutative group scheme that is smooth, proper and geometrically connected, the statement considers any number field F. It assumes that A has some relative dimension d with the degree of F over ℚ equal to 2d, and that some domain O with fraction field F acts on A through a ring homomorphism into the endomorphisms of A defined over K. The homomorphism is not required to be injective, but it is injective automatically because a nonzero kernel would contain a nonzero integer, so the hypothesis is the usual condition that F embeds in the endomorphism algebra of A. It concludes that A has potential good reduction with respect to R, meaning that there are a finite extension L of K and a discrete valuation ring W with fraction field L and W ∩ K = R such that A ×_K L is the generic fibre of an abelian scheme over W, by an isomorphism that respects the group law.

```
R DVR with finite residue field, K = Frac R, A/K abelian variety of dimension d, F number field with dim_ℚ F = 2d, O ↪ End_K(A) with Frac O = F ⟹ ∃ L/K finite and a DVR W ⊂ L over R such that A ×_K L has good reduction over W
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be a field with a discrete valuation and A an abelian variety over K with complex multiplication over K, so that End_K(A) ⊗ ℚ contains a commutative semisimple subalgebra of degree 2 dim A. Then A has potential good reduction, so it acquires good reduction over a finite extension of K. Reference is J.-P. Serre and J. Tate, Good reduction of abelian varieties, Annals of Mathematics 88, 1968.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement requires the residue field of R to be finite, while Serre and Tate prove the result for an arbitrary discrete valuation.
- The Lean statement requires the complex multiplication to come from one number field F of degree 2d over ℚ, while the published theorem allows a commutative semisimple algebra of that degree, which can be a product of fields.
- The Lean statement requires OAct to act by endomorphisms of A over Spec K, which matches the published theorem for complex multiplication over K but leaves out its corollary for complex multiplication that is defined only over an algebraic closure.
- The Lean statement does not require the map from O to the endomorphisms of A to be injective, but a nonzero kernel would contain a nonzero integer m, and multiplication by m is a nonzero endomorphism because d is at least 1, so the hypothesis still expresses complex multiplication by F.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The project's definitions of abelian scheme, complex multiplication and potential good reduction match the standard notions, and the only changes are the finite residue field and the requirement that the CM algebra be a field.

### 35, `ChowFormHyperplaneSection`

The proposition is `GlobalTheory.Published.ChowFormHyperplaneSection`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `ChowFormCompatibility.chow_form_hyperplane_section` that states it rests on 427 declarations.

Let k be a field of characteristic zero, P a homogeneous prime ideal of k[x_0, …, x_{N−1}] with Krull dimension of k[x]/P equal to e + 2, so that V(P) is a projective variety of dimension e + 1, and u ∈ k^N a vector whose linear form ℓ_u = Σ u_j x_j does not lie in P. Suppose that f, a polynomial in e + 2 blocks of N variables, is a Chow form of P in the project's sense, namely an irreducible polynomial over k, homogeneous of one common degree in each block, whose zeros over the algebraic closure are exactly the tuples of e + 2 linear forms that have a common nonzero zero on V(P). Suppose also that for every prime Q in the hyperplane-section cycle of P + (ℓ_u), whose members are the minimal primes other than the irrelevant ideal with multiplicity m_Q equal to the length of the localisation at Q, the polynomial g_Q in e + 1 blocks is a Chow form of Q in the same sense. Then substituting u for the first block of variables in f gives c·∏_Q g_Q^{m_Q} for some nonzero constant c in k.

```
char k = 0, P homogeneous prime, dim k[x]/P = e + 2, ℓ_u ∉ P, f = Ch_P, g_Q = Ch_Q for V(P)·H_u = Σ m_Q [Q] with m_Q = length(k[x]_Q/(P + (ℓ_u))) ⟹ ∃ c ∈ k^×, f(u, U_1, …, U_{e+1}) = c ∏_Q g_Q(U_1, …, U_{e+1})^{m_Q}
```

The theorem that the name points to, as the first reader states it from its own knowledge. If V is an irreducible projective variety of dimension r ≥ 1 with Chow form Ch_V and H_u is a hyperplane that does not contain V, then the Chow form of the intersection cycle V·H_u, the product of the Chow forms of its components raised to their intersection multiplicities, equals Ch_V(u, U_1, …, U_r) up to a nonzero constant factor. Reference is P. Philippon, Critères pour l'indépendance algébrique, Publications Mathématiques de l'IHÉS 64, 1986.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement is restricted to fields of characteristic zero, where an irreducible polynomial with the zero set that IsChowFormInt requires is the Chow form up to a nonzero constant, while the published identity holds over any field when Chow forms of cycles are used.
- The Lean statement treats one variety given by a homogeneous prime ideal and specialises only the first block of f, and the published versions for cycles and for other blocks reduce to this case by multiplicativity and the symmetry of the Chow form.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The project's Chow form agrees with the usual one up to a constant because a prime ideal stays radical over the algebraic closure in characteristic zero, and its length multiplicities are the intersection multiplicities with a Cartier divisor, but the identity is a folklore lemma of elimination theory whose exact published wording and field hypotheses vary between sources.

### 36, `DeligneRibet`

The proposition is `GlobalTheory.Published.DeligneRibet`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `PositivityTheory.PfDR.deligneRibet_holds` that states it rests on 4,444 declarations.

Let F be a totally real number field, l a prime and n ≥ 1, and let ε be a rational-valued function on ideals of the ring of integers that is constant on narrow ray classes modulo l^n among nonzero ideals coprime to l and that takes l-integral values on those ideals. Let 𝔠 be a nonzero ideal coprime to l and k ≥ 1 an integer. Suppose r is the value at 1 − k of a function holomorphic on ℂ ∖ {1} that equals the Dirichlet series Σ ε(I) N(I)^{−s} over nonzero ideals I coprime to l for Re s > 1, and r' is the corresponding value for the translated function I ↦ ε(𝔠I). Then r − N(𝔠)^k r' is l-integral, that is, it lies in ℤ_(l).

```
F totally real, ε constant on Cl^+_F(l^n) with values in ℤ_(l), (𝔠, l) = 1, k ≥ 1 ⟹ ζ(ε, 1 − k) − N𝔠^k ζ(ε_𝔠, 1 − k) ∈ ℤ_(l), where ζ(ε, s) = Σ_{(I, l) = 1} ε(I) N I^{−s} and ε_𝔠(I) = ε(𝔠I)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let F be totally real, 𝔣 an integral ideal, p a prime and ε a locally constant ℤ_p-valued function on the narrow ray class group of F modulo 𝔣p^∞. For an integral ideal 𝔠 prime to 𝔣p and an integer k ≥ 1, the smoothed value ζ(ε, 1 − k) − N𝔠^k ζ(ε_𝔠, 1 − k), with ε_𝔠(𝔞) = ε(𝔠𝔞) and partial zeta functions summed over ideals prime to 𝔣p, lies in ℤ_p. Reference is P. Deligne and K. A. Ribet, Values of abelian L-functions at negative integers over totally real fields, Inventiones Mathematicae 59, 1980.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement uses only the moduli powMod F l n, which are powers of l, so the auxiliary ideal 𝔣 of Deligne and Ribet is the unit ideal.
- The Lean statement takes ε rational-valued, l-integral on ideals coprime to l and constant on narrow ray classes modulo one fixed l^n, while Deligne and Ribet take a locally constant ℤ_l-valued function on the narrow ray class group modulo 𝔣l^∞, and for 𝔣 equal to the unit ideal the two forms are equivalent by linearity in ε.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The hypotheses and the smoothed combination match the Deligne–Ribet integrality statement, and a check over ℚ at k = 1 with Hurwitz zeta values confirms the direction of the translation ε(𝔠I), but the paper's exact normalisation is recalled from memory.

### 37, `RayClassFieldMaximalSt`

The proposition is `GlobalTheory.Published.RayClassFieldMaximalSt`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `GlobalTheory.Published.rayClassFieldMaximalSt_holds` that states it rests on 62 declarations.

Let K be a number field, L and L' finite abelian Galois extensions of K, and 𝔪 a nonzero ideal of the ring of integers of K. Assume that L satisfies the project's ray class field condition for 𝔪, the same three clauses as the field in proposition 32, which make L the ray class field of K for the modulus 𝔪 times all real places. Assume also that every character χ of Gal(L'/K) is unramified at every prime not dividing 𝔪 and takes equal values on the Artin symbols of (α) and (β) whenever α and β are nonzero integers coprime to 𝔪 with α ≡ β mod 𝔪 and α/β positive at every real embedding. Then L' admits a K-algebra embedding into L.

```
L = K_{𝔪∞} the narrow ray class field mod 𝔪, L'/K abelian, every χ of Gal(L'/K) unramified outside 𝔪 with χ(Art(α)) = χ(Art(β)) whenever α ≡ β mod 𝔪 and α/β ≫ 0 ⟹ ∃ a K-embedding L' ↪ L
```

The theorem that the name points to, as the first reader states it from its own knowledge. The ray class field K_𝔪 of a number field K for a modulus 𝔪 contains every abelian extension L'/K whose conductor divides 𝔪, equivalently every abelian extension unramified outside 𝔪 whose Artin map kills the ray P_{𝔪,1}. Reference is J. Neukirch, Algebraic Number Theory, 1999, Chapter VI, Section 6.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement takes L to be the ray class field for 𝔪 times all real places, because RayPair asks for positivity at every real embedding, so it covers only narrow ray class fields.
- The Lean statement expresses the condition that the conductor of L' divides 𝔪 times all real places through IsModulus for every character of the Galois group of L' over K, and taking β = 1 in RayPair shows that this is equivalent to the usual conductor condition.
- The Lean conclusion is a K-algebra embedding of L' into L, which is equivalent to the inclusion of L' in L inside a fixed algebraic closure.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Taking β = 1 in the character condition shows that the Artin map of L' kills every principal ideal with a totally positive generator congruent to 1 mod 𝔪, which is the condition that the conductor of L' divides 𝔪 times all real places, and the conclusion is the standard containment of L' in the ray class field.

### 38, `WeberRayFieldSt`

The proposition is `GlobalTheory.Published.WeberRayFieldSt`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `PositivityTheory.Prw.weberRayFieldSt_holds` that states it rests on 7,141 declarations.

Let K be an imaginary quadratic field with a chosen embedding into ℂ and discriminant less than −4, so that its only units are ±1. Let Λ be a period lattice whose points are exactly the images of the integers of K, with Weierstrass invariants g₂ and g₃ and Weierstrass function ℘, and let n be a positive integer. The statement asserts that the field generated over K by g₂³/(g₂³ − 27g₃²) and by the numbers g₂g₃/(g₂³ − 27g₃²)·℘(z/n) for z ∈ Λ with z/n ∉ Λ is a number field, is abelian Galois over K, and satisfies the project's ray class field condition for the ideal nO_K. Because K has no real embeddings, that condition says that this field is the ray class field of K modulo n, and the generators are j/1728 and a constant multiple of the Weber function at the nonzero n-torsion points.

```
K imaginary quadratic, d_K < −4, Λ = O_K ⊂ ℂ, n ≥ 1 ⟹ K(g₂³/Δ, g₂g₃Δ^{−1}℘(z/n) for z ∈ Λ ∖ nΛ) is the ray class field of K modulo nO_K, with Δ = g₂³ − 27g₃²
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be an imaginary quadratic field, E an elliptic curve over ℂ with End(E) ≅ O_K, h a Weber function for E and 𝔠 a nonzero integral ideal of O_K. Then K(j(E), h(E[𝔠])) is the ray class field of K modulo 𝔠. Reference is J. H. Silverman, Advanced Topics in the Arithmetic of Elliptic Curves, 1994, Chapter II, Theorem 5.6.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement treats only the moduli nO_K generated by a positive integer n, while the published theorem covers every nonzero integral ideal 𝔠 of O_K through the 𝔠-torsion points.
- The Lean statement excludes the fields of discriminant −3 and −4, which the published theorem covers with a Weber function built from ℘³ or ℘².
- The Lean statement fixes the lattice to be the image of O_K, while the published theorem allows any elliptic curve with complex multiplication by O_K, whose lattice can lie in any ideal class.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. For a field without real embeddings the project's ray class field condition is the usual characterisation of the ray class field, and the adjoined numbers generate the same field over K as j(E) and the Weber function values on E[n].

### 39, `KStability`

The proposition is `UpperTheory.V.Published.KStability`. Its vocabulary has 8 definitions of the project, and the proof of the theorem `PositivityTheory.v8.KStability.kStability` that states it rests on 345 declarations.

For every commutative ring R and natural number s, the statement assumes that every unimodular row of length m + 1 with m ≥ s can be shortened, meaning that adding suitable multiples of its last entry to the other entries gives a unimodular row of length m, which is the condition that the stable rank of R is at most s. For all natural numbers i and n with 2i + s + 2 ≤ n, it concludes that the map H_i(GL_n(R), ℤ) → H_i(GL_{n+1}(R), ℤ) on group homology with trivial integer coefficients, induced by A ↦ diag(A, 1), is an isomorphism.

```
sr(R) ≤ s, n ≥ 2i + s + 2 ⟹ H_i(GL_n(R), ℤ) → H_i(GL_{n+1}(R), ℤ) is an isomorphism
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let R be a ring of finite stable rank sr(R), normalised so that fields have stable rank 1. Then the stabilisation map H_i(GL_n(R), ℤ) → H_i(GL_{n+1}(R), ℤ) is surjective for n ≥ 2i + sr(R) − 1 and an isomorphism for n ≥ 2i + sr(R). Reference is W. van der Kallen, Homology stability for linear groups, Inventiones Mathematicae 60, 1980.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean statement asks for n ≥ 2i + s + 2, while van der Kallen proves the isomorphism for n ≥ 2i + s, so the Lean range starts two steps later.
- The Lean statement is restricted to commutative rings, while van der Kallen's theorem holds for associative rings with unit.
- The Lean statement leaves out the surjectivity of the stabilisation map for n ≥ 2i + s − 1.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The project's stable range condition is the standard one and the Lean range lies inside the isomorphism range of van der Kallen's theorem and also inside the slightly smaller range of later proofs such as that of Randal-Williams and Wahl.

### 40, `PrincipalisationCharZero`

The proposition is `GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero`. Its vocabulary has 9 definitions of the project, and the proof of the theorem `PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisationCharZero_closed` that states it rests on 6,159 declarations.

Let k be a field of characteristic zero and X a scheme that is smooth of constant relative dimension d, quasi-compact and separated over k. Let I be an ideal sheaf on X whose zero locus contains no irreducible component of X, and let E be a closed subset of X whose reduced ideal is a simple normal crossings divisor at every point of E. The statement asserts a finite sequence of blowups s from X' to X in which every centre Z is smooth over k and has simple normal crossings with the accumulated boundary, where the boundary starts as E and is replaced at each step by the preimage of the old boundary together with the centre. It further asserts that X' is smooth over k, that the pulled-back ideal I·O_{X'} is locally generated by one nonzerodivisor, that the reduced zero locus of I·O_{X'} is a simple normal crossings divisor, and that s is an isomorphism over the complement of the zero locus of I.

```
X smooth over k with char k = 0, I ≠ 0 on every component, E snc ⟹ ∃ s from X' to X, a composite of blowups along smooth centres that are snc with the accumulated boundary, with X' smooth, I·O_{X'} invertible with snc support, and s an isomorphism over X ∖ V(I)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let X be a smooth scheme of finite type over a field of characteristic zero, I an ideal sheaf that is nonzero on every irreducible component and E a simple normal crossings divisor. Then there is a finite sequence of blowups along smooth centres lying over the cosupport of I, each with simple normal crossings with the accumulated exceptional divisors and the transform of E, such that I·O_{X'} is the ideal sheaf of a divisor whose support together with the exceptional divisors and the transform of E has simple normal crossings, and the composite is an isomorphism over the complement of the cosupport of I. Reference is J. Kollár, Lectures on Resolution of Singularities, Annals of Mathematics Studies 166, 2007, Chapter 3.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean statement requires X to be smooth of one relative dimension d and separated over k, while the published theorem allows any smooth scheme of finite type over k.
- The Lean statement does not require each centre to lie over the zero set of I, although IsIso (s ∣_ I.support.compl) forces the composite to be an isomorphism over the complement of that zero set.
- The Lean conclusion gives simple normal crossings for the reduced support of I·O_X' alone, while the published theorem gives simple normal crossings for that support together with the final boundary of exceptional divisors and the transform of E.
- The Lean statement leaves out the functoriality under smooth morphisms and field extensions that the published versions of Kollár and others include.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. Every Lean clause follows from the standard principalisation theorem with boundary, since an invertible ideal with snc support on a regular scheme is locally a monomial in a regular system of parameters, but the theorem exists in several versions with different boundary clauses and the comparison relies on the project's local definitions of snc centres and blowups.

### 41, `SemiAbelianHomExtension`

The proposition is `GlobalTheory.Published.SemiAbelianHomExtension`. Its vocabulary has 9 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension` that states it rests on 2,424 declarations.

Let S be a Noetherian scheme all of whose local rings are integrally closed domains, and let U be a dense open subset of S. Let G and H be group schemes over S that are semi-abelian in the project's sense, which means commutative, smooth, separated, quasi-compact and geometrically connected over S, with the pullback to every geometric point Spec Ω → S an extension of an abelian variety by a split torus whose character group is free of finite rank. Then every homomorphism of group schemes f from G_U to H_U over U is the restriction to U of exactly one homomorphism of group schemes F from G to H over S.

```
S normal Noetherian, U ⊆ S dense open, G, H semi-abelian over S ⟹ ∀ f ∈ Hom_{U-gr}(G_U, H_U) ∃! F ∈ Hom_{S-gr}(G, H) with F|_U = f
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let S be a normal Noetherian scheme, U ⊆ S a dense open subscheme and G, H semi-abelian schemes over S, that is smooth separated commutative group schemes of finite type whose fibres are extensions of abelian varieties by tori. Then every homomorphism G_U → H_U extends uniquely to a homomorphism G → H. The reference is G. Faltings and C.-L. Chai, Degeneration of Abelian Varieties, Springer 1990, Chapter I, Proposition 2.7.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text asks for the torus extension only over geometric points Spec Ω → S and with a split torus whose character group is free of finite rank, and this agrees with the fibrewise condition of Faltings and Chai because a torus over an algebraically closed field is split and the extension structure descends from the geometric fibre to the fibre.
- The Lean text lists quasi-compactness of G and H over S as a separate condition, and together with smoothness it gives the finite type that Faltings and Chai require.
- Uniqueness of F is asserted among homomorphisms of group objects, because the Lean formula is ∃! F with IsMonHom F and the restriction condition taken together.
- The Lean text quantifies only over schemes and algebraically closed fields in universe 0, which has no mathematical effect.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Every hypothesis on S, U, G and H and the existence and uniqueness in the conclusion match the statement of Faltings and Chai once the fibre condition is read geometrically.

### 42, `CubeTheorem`

The proposition is `GlobalTheory.Published.CubeTheorem`. Its vocabulary has 10 definitions of the project, and the proof of the theorem `GlobalTheory.SpreadingModels.cubeTheorem_holds` that states it rests on 2,459 declarations.

Let S be a scheme, A an abelian scheme over S in the project's sense (a commutative group scheme that is smooth, proper and geometrically connected over S), and L a line bundle on A presented by a cocycle of units g_ij on an open cover with g_ii = 1 and g_ij g_jk = g_ik. For every S-scheme T and all S-morphisms a, b, c from T to A, form the line bundle on T that is the tensor product of the pullbacks of L along a+b+c, a+b, a+c, b+c, a, b, c and the zero morphism, with exponents 1, −1, −1, −1, 1, 1, 1, −1 in this order. The Lean text claims that this line bundle is trivial, which it expresses as the existence of units on the charts of the induced cover of T that turn the pulled-back cocycle into a coboundary.

```
(a+b+c)^*L ⊗ (a+b)^*L^{−1} ⊗ (a+c)^*L^{−1} ⊗ (b+c)^*L^{−1} ⊗ a^*L ⊗ b^*L ⊗ c^*L ⊗ 0^*L^{−1} ≅ O_T for every S-scheme T and all a, b, c ∈ A(T)
```

The theorem that the name points to, as the first reader states it from its own knowledge. For an abelian scheme A over an arbitrary base scheme S and a line bundle L on A, the line bundle Θ(L) = ⊗_{I ⊆ {1,2,3}} m_I^*L^{(−1)^{|I|+1}} on A ×_S A ×_S A is trivial, where m_I is the sum of the coordinates indexed by I and m_∅ is the zero section. Pulling back along (a, b, c) gives the equivalent form that the corresponding line bundle on T is trivial for every S-scheme T and all a, b, c ∈ A(T). The reference is L. Moret-Bailly, Pinceaux de variétés abéliennes, Astérisque 129, 1985, Chapter I.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text encodes a line bundle as a Čech cocycle of units on an open cover and triviality as the existence of units on the charts that split the pulled-back cocycle, and both encodings are equivalent to the usual notions of an invertible sheaf and of its triviality.
- The Lean text states triviality for T-valued points a, b and c, which is equivalent to the triviality of the cube bundle on A ×_S A ×_S A by taking T to be that product with its three projections.
- The eighth factor is the pullback along the unit morphism 1 with exponent −1, so the Lean text is the form Θ(L) ⊗ π^*e^*L^{−1} that holds over an arbitrary base, and over a field this factor is trivial.
- The Lean text asserts only that a trivialisation exists and says nothing about the canonical trivialisation or the cubical structure of Breen and Moret-Bailly.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The eight pullbacks and the coefficient vector are exactly the cube line bundle with its rigidifying term 0^*L^{−1}, and the remaining doubt concerns only my recollection of the precise published source for an arbitrary base.

### 43, `GreenRegularCharacters`

The proposition is `GlobalTheory.Published.GreenRegularCharacters`. Its vocabulary has 10 definitions of the project, and the proof of the theorem `GlobalTheory.greenRegularCharacters_holds` that states it rests on 1,169 declarations.

Let g be a prime, d a positive integer and K a field with an F_g-algebra structure of dimension d, so that K is a field with g^d elements. The Lean text claims a map τ from the characters θ of K^× to complex-valued functions on GL_d(F_g) such that, for every regular θ (one with θ, θ^g, …, θ^{g^{d−1}} pairwise distinct), τ(θ) is an irreducible character whose average over the unipotent radical of each standard maximal parabolic subgroup is zero, τ(θ)(1) = ∏_{i=1}^{d−1}(g^i − 1), and τ(θ)(y) = (−1)^{d−1} ∑_{i=0}^{d−1} θ(z^{g^i}) for every y with irreducible characteristic polynomial and every root z of that polynomial in K^×. For regular θ and θ′ it claims τ(θ) = τ(θ′) exactly when θ′ = θ^{g^i} for some i < d. Finally it claims that every irreducible character of GL_d(F_g) with these vanishing averages, which is the project's notion of a cuspidal character, equals τ(θ) for some regular θ.

```
∃ τ with τ(θ) irreducible cuspidal, τ(θ)(1) = ∏_{i=1}^{d−1}(g^i − 1) and τ(θ)(y) = (−1)^{d−1} ∑_{i=0}^{d−1} θ(z^{g^i}) for regular θ and elliptic y with eigenvalue z ∈ K^×, τ(θ) = τ(θ′) ⇔ ∃ i < d, θ′ = θ^{g^i}, and {cuspidal χ} = {τ(θ) | θ regular}
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a prime power q and n ≥ 1, the irreducible cuspidal characters of GL_n(F_q) correspond bijectively to the Frobenius orbits {θ, θ^q, …, θ^{q^{n−1}}} of regular characters θ of F_{q^n}^×. The character attached to θ has degree ∏_{i=1}^{n−1}(q^i − 1) and value (−1)^{n−1} ∑_{i=0}^{n−1} θ(z^{q^i}) at an element whose eigenvalues z, z^q, …, z^{q^{n−1}} generate F_{q^n}, and Green's paper determines its values on all conjugacy classes. The reference is J. A. Green, The characters of the finite general linear groups, Transactions of the American Mathematical Society 80, 1955.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only GL_d over the prime field ZMod g, while Green's theorem covers GL_n(F_q) for every prime power q.
- The Lean text fixes the values of τ(θ) only at the identity and at elements with irreducible characteristic polynomial, while Green gives the values on every conjugacy class.
- Cuspidality is defined by the vanishing of the average of the character over the unipotent radical of each standard maximal parabolic subgroup, and since this average is the dimension of the fixed space and every proper parabolic is conjugate to a standard one inside a maximal one, the condition is equivalent to the usual definition.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The degree, the elliptic values, the identification modulo Frobenius and the surjectivity onto cuspidal characters each match the standard statement, and the restriction to prime fields is explicit because the group is GL_d over the integers modulo the prime g.

### 44, `KFiniteAnalyticUJ`

The proposition is `GlobalTheory.Published.KFiniteAnalyticUJ`. Its vocabulary has 10 definitions of the project, and the proof of the theorem `CompanionTheory.D.gk.HC.kFiniteVectors_analytic_indefiniteUnitary` that states it rests on 838 declarations.

Let n be a natural number, J a diagonal n×n matrix with entries ±1 (p entries 1 and q entries −1), U_J = {g ∈ M_n(ℂ) | g^*Jg = J} the indefinite unitary group U(p, q), and K the set of unitary matrices commuting with J, which is U(p) × U(q). Let H be a nonzero complex Hilbert space and σ a map from M_n(ℂ) to bounded operators on H whose restriction to U_J is multiplicative with σ(1) = 1, isometric, strongly continuous and topologically irreducible. Then for every vector v lying in a finite-dimensional σ(K)-stable subspace, the map g ↦ σ(g)v is real-analytic on U_J, in the sense that near each point of U_J it agrees with a real-analytic H-valued function on an open subset of M_n(ℂ) ≅ ℝ^{2n²}.

```
σ irreducible unitary representation of U(p, q) on H, v K-finite for K = U(p) × U(q) ⟹ g ↦ σ(g)v real-analytic on U(p, q)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a connected real reductive Lie group with maximal compact subgroup K and π an irreducible unitary representation of G on a Hilbert space. Then π is admissible, and every K-finite vector v is an analytic vector, so g ↦ π(g)v is real-analytic on G. The reference is Harish-Chandra, Representations of a semisimple Lie group on a Banach space. I, Transactions of the American Mathematical Society 75, 1953.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only the groups U(p, q) given by a diagonal sign matrix J, with K = U(p) × U(q), while Harish-Chandra's theorem holds for every real reductive group with a maximal compact subgroup.
- The Lean text assumes an irreducible unitary representation on a Hilbert space, while the published theorem also covers admissible representations on Banach spaces.
- Real analyticity on U(p, q) is expressed as local agreement with a real-analytic function on an open subset of the ambient matrix space, which is equivalent to analyticity on the real-analytic submanifold U(p, q).
- The map σ is defined on all matrices, but only its values on U(p, q) enter the hypotheses and the conclusion.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. U(p, q) is a connected linear reductive group with maximal compact subgroup U(p) × U(q), and every hypothesis matches the standard notions of an irreducible unitary representation and of a K-finite vector.

### 45, `Principalisation`

The proposition is `GlobalTheory.Published.Principalisation`. Its vocabulary has 10 definitions of the project, and the proof of the theorem `PositivityTheory.ResPlug.WeightsCompactStabilizer.principalisation_closed` that states it rests on 6,583 declarations.

Let k be a field of characteristic zero and Y an integral scheme that is smooth of relative dimension d and projective over k, meaning a closed subscheme of some P^N_k over k, and let I be a nonzero ideal sheaf on Y. The Lean text claims a morphism s from an integral scheme Y′ to Y such that Y′ is again smooth of relative dimension d and projective over k, s is a finite composite of blowups whose centres are smooth over k and lie over the zero locus V(I), and s is an isomorphism over Y ∖ V(I). It further claims that the pulled-back ideal I·O_{Y′} is locally generated by one nonzerodivisor and that the reduced ideal of its zero locus is a simple normal crossings divisor, meaning that near each point it is generated by a product of part of a regular system of parameters. Each blowup is characterised by its universal property among all schemes on which the pulled-back centre ideal becomes locally principal and generated by a nonzerodivisor.

```
Y/k smooth projective integral, char k = 0, I ≠ 0 ⟹ ∃ s = π_1 ∘ ⋯ ∘ π_r from Y′ to Y, blowups with smooth centres over V(I), s iso over Y ∖ V(I), I·O_{Y′} invertible with snc support
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let X be a smooth variety over a field of characteristic zero and I ⊆ O_X an ideal sheaf that is nonzero on every irreducible component. Then there is a sequence of blowups X_r → ⋯ → X_0 = X with composite π, whose centres are smooth and have simple normal crossings with the exceptional divisors already created, such that π is an isomorphism over X ∖ cosupp(I) and π^*I is the ideal sheaf of a simple normal crossings divisor, and the construction is functorial for smooth morphisms. The reference is J. Kollár, Lectures on Resolution of Singularities, Annals of Mathematics Studies 166, 2007, Theorem 3.26.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text requires Y to be integral and projective over k, while principalisation holds for every smooth variety over a field of characteristic zero.
- The centres in the Lean chain need only be smooth over k and lie over the support of I, and the condition that each centre has simple normal crossings with the exceptional divisors created before it is absent.
- The Lean text makes no claim of functoriality under smooth morphisms, which Kollár's formulation includes.
- The Lean conclusion says that I·O_{Y′} is locally generated by one nonzerodivisor and that the reduced ideal of its support is locally generated by a product of part of a regular system of parameters, which on the regular scheme Y′ is equivalent to I·O_{Y′} being the ideal of a divisor with simple normal crossings support.
- The Lean text adds that Y′ is integral, smooth of relative dimension d and projective over k, which follows from blowing up along smooth centres.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The core conclusion matches principalisation, but the restriction to projective varieties together with the weaker conditions on the centres makes the label depend on which formulation of the published theorem one takes as the standard.

### 46, `RealMetaplecticRepresentation`

The proposition is `GlobalTheory.Published.RealMetaplecticRepresentation`. Its vocabulary has 10 definitions of the project, and the proof of the theorem `PositivityTheory.Stage1.PM.realMetaplecticRepresentation` that states it rests on 259 declarations.

For every nonempty finite index set l of size n, the Lean text claims a topological group G with a homomorphism pr onto the real symplectic group Sp(2n, ℝ), a homomorphism ω into the unitary operators on L²(ℝⁿ) and a homomorphism into the continuous linear operators on the Schwartz space 𝒮(ℝⁿ). The map pr is a surjective covering map with kernel {1, ε} for some ε ≠ 1, and ω(ε) = −1. The representation ω is strongly continuous, satisfies ω(g)ρ(w) = ρ(pr(g)w)ω(g) for the Weyl operators ρ(p, q)f(x) = e^{2πi⟨q,x⟩ + πi⟨p,q⟩} f(x + p), preserves 𝒮(ℝⁿ), and makes t ↦ ω(γ(t))f smooth into L² for every Schwartz f and every continuous family γ in G whose image in Sp(2n, ℝ) depends smoothly on the parameters. For every X in sp(2n, ℝ) there is a continuous one-parameter subgroup γ of G with pr(γ(t)) = exp(tX), and the derivative of t ↦ ω(γ(t))f at t = 0 is (4πi)^{−1} ∑_{a,b} ((XJ)_{ab}/2)(D_a D_b + D_b D_a)f, where D_a = ∂/∂x_a for the first n coordinates of phase space and D_a = 2πi x_a for the last n.

```
∃ G, pr ∈ Hom(G, Sp(2n,ℝ)) a double covering with kernel {1, ε}, ω ∈ Hom(G, U(L²(ℝⁿ))) strongly continuous with ω(ε) = −1, ω(g)ρ(w)ω(g)^{−1} = ρ(pr(g)w), ω(G)𝒮 ⊆ 𝒮, 𝒮 ⊆ smooth vectors, dω(X) = (4πi)^{−1} ∑_{a,b} ½(XJ)_{ab}(D_a D_b + D_b D_a) on 𝒮
```

The theorem that the name points to, as the first reader states it from its own knowledge. For each g ∈ Sp(2n, ℝ) there is a unitary operator μ(g) on L²(ℝⁿ), unique up to a scalar of modulus one by the Stone–von Neumann theorem, with μ(g)ρ(w)μ(g)^{−1} = ρ(gw), and these operators can be normalised to a strongly continuous unitary representation of the metaplectic group Mp(2n, ℝ), the connected double cover of Sp(2n, ℝ), on which the nontrivial element of the kernel acts by −1. This representation preserves the Schwartz space, which is its space of smooth vectors, and its differential sends X ∈ sp(2n, ℝ) to the Weyl quantisation of the quadratic form attached to X. The reference is G. B. Folland, Harmonic Analysis in Phase Space, Annals of Mathematics Studies 122, 1989, Chapter 4.

The first reader takes the proposition for a weaker statement and the second reader for the same statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text asserts only the existence of G and of the representation with the listed properties and says nothing about the uniqueness of the operators ω(g) up to scalars, which the published theorem obtains from the Stone–von Neumann theorem.
- The Lean text neither names G as the metaplectic group nor requires it to be connected, but the intertwining relation and strong continuity rule out the split double cover, so G is forced to be Mp(2n, ℝ).
- The Lean text states that Schwartz functions are smooth vectors along smooth families in G but not that they are all of the smooth vectors.
- The Lean text leaves out the decomposition of L²(ℝⁿ) into the even and the odd irreducible subrepresentations.
- The Weyl operators, the matrix J and the generator formula follow the Mathlib conventions, and the operator quad X satisfies [quad X, dρ(w)] = dρ(Xw) with no scalar left over on the perfect Lie algebra sp(2n, ℝ), so the generator formula has the right normalisation.

The check gives this reason for its judgement. A judges weaker and B judges same, and I side with A because the Lean text asserts only the existence of the cover and the representation and omits the uniqueness up to scalars and the identification of the smooth vectors with the Schwartz space, which standard statements of the Segal–Shale–Weil theorem include.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. All the listed properties belong to the Segal–Shale–Weil theorem and the generator formula has the correct sign and constant for the dilation and the lower shear in one variable, which I computed, but the Lean text leaves out the uniqueness that standard statements include.

### 47, `TameQuotient`

The proposition is `GlobalTheory.Published.TameQuotient`. Its vocabulary has 10 definitions of the project, and the proof of the theorem `GlobalTheory.Published.TameQuotient_holds` that states it rests on 157 declarations.

Let F be a number field with algebraic closure Ω, l a prime, v a maximal ideal of O_F not containing l, Nv = |O_F/v|, and A a valuation ring of Ω lying over v, with decomposition group D and inertia group I inside Gal(Ω/F), and let I′ be the intersection of all open normal subgroups of I of l-power index. The Lean text claims that I′ is closed in Gal(Ω/F) and normal in D, that every open normal subgroup of I′ has index prime to l, that there is a continuous surjection from I onto the additive group ℤ_l with kernel exactly I′, and that some γ ∈ I generates I topologically modulo I′. It further claims, for every Frobenius element φ ∈ D (one inducing x ↦ x^{Nv} on the residue field) and every such γ, that φ, γ and I′ generate a dense subgroup of D and that φγφ^{−1} ≡ γ^{Nv} modulo I′. Finally, for every finite group H and elements a, c ∈ H with c of l-power order and aca^{−1} = c^{Nv}, it claims a continuous homomorphism from D to H that is trivial on I′ and sends φ to a and γ to c.

```
I′ = ⋂{U ⊴ I open, [I : U] = l^k}, I/I′ ≅ ℤ_l, I′ prime to l, D/I′ topologically generated by φ, γ with φγφ^{−1} ≡ γ^{Nv}, and ∃ continuous f from D/I′ to H with f(φ) = a, f(γ) = c for every finite H and a, c ∈ H with c^{l^k} = 1, aca^{−1} = c^{Nv}
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be a non-archimedean local field with residue field of q elements and residue characteristic p. The Galois group of the maximal tamely ramified extension of K is topologically generated by a lift φ of Frobenius and a generator τ of tame inertia subject to the single relation φτφ^{−1} = τ^q, the tame inertia group is isomorphic to ∏_{ℓ ≠ p} ℤ_ℓ(1), and the wild inertia group is a pro-p group. The reference is J. Neukirch, A. Schmidt and K. Wingberg, Cohomology of Number Fields, 2nd edition, Springer 2008, Chapter VII §5.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text works with the decomposition and inertia subgroups of Gal(Ω/F) at a finite place of a number field, which are isomorphic to the Galois groups of the completion, so local fields of positive characteristic are left out.
- The Lean text describes only the quotient of the decomposition group by the kernel I′ of the maximal pro-l quotient of inertia and says nothing about the prime-to-l part of tame inertia or about wild inertia beyond the fact that every open normal subgroup of I′ has index prime to l.
- The Lean text identifies I/I′ with ℤ_l only as a topological group, and the cyclotomic action enters only through the relation φγφ^{−1} ≡ γ^{Nv} modulo I′.
- The presentation of D/I′ is given as the existence of homomorphisms to finite groups in which the image of γ has l-power order, and the uniqueness of such a homomorphism is left to follow from the generation clause.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. Each clause follows from the tame structure theorem when l differs from the residue characteristic, but the Lean text is a reformulation for which I know no single standard published wording.

### 48, `InducedSimpleLowestAlcove`

The proposition is `GlobalTheory.Published.InducedSimpleLowestAlcove`. Its vocabulary has 11 definitions of the project, and the proof of the theorem `GlobalTheory.Alc.inducedSimpleLowestAlcove` that states it rests on 523 declarations.

Let p be a prime, k a field of characteristic p, N a natural number and λ = (λ_1 ≥ ⋯ ≥ λ_N) a dominant weight of GL_N with λ_i − λ_j + (j − i) ≤ p for all i < j. The project realises the induced module ∇(λ) = H^0(λ) as the space of polynomials in the entries of an N×N matrix X that are homogeneous of degree λ_j − λ_N in the j-th column and invariant under adding a multiple of an earlier column to a later one, with GL_N acting by f(X) ↦ det(g)^{λ_N} f(g^T X). The Lean text claims that this module is nonzero and that every k-subspace of it that is stable under GL_N(A), after base change to A, for every commutative k-algebra A is either zero or the whole module.

```
λ ∈ X^+(GL_N), ⟨λ + ρ, α^∨⟩ ≤ p for all α > 0 ⟹ H^0(λ) ≠ 0 and H^0(λ) is a simple GL_N-module
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a split reductive group over a field k of characteristic p > 0 and λ a dominant weight with ⟨λ + ρ, β^∨⟩ ≤ p for every positive root β. Then the induced module H^0(λ) = ind_B^G λ is simple, so H^0(λ) = L(λ) = V(λ). The reference is J. C. Jantzen, Representations of Algebraic Groups, 2nd edition, American Mathematical Society 2003, Part II, Corollary 5.6.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only G = GL_N, while Jantzen's result holds for every split reductive group.
- The project models H^0(λ) as the polynomials on N × N matrices with column degrees λ_j − λ_N that are invariant under adding a multiple of an earlier column to a later one, with g acting by f(X) ↦ det(g)^{λ_N} f(gᵀX), and for the weights (1, 0, …, 0) and (1, 1, 0, …, 0) this model gives the natural representation and its second exterior power, which are the induced modules of those weights.
- The hypothesis λ_i − λ_j + (j − i) ≤ p for all i < j says that ⟨λ + ρ, α^∨⟩ ≤ p for every positive root α, which is the closure of the lowest alcove and is equivalent to λ_1 − λ_N + N − 1 ≤ p.
- Stability of a subspace is tested after base change to every commutative k-algebra, which is the scheme-theoretic notion of a G-submodule.
- The conclusion asserts only that H^0(λ) is nonzero and simple and leaves out the equalities H^0(λ) = L(λ) = V(λ).

On emptiness the check wrote this. No emptiness was found, although the hypothesis can be met only when N ≤ p + 1, which is the same limit that the published lowest-alcove condition imposes.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The hypothesis is exactly the closure of the lowest p-alcove for GL_N, and on the weights (1, 0, …, 0) and (1, 1, 0, …, 0) the polynomial model gives the natural representation and its second exterior power, as the induced module should.

### 49, `CuspidalRestrictsToInduced`

The proposition is `GlobalTheory.Published.CuspidalRestrictsToInduced`. Its vocabulary has 13 definitions of the project, and the proof of the theorem `CompanionTheory.Mirab.Restr.cuspidalRestrictsToInduced` that states it rests on 313 declarations.

Let k be a finite field, n a natural number and ψ₀ a nontrivial additive character of k. Let ρ be a finite-dimensional irreducible complex representation of GL_{n+1}(k) that is cuspidal, meaning that for every proper standard parabolic subgroup the unipotent radical fixes no nonzero vector. Then the restriction of ρ to the mirabolic subgroup P of matrices with last row (0, …, 0, 1) is isomorphic to the representation of P induced from the character u ↦ ψ₀(u_{12} + u_{23} + ⋯ + u_{n,n+1}) of the upper unitriangular group U.

```
ρ irreducible cuspidal representation of GL_{n+1}(F_q), ψ₀ ≠ 1 ⟹ ρ|_{P_{n+1}} ≅ Ind_{U_{n+1}}^{P_{n+1}} ψ with ψ(u) = ψ₀(∑_i u_{i,i+1})
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let π be an irreducible cuspidal representation of GL_n(F_q) and ψ a nondegenerate character of the upper unitriangular group U_n. Then the restriction of π to the mirabolic subgroup P_n is isomorphic to Ind_{U_n}^{P_n} ψ, which is irreducible. The reference is S. I. Gelfand, Representations of the full linear group over a finite field, Mathematics of the USSR Sbornik 12, 1970.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- The Lean text uses the coinduced representation, which for finite groups is isomorphic to the induced one.
- Cuspidality is tested on the unipotent radicals of the standard parabolic subgroups given by monotone non-constant block functions, which is equivalent to the usual definition because every parabolic subgroup is conjugate to a standard one.
- The Lean text states only the implication from cuspidality to the isomorphism and leaves out the converse.
- The Lean text does not state that the induced representation of the mirabolic subgroup is irreducible, which Gelfand's statement adds as a separate fact about the mirabolic subgroup.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The groups, the generic character and the cuspidality condition all match the standard ones, and the Lean text leaves out only the converse direction, which the name of the proposition does not refer to.

### 50, `DepthZeroJacquetInjective`

The proposition is `GlobalTheory.Published.DepthZeroJacquetInjective`. Its vocabulary has 13 definitions of the project, and the proof of the theorem `GlobalTheory.DepthZeroJac.depthZeroJacquetInjective` that states it rests on 156 declarations.

Let k be a non-archimedean local field with ring of integers O, let K = GL_n(O) and let K_1 be the kernel of reduction from K to GL_n of the residue field. Let P be the parabolic subgroup of GL_n(k) of matrices that are block upper triangular for an ordered partition of the n indices, not necessarily into intervals, into blocks of sizes d_1, …, d_s, and let N be its unipotent radical, the kernel of the projection of P onto its diagonal blocks. Let π be a smooth irreducible complex representation of GL_n(k) on V. The Lean text claims that every v ∈ V fixed by the subgroup generated by K_1 and N ∩ K whose image in the Jacquet module V_N is zero is itself zero, so the projection from V^{K_1(N∩K)} to V_N is injective. The dossier does not show the definition of the Jacquet module, and I read it as V divided by the span of the vectors π(u)w − w with u ∈ N, which is what the listed definition twKer gives with the trivial character.

```
π smooth irreducible representation of GL_n(k), P = MN ⊇ diagonal torus ⟹ V^{K_1·(N∩K)} → V_N = V/⟨π(u)w − w | u ∈ N⟩ is injective
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a reductive p-adic group, x a point of the building in the apartment of a Levi subgroup M of a parabolic subgroup P = MN, and (π, V) a smooth admissible representation. Then the projection V → V_N restricts to an isomorphism from the vectors fixed by G_{x,0+}N_{x,0} onto the vectors of V_N fixed by M_{x,0+}, so parahoric restriction commutes with the Jacquet functor. The reference is A. Moy and G. Prasad, Jacquet functors and unrefined minimal K-types, Commentarii Mathematici Helvetici 71, 1996.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text claims only that the projection from the vectors fixed by K_1(N ∩ K) to the Jacquet module is injective, while the published result also identifies the image with the vectors of V_N fixed by M ∩ K_1.
- The Lean text treats only GL_n at the vertex fixed by GL_n(O) and only the depth-zero subgroups K_1 and N ∩ K, while the published result covers general reductive groups, general points of the building and higher depths.
- The parabolic subgroups in the Lean text are block upper triangular for an ordered partition whose blocks need not be intervals, which gives every parabolic subgroup containing the diagonal torus, and each such subgroup is conjugate to a standard one by a permutation matrix in GL_n(O).
- The Lean text assumes π irreducible, while the published result does not need irreducibility.
- The dossier does not show the definition of Jacquet, and the listed definition twKer supports reading it as V divided by the span of the vectors π(u)w − w with u ∈ N.

On emptiness the check wrote this. No emptiness was found, and the statement is trivially true only in special instances, namely for the partition with a single block, where N is trivial, and for representations without nonzero K_1-fixed vectors.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean claim is the injective half of the depth-zero compatibility between invariants and Jacquet modules, which I checked on unramified principal series and depth-zero supercuspidal representations of GL_2, but I cannot confirm the exact published wording and the dossier omits the definition of the Jacquet module.

### 51, `KudlaSplittingSplitUnitary`

The proposition is `GlobalTheory.Published.KudlaSplittingSplitUnitary`. Its vocabulary has 13 definitions of the project, and the proof of the theorem `GlobalTheory.kudlaSplittingSplitUnitary` that states it rests on 1,737 declarations.

Let F be a nonarchimedean local field of characteristic zero and E a quadratic field extension of F with nontrivial involution c, given by a unit δ with c(δ) = −δ such that 1 and δ form an F-basis of E. Let Q be an invertible hermitian m×m matrix over E, ψ a continuous nontrivial unitary character of F, and χ a continuous unitary character of E^× that is 1 on norms from E^× and (−1)^m on the other elements of F^×. The text asserts that there is a representation ω of U(n,n) = {g ∈ GL_{2n}(E) | g^T J c(g) = J}, with J = [[0,1],[−1,0]], on the space of locally constant compactly supported functions on M_{m×n}(E), and that ω is smooth and preserves the L² norm for every Haar measure. The representation satisfies ρ(w)ω(g) = ω(g)ρ(wg) for all g and all w = (w₁,w₂) ∈ M_{m×2n}(E). Here (ρ(w)φ)(x) = ψ(⟨(x,0),(0,w₂)⟩ + ½⟨(w₁,0),(0,w₂)⟩)φ(x + w₁) and ⟨w,w'⟩ = ½ Tr_{E/F} tr(w^T Q c(w') J^T). On m(a) = diag(a, c(a)^{−T}) it acts by (ω(m(a))φ)(x) = χ(det a)|N_{E/F}(det a)|_F^{m/2} φ(xa).

```
F p-adic of char 0, E/F quadratic, Q = Q* ∈ GL_m(E), ψ ≠ 1, χ|_{F^×} = η_{E/F}^m ⇒ ∃ ω ∈ Rep(U(n,n), S(M_{m×n}(E))) smooth, L²-isometric, ρ_ψ(w)ω(g) = ω(g)ρ_ψ(wg), ω(m(a))φ(x) = χ(det a)|det a|_E^{m/2} φ(xa)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let E/F be a quadratic extension of local fields, V an m-dimensional hermitian space and W a skew-hermitian space over E. The metaplectic cover of Sp(Res_{E/F} V⊗W) splits over U(W), and the splittings correspond to characters χ of E^× with χ|_{F^×} = ε_{E/F}^m. In the Schrödinger model for split W of dimension 2n, the Siegel Levi acts by ω(m(a))φ(x) = χ(det a)|det a|_E^{m/2} φ(xa), and there are matching formulas for the unipotent radical and the Weyl element. S. S. Kudla, Splitting metaplectic covers of dual reductive pairs, Israel J. Math. 87 (1994).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only the split skew-hermitian space with the standard matrix J = [[0,1],[−1,0]], so the group is the quasi-split U(n,n), while Kudla treats every skew-hermitian space W.
- The Lean text treats only nonarchimedean local fields F of characteristic zero, while Kudla's splitting also covers archimedean fields.
- The Lean text requires E to be a field, so the split algebra F × F is excluded.
- The Lean text gives the action only on the Siegel Levi subgroup and leaves out the published formulas for the unipotent radical and the Weyl element, although the covariance relation and the Levi formula together already determine ω.
- The Lean text replaces the splitting homomorphism into the metaplectic group by the existence of a smooth L²-isometric representation that intertwines the Schrödinger-model Heisenberg operators, which carries the same information by the Stone–von Neumann theorem.
- The Lean text asserts existence for each admissible χ and states neither uniqueness nor the classification of the splittings by the characters χ, and it does not treat the splitting over U(V).

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The group, the Schrödinger model and the Levi formula are written out in the dossier, and a direct check shows that the Levi formula is compatible with the covariance relation and that U(n,n) preserves the symplectic form, as the standard description of Kudla's splitting requires.

### 52, `AdmissibleCoefficientsAnalytic`

The proposition is `GlobalTheory.Published.AdmissibleCoefficientsAnalytic`. Its vocabulary has 14 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.Hypotheses₂.admissibleCoefficientsAnalytic` that states it rests on 939 declarations.

For every n and sign vector ε, the text writes J = diag(±1) for the matrix of ε, U(p,q) = {g | g*Jg = J}, and K = U(p)×U(q) for the unitary matrices that commute with J. Let π assign bounded operators on a complex Hilbert space H to n×n complex matrices. Assume that π is multiplicative on U(p,q) with π(1) = 1, strongly continuous on U(p,q) and isometric on K. Assume also that π is admissible, meaning that for every weight Λ ∈ ℝ^n the span of the irreducible K-stable finite-dimensional subspaces of highest weight Λ, taken with respect to the compact positive roots e_a − e_b with a < b and ε_a = ε_b, is finite-dimensional. Then for any two K-finite vectors v and w the matrix coefficient g ↦ ⟨w, π(g)v⟩ is real analytic on U(p,q), in the sense that near every point of U(p,q) it agrees with a real-analytic function on an open subset of ℂ^{n×n}.

```
π admissible representation of U(p,q) on H, v, w ∈ H_K ⇒ g ↦ ⟨w, π(g)v⟩ is real analytic on U(p,q)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let π be a continuous representation of a real reductive group G on a Hilbert space such that π restricted to a maximal compact subgroup K is unitary and every K-type occurs with finite multiplicity. Then every K-finite vector v is an analytic vector, so g ↦ ⟨w, π(g)v⟩ is real analytic on G for every vector w. Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Trans. Amer. Math. Soc. 75 (1953).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only U(p,q) in its matrix realization with K = U(p)×U(q), while Harish-Chandra's theorem covers every real reductive group of his class.
- The Lean text requires both v and w to be K-finite through the hypotheses IsKFin ε π v and IsKFin ε π w, while the published theorem needs only v to be K-finite and allows any vector w.
- The Lean text treats Hilbert space representations that act isometrically on K, while Harish-Chandra proved the result for Banach space representations with no unitarity condition on K.
- Admissibility is written as finite dimensionality of the sum of the irreducible K-stable subspaces of each highest weight Λ with respect to the compact positive roots e_a − e_b with a < b and ε_a = ε_b, which is the usual finite multiplicity condition.
- Real analyticity is expressed through local real-analytic extensions to open subsets of ℂ^{n×n}, which is equivalent to analyticity on the submanifold U(p,q).

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The definitions give the standard notions of representation, K-finiteness, admissibility through highest weights, and analyticity on a submanifold for U(p,q), and the conclusion is a direct instance of Harish-Chandra's theorem.

### 53, `CuspidalMirabolic`

The proposition is `GlobalTheory.Published.CuspidalMirabolic`. Its vocabulary has 15 definitions of the project, and the proof of the theorem `GlobalTheory.cuspidalMirabolic_holds` that states it rests on 708 declarations.

The proposition joins two statements about complex representations of GL_{n+1}(k) over a finite field k. The first says that for every finite field k and every n there are a number d and an irreducible cuspidal representation of GL_{n+1}(k) on ℂ^d. Here cuspidal means that for every proper standard parabolic subgroup, given by a monotone non-constant block function, only the zero vector is fixed by its unipotent radical. The second says the following for every finite field k, every n, every nontrivial additive character ψ₀ of k and every finite-dimensional irreducible cuspidal representation ρ of GL_{n+1}(k). The restriction of ρ to the mirabolic subgroup P of matrices with last row (0,…,0,1) is isomorphic to the representation induced from the upper unitriangular group U to P by the character u ↦ ψ₀(Σ_{i=1}^{n} u_{i,i+1}).

```
(∀ k finite, ∀ N ≥ 1, ∃ π ∈ Irr(GL_N(k)) cuspidal) ∧ (∀ k, N ≥ 1, ψ₀ ≠ 1, π ∈ Irr(GL_N(k)) cuspidal ⇒ π|_{P_N} ≅ Ind_{U_N}^{P_N} ψ)
```

The theorem that the name points to, as the first reader states it from its own knowledge. For every finite field F_q and every n ≥ 1 the group GL_n(F_q) has irreducible cuspidal representations, one for each Frobenius orbit of regular characters of F_{q^n}^× (Green). The restriction of an irreducible cuspidal representation of GL_n(F_q) to the mirabolic subgroup P_n is irreducible and isomorphic to Ind_{U_n}^{P_n} ψ, where ψ is a generic character of the upper unitriangular group. S. I. Gelfand, Representations of the full linear group over a finite field, Math. USSR-Sbornik 12 (1970).

The first reader takes the proposition for the same statement and the second reader for a stronger statement. The check takes it for a stronger statement.

The check confirmed these differences from the Lean text.

- The Lean text adds a separate conjunct CuspidalExists, which says that GL_{n+1}(k) over every finite field has an irreducible cuspidal representation, and this is Green's existence result and not part of Gelfand's restriction theorem.
- The existence conjunct asserts only that some irreducible cuspidal representation exists and gives neither Green's count nor his parametrization.
- The restriction conjunct gives only the isomorphism of the restriction of ρ to the mirabolic subgroup with the representation induced from the generic character, and it does not state that this representation is irreducible.
- The restriction conjunct states only the direction from cuspidality to the isomorphism and not the converse characterization of cuspidal representations by their mirabolic restriction.
- The induced representation is Mathlib's coinduced representation, which for finite groups is isomorphic to the induced one, so this is a difference of writing only.

The check gives this reason for its judgement. A calls the relation same although its own differences list an added conjunct and omitted parts, and B calls it stronger, and I judge it stronger because the restriction conjunct is exactly the core claim of Gelfand's theorem and the existence conjunct is a further true theorem that the restriction claim does not imply, while the irreducibility of the induced representation and the converse direction are separate statements that only some sources include in the theorem.

On emptiness the check wrote this. None found, because cuspidality holds for every representation only for GL_1, where every irreducible representation is cuspidal by the standard convention.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The cuspidality condition, the mirabolic subgroup and the generic character are the standard ones and the isomorphism is exactly Gelfand's, but the proposition joins two published results, so the published statement to compare against can be chosen in more than one way.

### 54, `InfinitesimalEquivalence`

The proposition is `GlobalTheory.Published.InfinitesimalEquivalence`. Its vocabulary has 15 definitions of the project, and the proof of the theorem `GlobalTheory.GKPort.Closure.infinitesimalEquivalence_unitaryGroupPQ` that states it rests on 1,227 declarations.

For every n and sign vector ε, which give U(p,q) and K = U(p)×U(q), take nonzero complex Hilbert spaces H₁ and H₂ with strongly continuous unitary representations σ₁ and σ₂ of U(p,q). Both representations are irreducible, which means that 0 and the whole space are their only closed invariant subspaces. Let e be a linear bijection between the spaces of K-finite vectors that commutes with σ(k) for k ∈ K and with the derived action of every X in 𝔲(p,q) = {X | X*J + JX = 0}, where the derived action is the derivative of t ↦ σ(exp tX)v at t = 0. Then there are a unitary isomorphism U from H₁ onto H₂ with Uσ₁(g) = σ₂(g)U for every g ∈ U(p,q) and a real number c > 0 with Uv = c·e(v) for every K-finite vector v of σ₁.

```
σ₁, σ₂ irreducible unitary representations of U(p,q), e a (𝔤,K)-isomorphism from H₁^{K-fin} to H₂^{K-fin} ⇒ ∃ U unitary, c > 0, Uσ₁(g) = σ₂(g)U ∀ g, U|_{H₁^{K-fin}} = c·e
```

The theorem that the name points to, as the first reader states it from its own knowledge. Two irreducible unitary representations of a real reductive group G are unitarily equivalent if and only if their Harish-Chandra modules of K-finite vectors are isomorphic as (𝔤,K)-modules. A. W. Knapp, Representation Theory of Semisimple Groups, An Overview Based on Examples (1986).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only U(p,q) with K = U(p)×U(q), while Harish-Chandra's theorem holds for every real reductive group of his class.
- The Lean conclusion adds that U restricts on K-finite vectors to a positive multiple c·e of the given isomorphism, which follows from Schur's lemma for the irreducible Harish-Chandra module after U is multiplied by a phase.
- The Lean text states only the direction from infinitesimal equivalence to unitary equivalence.
- The derived action is Mathlib's derivative, which is zero where the derivative does not exist, and the Lie algebra condition on e applies only when dRep σ₁ X v is again K-finite, and neither feature changes the content because the K-finite vectors of an irreducible unitary representation are smooth and form a 𝔤-stable space.

The check found no emptiness.

The check found these errors in the first reader's account of the Lean text, and the account above is printed as the reader wrote it.

- A says that e commutes with the derived action of every X in 𝔲(p,q), while IsGKHom requires e(dRep σ₁ X v) = dRep σ₂ X (e v) only when dRep σ₁ X v is itself a K-finite vector, although this guard is always met for irreducible unitary representations.

The first reader's confidence is high. The hypotheses state irreducible unitary representations and (𝔤,K)-isomorphisms for U(p,q) in the standard way, and the extra scalar clause is a routine consequence of the published theorem.

### 55, `GreenCuspidal`

The proposition is `GlobalTheory.Published.GreenCuspidal`. Its vocabulary has 16 definitions of the project, and the proof of the theorem `PositivityTheory.Stage1.PM.greenCuspidal` that states it rests on 601 declarations.

The text fixes a prime p (called g in the text), a label datum L and an integer d > 0. A label datum is a multiplicative map from the algebraic closure of F_p to ℂ that is injective on nonzero elements, together with norm-compatible generators ζ_d of the groups F_{p^d}^×. The text claims a map τ from polynomials over F_p to complex functions on GL_d(F_p) such that, for every monic irreducible P of degree d with P(0) ≠ 0, τ(P) is the character of an irreducible cuspidal representation with τ(P)(1) = ∏_{i=1}^{d−1}(p^i − 1). Cuspidality is written as the vanishing of the averages of the character over the unipotent radicals of the maximal standard parabolic subgroups. For such P and every y whose characteristic polynomial is irreducible, τ(P)(y) = (−1)^{d−1} Σ_{i=0}^{d−1} θ_x(z^{p^i}) for every root x of P and every eigenvalue z of y, where θ_x(ζ_d^k) = L(x)^k, and τ is injective on such P, and every irreducible cuspidal character of GL_d(F_p) equals τ(P) for some such P.

```
∀ p, L, d > 0 ∃ τ bijective from {P ∈ F_p[X] monic irreducible, deg P = d, P(0) ≠ 0} onto cuspidal Irr(GL_d(F_p)), τ(P)(1) = ∏_{i=1}^{d−1}(p^i − 1), τ(P)(y) = (−1)^{d−1} Σ_{i=0}^{d−1} θ_x(z^{p^i}) for elliptic y with eigenvalue z
```

The theorem that the name points to, as the first reader states it from its own knowledge. The irreducible cuspidal characters of GL_n(F_q) correspond bijectively to the Frobenius orbits of regular characters θ of F_{q^n}^×. The character χ_θ has degree ∏_{i=1}^{n−1}(q^i − 1), and on a regular elliptic element with eigenvalue z it takes the value (−1)^{n−1} Σ_{i=0}^{n−1} θ(z^{q^i}), and Green also gives its values on all other classes. J. A. Green, The characters of the finite general linear groups, Trans. Amer. Math. Soc. 80 (1955).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only the prime fields ZMod g, while Green's theorem holds over every finite field F_q.
- Cuspidal characters are labelled by monic irreducible polynomials P of degree d with nonzero constant term instead of Frobenius orbits of regular characters of F_{g^d}^×, and the label datum supplies the bijection by sending a root x of P to the character θ_x that maps the chosen generator of F_{g^d}^× to teich(x).
- The Lean text states only the degree and the values on elements with irreducible characteristic polynomial, while Green's formula gives the values on all conjugacy classes.
- Cuspidality is tested only through the vanishing average of the character over the unipotent radicals of the maximal standard parabolic subgroups, which is equivalent to the usual condition because the unipotent radical of every proper standard parabolic subgroup contains that of a maximal one.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The bijection, the degree and the elliptic values agree with Green's theorem once the polynomial labels are turned into regular characters, a label datum always exists by a Brauer lift and a compactness argument, and the only narrowing is to prime fields.

### 56, `QuadraticClassFieldTheory`

The proposition is `GlobalTheory.Published.QuadraticClassFieldTheory`. Its vocabulary has 16 definitions of the project, and the proof of the theorem `PositivityTheory.Stage1.PM.quadraticClassFieldTheory` that states it rests on 436 declarations.

The first part concerns a quadratic extension L/K of number fields. At each place v of K, the sign η_v(a) is 1 when a ∈ K_v^× is a norm from K_v ⊗_K L and −1 otherwise. This part asserts that each η_v is multiplicative, that an element of K^× is a norm from L exactly when it is a local norm at every place, and that every t ∈ K^× is a local norm at almost all finite places with ∏_v η_v(t) = 1. It also asserts that a family (x_v) of local units that are norms at almost all places becomes a local norm everywhere after division by some t ∈ K^× exactly when ∏_v η_v(x_v) = 1, and that some such family has product −1. The second part takes number fields F ⊂ E and F ⊂ K ⊂ L with E/F and L/K quadratic and L generated over K by E, and it asserts that η_{L/K}(x) = η_{E/F}(N_{B/F_v}(x)) at every finite or infinite place v of F, for every finite field extension B of F_v with a compatible K-algebra structure and every x ∈ B^×.

```
L/K quadratic ⇒ η_v multiplicative, K^× ∩ ∏_v N_v = N(L^×), ∏_v η_v(t) = 1, ∏_v η_v(x_v) = 1 ⇔ x ∈ K^× · ∏_v N_v, ∏_v η_v onto {±1}, and L = KE ⇒ η_{L/K,B}(x) = η_{E/F,F_v}(N_{B/F_v} x)
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a quadratic extension L/K of number fields, the local norm group has index two at every nonsplit place, an element of K^× is a global norm if and only if it is a local norm everywhere (Hasse), and ∏_v η_v(t) = 1 for t ∈ K^× (Hilbert reciprocity), with K^× → A_K^×/N(A_L^×) → {±1} → 1 exact. Functoriality of the local reciprocity map gives η_{KE/K} = η_{E/F} ∘ N_{K/F} locally. J. Neukirch, Algebraic Number Theory (1999).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only quadratic extensions, which is the degree-two case of local and global class field theory.
- The local clause LocalCharacters says only that each η_v is multiplicative, which means that the local norm group has index at most two, and it does not say that the index is exactly two at the nonsplit places.
- The reciprocity sequence is stated for families in the full product of the groups K_v^× that are local norms at almost all finite places instead of ideles, which gives the same content because such a family agrees modulo local norms with an idele.
- The reciprocity map appears only through the sign η_v of membership in the local norm group, so the Lean text never mentions the Artin map or its values in Gal(L/K).
- The base change clause quantifies over every finite field extension B of F_v with a compatible K-algebra structure, which includes the completions of K above v and is still a consequence of local class field theory.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. Each clause is a standard consequence of class field theory and I checked them one by one, but the proposition bundles several results and there is no single published statement to compare it with.

### 57, `GlobalArtinReciprocity`

The proposition is `GlobalTheory.Published.GlobalArtinReciprocity`. Its vocabulary has 17 definitions of the project, and the proof of the theorem `CompanionTheory.FamInh.globalArtin` that states it rests on 3,761 declarations.

For every number field E and algebraic closure Ω of E there is a group homomorphism art from the idele group of E to the quotient of Gal(Ω/E) by the closure of its commutator subgroup. The map art is continuous, surjective and open, and its kernel is the closure of the subgroup generated by E^× and the identity component of the infinite ideles. Let v be a finite place and A a valuation ring of Ω above v. An element is the image of a unit of E_v exactly when it is the image of an inertia element of A. It is the image of a uniformizer of E_v exactly when it is the image of σ^{−1} for some σ in the decomposition group of A that acts as x ↦ x^{Nv} on the residue field, and the closure of the image of E_v^× is the image of the decomposition group of A.

```
∃ art ∈ Hom(A_E^×, Gal(Ω/E)^{ab}) open onto, ker art = closure(E^×(E_∞^×)^0), art(O_v^×) = I_v^{ab}, art(ϖ_v O_v^×) = Frob_v^{−1} I_v^{ab}, closure art(E_v^×) = D_v^{ab}
```

The theorem that the name points to, as the first reader states it from its own knowledge. For a number field E there is a unique continuous surjective homomorphism from A_E^× onto Gal(E^{ab}/E) whose kernel is the closure of E^×(E_∞^×)^0 and whose restriction to each E_v^× is the local reciprocity map. This homomorphism therefore maps O_v^× onto the inertia group and a uniformizer to a Frobenius element modulo inertia, and its image on E_v^× is dense in the decomposition group. J. Tate, Global class field theory, in J. W. S. Cassels and A. Fröhlich, Algebraic Number Theory (1967).

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean text sends uniformizers to inverses of arithmetic Frobenius elements, which is the geometric normalization, and composing with inversion in the abelian group turns it into the classical arithmetic one.
- The Lean text asserts existence alone and states no uniqueness, although continuity, the kernel condition and the inertia and Frobenius conditions already force uniqueness by the usual weak approximation argument, so the map is pinned down after all.
- Local-global compatibility is expressed only through the images of the local units, of the uniformizers and of E_v^×, and not as equality with the local reciprocity maps on each E_v^×.
- The archimedean places enter only through the kernel, and the Lean text says nothing about the image of E_v^× at a real place being generated by a complex conjugation.
- The Lean text adds that art is an open quotient map, which follows from the classical theorem because the induced map from the compact quotient of the ideles onto the abelianized Galois group is a homeomorphism.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The kernel, the surjectivity and the local conditions match the classical law in Deligne's normalization, and the Lean statement is weaker because it leaves out the uniqueness and the full local compatibility.

### 58, `KernelFiniteFlatSt`

The proposition is `GlobalTheory.Published.KernelFiniteFlatSt`. Its vocabulary has 17 definitions of the project, and the proof of the theorem `GlobalTheory.kernelFiniteFlat_holds` that states it rests on 3,378 declarations.

Let V be a Noetherian ring and A an abelian scheme over Spec V, that is, a commutative group scheme that is smooth and proper with geometrically connected fibres. Let L be a line bundle on A that is relatively ample, which means that over each affine open U of Spec V some power L^N embeds A_U as a closed subscheme of a projective space over U. Then there is a closed subscheme Z of A that is finite and flat over V. For every V-scheme T, a point x ∈ A(T) factors through Z exactly when the line bundle t_x^*L ⊗ pr₂^*L^{−1} on T ×_V A is trivial over T' ×_V A for each member T' of some open cover of T. In other words Z represents the functor K(L) of points whose translation preserves L up to a bundle from the base.

```
A abelian scheme over Spec V, V Noetherian, L relatively ample ⇒ K(L) = {x ∈ A(T) | t_x^*L ⊗ L^{−1} locally trivial over T} is represented by a closed subscheme of A that is finite and flat over V
```

The theorem that the name points to, as the first reader states it from its own knowledge. For an abelian scheme A over S and a line bundle L on A, the functor K(L) of points x for which t_x^*L ⊗ L^{−1} comes from the base is represented by a closed subgroup scheme of A, namely the kernel of φ_L from A to its dual. If L is relatively ample then φ_L is an isogeny, so K(L) is a finite flat group scheme over S. D. Mumford, J. Fogarty and F. Kirwan, Geometric Invariant Theory, Chapter 6 (1994).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The base is the spectrum of a Noetherian ring, while the published result holds over more general base schemes.
- The Lean text says only that Z is a closed subscheme of A that is finite and flat over the base and represents K(L), and it does not say that Z is a subgroup scheme, that it is the kernel of φ_L from A to the dual abelian scheme, or that its rank is χ(L)².
- Membership in K(L) is written as triviality of m_x^*L ⊗ pr₂^*L^{−1} over T' ×_V A for the members T' of an open cover of T, which agrees with the usual condition that this bundle comes from the base because the direct image of the structure sheaf of an abelian scheme is the structure sheaf of the base.
- Relative ampleness is written as the existence, over each affine open U of the base, of sections of some power L^N whose charts give a closed immersion of A_U into projective space over U, which is equivalent to the usual definition for a proper scheme over a Noetherian base.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. By the seesaw principle the membership condition matches the usual definition of K(L), and the ampleness condition matches relative ampleness, but the cocycle encodings of line bundles are intricate, so I checked them only for their intended meaning.

### 59, `LeviSubmoduleDense`

The proposition is `GlobalTheory.Published.LeviSubmoduleDense`. Its vocabulary has 17 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.Hypotheses₂.leviSubmoduleDense` that states it rests on 547 declarations.

Fix n, a sign vector ε that gives U(p,q), and a strictly increasing flag 0 = W_0 ⊊ W_1 ⊊ … ⊊ W_a of subspaces of ℂ^n whose top member W_a is totally isotropic for the form x*Jy. Let M be the subgroup of those g ∈ U(p,q) such that both g and g* preserve every W_i and the restriction of g to each W_i has determinant of absolute value 1. Let σ be a strongly continuous irreducible unitary representation of M on a Hilbert space V. Let S be a nonzero subspace of V whose vectors are all (K∩M)-finite. Suppose that for every X with exp(tX) ∈ M for all real t and every v ∈ S, the derivative of σ(exp tX)v at t = 0 exists and lies in S. Then S is dense in V.

```
M = {g ∈ U(p,q) | g, g* preserve each W_i, |det(g|W_i)| = 1}, σ irreducible unitary representation of M, 0 ≠ S ⊂ V^{(K∩M)-fin}, 𝔪·S ⊂ S ⇒ closure(S) = V
```

The theorem that the name points to, as the first reader states it from its own knowledge. For an irreducible unitary representation of a real reductive group G with maximal compact subgroup K, the closure of every nonzero (𝔤,K)-submodule of the K-finite vectors is a closed invariant subspace and hence the whole space. For connected G, the closure of any 𝔤-stable subspace of analytic vectors is G-invariant, and K-finite vectors of admissible representations are analytic. Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Trans. Amer. Math. Soc. 75 (1953).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text treats only the groups ⁰M attached to isotropic flags in U(p,q), which are products of groups {g ∈ GL_m(ℂ) | |det g| = 1} with a smaller U(p',q') and include U(p,q) itself as the case a = 0 of the empty flag, while Harish-Chandra's result holds for every real reductive group.
- The subspace S is required to consist of (K∩M)-finite vectors and to be stable under the Lie algebra of M, but it is not required to be stable under K∩M, which does no harm because M is connected and the K-finite vectors of an irreducible unitary representation are analytic.
- Irreducibility and unitarity on a Hilbert space are assumed, while the published density statement holds for irreducible admissible Banach representations.
- The Lean text gives only the density and leaves out the irreducibility of the Harish-Chandra module and the correspondence between closed invariant subspaces and submodules.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The group M and the hypotheses are encoded faithfully, but the Lean hypothesis on S differs in form from the published (𝔤,K)-submodule hypothesis, and the two can be matched only by using that M is connected and that K-finite vectors are analytic.

### 60, `PotentialGoodReductionSt`

The proposition is `GlobalTheory.Published.PotentialGoodReductionSt`. Its vocabulary has 17 definitions of the project, and the proof of the theorem `UpperTheory.Lit.potentialGoodReduction` that states it rests on 9,253 declarations.

Let R be a discrete valuation ring with perfect residue field and fraction field K, Ω a separable closure of K, and V a valuation ring of Ω lying over R, with inertia group I_V ⊂ Gal(Ω/K). For every abelian variety A over K and every prime l different from the residue characteristic, A has potential good reduction exactly when the image of I_V in the automorphisms of the l-adic Tate module of A(Ω) is finite. Potential good reduction means that there are a finite extension L/K and a discrete valuation ring W with fraction field L lying over R such that A_L is the generic fibre of an abelian scheme over W, as a group scheme.

```
A/K abelian variety, l ≠ char k, k perfect ⇒ (A has potential good reduction ⇔ ρ_l(I_V) ⊂ GL(T_l A) is finite)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be a field with a discrete valuation, A an abelian variety over K and l a prime different from the residue characteristic. Then A has potential good reduction if and only if the image of the inertia group in Aut(T_l A) is finite, which follows from the Néron–Ogg–Shafarevich criterion. J.-P. Serre and J. Tate, Good reduction of abelian varieties, Annals of Mathematics 88 (1968).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean text assumes that the residue field of R is perfect, which the Serre–Tate criterion does not need.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Good reduction, potential good reduction, inertia and the Tate module are defined in the standard way, and the only narrowing is the extra assumption that the residue field is perfect.

### 61, `AdmissibleClosure`

The proposition is `GlobalTheory.Published.AdmissibleClosure`. Its vocabulary has 18 definitions of the project, and the proof of the theorem `GlobalTheory.GKPort.Closure.admissibleClosure_gKSubmodule` that states it rests on 661 declarations.

For every n, every sign vector ε in {true, false}^n, every complex Hilbert space H and every map σ from complex n×n matrices to bounded operators on H whose restriction to G = U(J) = {g | gᴴJg = J}, with J = diag(±1) read off from ε, is a strongly continuous unitary representation, the claim below holds for every complex subspace V of H. Suppose every vector of V is smooth and K-finite for K = G ∩ U(n), V is stable under K and under the derived action dσ(X) of every X in the Lie algebra {X | XᴴJ + JX = 0}, and for every weight Λ the sum of the irreducible K-stable subspaces of V with highest weight Λ, taken with respect to the compact roots e_a − e_b with a < b and ε_a = ε_b, is finite-dimensional. Then the closure of V is stable under σ(g) for every g in G, and every K-finite vector in the closure of V already lies in V.

```
∀ n, ε, H, σ unitary on U(J), ∀ V ≤ H with V ⊆ H^∞ ∩ H_K, σ(K)V ⊆ V, dσ(g)V ⊆ V and dim V(Λ) < ∞ for all Λ ⟹ σ(G) cl(V) ⊆ cl(V) and cl(V) ∩ H_K ⊆ V
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a real reductive group with maximal compact subgroup K and let π be an admissible representation of G on a Hilbert space H. Then V ↦ cl(V) is a bijection from the (g,K)-submodules of the space H_K of K-finite vectors onto the closed G-invariant subspaces of H, with inverse W ↦ W_K. A standard reference is A. W. Knapp, Representation Theory of Semisimple Groups, An Overview Based on Examples, 1986, Chapter VIII.

The first reader takes the proposition for a different statement and the second reader for a special case. The check takes it for a different statement.

The check confirmed these differences from the Lean text.

- The Lean statement concerns only the groups U(p,q), realised as U(J) = {g | gᴴJg = J} for a diagonal sign matrix J, while the published theorem covers real reductive groups.
- The Lean statement requires σ to be unitary on U(J), while the published theorem allows admissible Hilbert space representations that need not be unitary.
- The Lean statement asks finite K-multiplicities only of the subspace V and lets H have infinite K-multiplicities, while the published theorem assumes the whole representation H to be admissible.
- The Lean statement assumes explicitly that every vector of V is smooth along finite products of one-parameter subgroups, which the published theorem obtains from the admissibility of H.
- The Lean conclusion gives only the direction from submodules to closed subspaces, namely that the closure of V is invariant under U(J) and that its K-finite vectors lie in V, and it omits that every closed invariant subspace is the closure of its K-finite vectors.
- K-types are described by highest weights for the diagonal torus with respect to the compact positive roots e_a − e_b with a < b and ε_a = ε_b, and the isotypic part of V is the algebraic sum of the irreducible K-stable subspaces of V with a given highest weight.

The check gives this reason for its judgement. I judge the relation different because the Lean text keeps only the direction from submodules to closed invariant subspaces and moves the admissibility hypothesis from H to V, so it neither follows from the published theorem by specialisation nor implies it, which rules out B's special case.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean statement is a true variant, because each vector of an admissible V is Z(g)-finite and hence analytic by Harish-Chandra's theorem, but it trades admissibility of H for admissibility of V and keeps only half of the correspondence, so it is neither an instance nor a generalisation of the standard theorem.

### 62, `L2ExtensionLogCanonical`

The proposition is `GlobalTheory.Published.L2ExtensionLogCanonical`. Its vocabulary has 18 definitions of the project, and the proof of the theorem `GlobalTheory.l2ExtensionLogCanonical'` that states it rests on 1,297 declarations.

Let n ≥ 1 and let Y be a compact Hausdorff second countable space with a weighted atlas A, which makes Y a compact complex manifold of dimension n with a group La of holomorphic line bundles given by transition cocycles and smooth local weights ph, a canonical bundle κ whose cocycle is the Jacobian determinant of the chart changes, and a volume measure μ with density e^{ph_κ} against Lebesgue measure in each chart. Assume that some bundle in La has a positive definite Levi form everywhere. Let E and L be bundles and s_1, …, s_n holomorphic sections of L whose common zero set Z is finite with nonzero Jacobian determinant Jac_s(P) at each P in Z, assume |s|²_L = Σ_k |s_k|² e^{−ph_L} ≤ 1 everywhere, put ψ = n log|s|²_L, and let δ > 0 be such that ph_E + αψ has a positive semidefinite Levi form off Z for every α in [1, 1+δ]. Then for every function f on Y there is a holomorphic section F of κ + E with F(P) = f(P) at each P in Z, read in the chart chosen for P, such that ∫ 2^n (1 + δ²ψ²)^{−1} |F|²_{κ+E} e^{−ψ} dμ ≤ (34/δ) · 2^{n+1}π^n/(n−1)! · Σ_{P∈Z} |f(P)/Jac_s(P)|² e^{−ph_E(P) + n·ph_L(P)}.

```
∀ f ∃ F ∈ H^0(Y, K_Y ⊗ E) with F = f on Z and ∫_Y 2^n (1 + δ²ψ²)^{−1} |F|² e^{−φ_E − ψ} dλ ≤ (34/δ)(2^{n+1}π^n/(n−1)!) Σ_{P∈Z} |f(P)|² e^{−φ_E(P) + nφ_L(P)} / |Jac s(P)|², where ψ = n log|s|²_{h_L} ≤ 0
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let X be a weakly pseudoconvex Kähler manifold, L a holomorphic line bundle with metric e^{−φ}, and ψ a quasi-plurisubharmonic function with neat analytic singularities that is log canonical along the reduced subvariety Y cut out by the multiplier ideal of ψ. If iΘ_L + α i∂∂̄ψ ≥ 0 for every α in [1, 1+δ], then every holomorphic section f of K_X ⊗ L on Y_reg with ∫ |f|² dV[ψ] < ∞ extends to a section F on X with ∫_X γ(δψ)|F|² e^{−ψ} dV_X ≤ (34/δ) ∫_{Y_reg} |f|² dV[ψ], where γ(x) = e^{−x/2} for x ≥ 0, γ(x) = 1/(1+x²) for x ≤ 0, and dV[ψ] is the Ohsawa residue measure. A standard reference is J.-P. Demailly, Extension of holomorphic functions defined on non reduced analytic subvarieties, Advanced Lectures in Mathematics 35.1, 2016, Theorem 2.8.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean statement takes a compact complex manifold that carries a line bundle with positive definite Levi form, hence a projective manifold, while the published theorem allows any weakly pseudoconvex Kähler manifold.
- The Lean weight ψ is n log Σ|s_k|²e^{−φ_L} for n sections of one line bundle with finitely many common zeros of nonzero Jacobian, so the log canonical locus is a finite reduced set of points, while the published theorem allows any quasi-plurisubharmonic ψ with neat analytic log canonical singularities.
- The weight of E is smooth in every chart, while the published theorem also admits singular metrics.
- The hypothesis Σ|s_k|²e^{−φ_L} ≤ 1 makes ψ ≤ 0, so only the branch 1/(1 + x²) of Demailly's function γ appears.
- The curvature hypothesis is imposed only outside the zero set, which is equivalent to the published hypothesis in the sense of currents because φ_E + αψ is bounded above near the finitely many zeros and extends plurisubharmonically across them.
- The residue measure is replaced by resConst n = 2^{n+1}π^n/(n−1)! times |f(P)/Jac(P)|²e^{−φ_E(P)+nφ_L(P)} at each zero, while Demailly's residue measure for ψ = n log|s|² at a nondegenerate zero, with the normalisation that gives the factor 2^n on the left, has mass 2^nπ^n/n!, so the Lean right side is 2n times larger and the Lean bound is weaker.
- At the points of the zero set the Lean function ψ takes the value 0 because Real.log 0 = 0 in Mathlib, which changes the integrand only on a finite set of μ-measure zero.

The check gives this reason for its judgement. A and B both judge a special case, but my own computation of the residue measure gives 2^nπ^n/n! as theirs does, so the Lean statement is a special case with a constant 2n times larger and therefore weaker than the published theorem.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The hypotheses and the weight (34/δ)(1+δ²ψ²)^{−1} match Demailly's theorem specialised to transversal zero sets of sections on a projective manifold, and projective space with n linear forms satisfies all hypotheses, but the normalisation of the residue constant could not be checked.

### 63, `MoyPrasadJacquetIso`

The proposition is `GlobalTheory.Published.MoyPrasadJacquetIso`. Its vocabulary has 18 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.MoyPrasadTop.moyPrasadJacquetIso` that states it rests on 205 declarations.

Let k be a non-archimedean local field with ring of integers O and maximal ideal p, let n = d_1 + … + d_s be a block decomposition indexed through a bijection e, and let P = MN be the corresponding block upper triangular parabolic subgroup of GL_n(k) with Levi subgroup M = ∏_a GL_{d_a}(k) and unipotent radical N. Let π be an admissible complex representation of GL_n(k) on V, meaning that every vector has an open stabiliser and every compact open subgroup has a finite-dimensional space of fixed vectors. Put K_0 = GL_n(O), let K_1 be the kernel of reduction GL_n(O) → GL_n(O/p), and let J be the subgroup generated by K_1 and N ∩ K_0. Then the quotient map from V to the Jacquet module V_N = V/span{π(u)v − v | u ∈ N} restricts to a bijection from the J-fixed vectors V^J onto the vectors of V_N fixed by the preimage of J in M, which is the principal congruence subgroup ∏_a K_1(GL_{d_a}) of M.

```
π admissible on GL_n(k) ⟹ V^{K_1·N(O)} → (V_N)^{M ∩ K_1}, v ↦ v mod V(N), is bijective
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a connected reductive p-adic group, P = MN a parabolic subgroup, x a point of the building of M and r ≥ 0. For a smooth representation V of G the natural projection maps V^{G_{x,r+}} onto (V_N)^{M_{x,r+}}, and at depth zero it identifies the N_{x,0}-coinvariants of V^{G_{x,0+}} with (V_N)^{M_{x,0+}}, so taking fixed vectors under the pro-unipotent radical of a parahoric commutes with the Jacquet functor. A standard reference is A. Moy and G. Prasad, Jacquet functors and unrefined minimal K-types, Commentarii Mathematici Helvetici 71, 1996.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The group is GL_n over a nonarchimedean local field, while the published theorem covers connected reductive p-adic groups.
- Only the hyperspecial point with stabiliser GL_n(𝒪), its principal congruence subgroup K₁ and depth zero are treated, while the published theorem allows any point of the building of M and any depth r ≥ 0.
- Only parabolic subgroups that are block upper triangular for the order of the blocks after the reindexing e are covered, which are the standard parabolic subgroups up to conjugation by a permutation matrix in GL_n(𝒪).
- The source space is V^J for the subgroup J generated by K₁ and N ∩ GL_n(𝒪), which is the space of N(𝒪)-invariants of V^{K₁} in place of N(𝒪/𝔭)-coinvariants, and the two agree for complex representations of the finite group N(𝒪/𝔭).
- The group acting on the Jacquet module is the preimage of J under the block diagonal embedding of M, which equals the principal congruence subgroup of M.
- The Lean statement assumes π admissible, while the depth zero result holds for all smooth representations, so this hypothesis only narrows the statement.
- The conclusion is a bijection of sets for the linear quotient map and says nothing about compatibility with the action of M(𝒪).

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The bijection agrees with the depth zero form of the Moy–Prasad result and checks out for principal series, Steinberg and depth zero supercuspidal representations of GL_2, but I recall the exact formulation in the paper only roughly.

### 64, `NeronOggShafarevichSt`

The proposition is `GlobalTheory.Published.NeronOggShafarevichSt`. Its vocabulary has 18 definitions of the project, and the proof of the theorem `UpperTheory.Lit.neronOggShafarevich` that states it rests on 9,201 declarations.

Let R be a discrete valuation ring with perfect residue field k and fraction field K, let Ω be a separable closure of K and let V be a valuation ring of Ω with V ∩ K = R, which defines an inertia group I in Aut(Ω/K). Let A be an abelian variety over K, given as a commutative group object over Spec K that is smooth, proper and geometrically connected. Then four conditions are equivalent, namely that A has good reduction (A is isomorphic as a group object to the generic fibre of an abelian scheme over R), that I fixes every point of A[m](Ω) for every natural number m that is nonzero in k, that I fixes every point of A[m](Ω) for infinitely many such m, and that I acts trivially on the Tate module T_l A for some prime l that is nonzero in k.

```
A/K abelian ⟹ (good reduction over R) ⇔ (∀ m with p ∤ m, I acts trivially on A[m](K^s)) ⇔ (infinitely many such m) ⇔ (∃ prime l ≠ p, I acts trivially on T_l A)
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let K be a field with a discrete valuation v, residue field k of characteristic p ≥ 0 and inertia group I in Gal(K^s/K) attached to an extension of v. For an abelian variety A over K, good reduction at v, unramifiedness of A[m] for all m prime to p, unramifiedness of A[m] for infinitely many m prime to p, and unramifiedness of T_l A for some prime l ≠ p are equivalent. A standard reference is J.-P. Serre and J. Tate, Good reduction of abelian varieties, Annals of Mathematics 88, 1968, Theorem 1.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement assumes the residue field of R to be perfect, while Serre and Tate allow an arbitrary residue field.
- The inertia group is the inertia subgroup of a valuation subring V of the separable closure Ω with V ∩ K = R, which corresponds to the usual choice of an extension of the valuation.
- The Tate module is the group of compatible sequences of l-power torsion Ω-points with its ℤ_l-module structure, and torsion points are Ω-valued points of A with the group law of the group object.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The four conditions, the inertia group and the notion of good reduction match Serre–Tate's Theorem 1 term by term, and the only change is the added perfectness of the residue field.

### 65, `CasselmanWallach`

The proposition is `GlobalTheory.Published.CasselmanWallach`. Its vocabulary has 19 definitions of the project, and the proof of the theorem `PositivityTheory.CWB.casselmanWallach` that states it rests on 1,832 declarations.

Let σ be an irreducible strongly continuous unitary representation of G = U(J) ≅ U(p,q) on a Hilbert space H, with K = U(p) × U(q). Let E be a complete Hausdorff topological vector space whose topology comes from a sequence of seminorms p_i, with a strongly continuous representation π of G in which every vector is differentiable along every one-parameter subgroup exp(tX) with derivative given by a continuous operator dπ(X), and which has moderate growth p_i(π(g)v) ≤ (1 + Σ|g_ab|²)^N q(v) for some continuous seminorm q and some N. Let T_0 be a linear map from H to E that intertwines the actions of K and of the Lie algebra on K-finite vectors. Then there is a linear map T that agrees with T_0 on K-finite vectors, intertwines σ and π on smooth vectors and is continuous for the Sobolev seminorms of H^∞, any other such map agrees with T on H^∞, the image T(H^∞) is closed in E, and if T_0 is nonzero on some K-finite vector then every Sobolev seminorm of w is bounded by a continuous seminorm of T(w), so T embeds H^∞ topologically into E.

```
∀ T_0 ∈ Hom_{(g,K)}(H_K, E) ∃ T ∈ Hom_G(H^∞, E) continuous with T|_{H_K} = T_0, unique on H^∞, T(H^∞) closed in E, and T a topological embedding if T_0 ≠ 0
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a real reductive group with maximal compact subgroup K. The functor V ↦ V_K from admissible, finitely generated smooth Fréchet representations of moderate growth to Harish-Chandra modules is an equivalence of categories, so every (g,K)-homomorphism V_K → W_K between such representations extends uniquely to a continuous G-homomorphism V → W, and this extension has closed image. Standard references are N. R. Wallach, Real Reductive Groups II, 1992, Chapter 11, and J. Bernstein and B. Krötz, Smooth Fréchet globalizations of Harish-Chandra modules, Israel Journal of Mathematics 199, 2014.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The group is U(p,q), realised as U(J) for a diagonal sign matrix J, while the published theorem covers real reductive groups.
- The source representation is the space of smooth vectors of an irreducible unitary Hilbert space representation, while the published theorem allows any admissible finitely generated smooth Fréchet representation of moderate growth.
- The target E is any complete Hausdorff space whose topology comes from a sequence of seminorms and which carries a representation of moderate growth, and it is not assumed admissible or finitely generated, which reduces to the published case through the closure of T₀(H_K) in E.
- Smoothness of E is encoded by asking that every vector be differentiable at t = 0 along every one-parameter subgroup with continuous derived operators dπ(X), and moderate growth uses the weight (1 + Σ|g_ab|²)^N.
- Smooth vectors of H are defined through finite products of one-parameter subgroups, and continuity of T on them through finite sums of norms of iterated derivatives.
- The conclusion adds that T embeds the smooth vectors topologically into E when T₀ is nonzero on some K-finite vector, which in the published setting follows from the closed range and the open mapping theorem.
- The equivalence of categories form of the published theorem is not stated.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean conclusion follows from the Casselman–Wallach theorem applied to the closure of the image, but the target class is wider than in the published statement, so the match relies on that standard reduction.

### 66, `DualAbelianScheme`

The proposition is `GlobalTheory.Published.DualAbelianScheme`. Its vocabulary has 19 definitions of the project, and the proof of the theorem `GlobalTheory.dualAbelianScheme` that states it rests on 7,912 declarations.

For every scheme S and every abelian scheme A over S, meaning a commutative group object over S that is smooth, proper and geometrically connected, there are an abelian scheme B over S and a line bundle P on A ×_S B, given by Čech transition data, with four properties. If A is smooth of relative dimension g over S then so is B. P is additive in the A-variable, meaning (a·a′, t)^*P ≅ (a, t)^*P ⊗ (a′, t)^*P for all points a, a′ of A and t of B with values in any S-scheme, P is trivial on A × {0}, and for every S-scheme T and every line bundle M on A ×_S T that is additive in the A-variable there is a unique S-morphism x from T to B with M ≅ (1 × x)^*P. The same three properties hold with A and B exchanged and P replaced by its pullback along the swap B ×_S A → A ×_S B.

```
∀ S, ∀ A/S abelian ∃ B/S abelian and P ∈ Pic(A ×_S B) with reldim B = reldim A, (B, P) representing T ↦ {M ∈ Pic(A ×_S T) additive in A}/≅, and (A, swap^*P) representing the same functor for B
```

The theorem that the name points to, as the first reader states it from its own knowledge. For an abelian scheme A over a scheme S, the functor of line bundles on A ×_S T that are rigidified along the zero section and lie in Pic^0 on the fibres is represented by an abelian scheme A^t over S with a Poincaré bundle, A^t has the same relative dimension as A, and the swapped Poincaré bundle identifies A with the dual of A^t. A standard reference is G. Faltings and C.-L. Chai, Degeneration of Abelian Varieties, 1990, Chapter I, Section 1, building on D. Mumford, Geometric Invariant Theory, Chapter 6, for projective abelian schemes.

The first reader takes the proposition for the same statement and the second reader for a stronger statement. The check takes it for undecided.

The check confirmed these differences from the Lean text.

- The Lean statement asserts that the dual exists as an abelian scheme over every base scheme S without a projectivity or normality hypothesis, while the classical construction gives a projective scheme for projective A and over a general base starts from an algebraic space, with the scheme property resting on results attributed to Raynaud.
- The represented functor consists of isomorphism classes of line bundles on A ×_S T that are additive in the A-variable, in place of rigidified line bundles with fibres in Pic⁰, and the two agree for abelian schemes by the theorem of the square and the rigidity lemma.
- Line bundles are encoded as Čech cocycles on chosen open covers, and isomorphisms as generators of the quotient bundle.
- Biduality, in the form that the swapped Poincaré bundle makes A the dual of B, and the equality of relative dimensions are part of the same statement.

The check gives this reason for its judgement. The Lean text agrees with the standard statement term by term, so the relation is same if the published existence theorem gives an abelian scheme over every base and stronger if it gives only an algebraic space outside the projective and normal cases, and I cannot settle that scope from memory.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The universal property matches the usual one once additivity is translated into rigidified Pic^0 by the theorem of the square, but I am less sure how far the published scheme representability over an arbitrary base reaches.

### 67, `KFiniteVectorsUnitary`

The proposition is `GlobalTheory.Published.KFiniteVectorsUnitary`. Its vocabulary has 19 definitions of the project, and the proof of the theorem `GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ` that states it rests on 964 declarations.

For every n, every sign vector ε, which fixes G = U(J) ≅ U(p,q) and K = U(p) × U(q), and every irreducible strongly continuous unitary representation σ of G on a nonzero Hilbert space H, five claims hold. Every K-isotypic component, defined as the sum of the images of all K-equivariant linear maps from an irreducible finite-dimensional K-stable subspace S of H into H, is finite-dimensional. For every K-finite vector v the orbit map g ↦ σ(g)v is real analytic on G, in the sense that near each point it is the restriction of a real-analytic function on the space of complex n×n matrices. The K-finite vectors form a dense subspace H_K that is stable under the derived action of every X with XᴴJ + JX = 0, and the only subspaces of H_K stable under this derived action are 0 and H_K.

```
σ irreducible unitary of U(p,q) ⟹ dim H(τ) < ∞ for all τ ∈ K̂, g ↦ σ(g)v analytic for v ∈ H_K, cl(H_K) = H, dσ(g)H_K ⊆ H_K, and H_K irreducible as a g-module
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be a linear connected reductive Lie group with maximal compact subgroup K and let π be an irreducible unitary representation of G on H. Then π is admissible, every K-finite vector is analytic, the K-finite vectors form a dense g-stable subspace H_K, and H_K is an irreducible (g,K)-module. A standard reference is A. W. Knapp, Representation Theory of Semisimple Groups, An Overview Based on Examples, 1986, Chapter VIII, going back to Harish-Chandra, Representations of a semisimple Lie group on a Banach space I, Transactions of the American Mathematical Society 75, 1953.

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The group is U(p,q), realised as U(J) for a diagonal sign matrix J, while the published theorem covers linear connected reductive groups.
- Admissibility is stated as finite dimensionality of the algebraic sum of the images of all K-equivariant maps from an irreducible K-stable subspace into H, without Harish-Chandra's bound of the multiplicity of a K-type by its dimension.
- Irreducibility of the K-finite vectors is stated for the Lie algebra action alone, which is equivalent to irreducibility as a (g,K)-module because K = U(p) × U(q) is connected.
- Analyticity is expressed through local real-analytic extensions of the orbit map to open sets of the ambient matrix space.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Each of the five claims is a standard consequence of Harish-Chandra's theory for linear connected reductive groups, and U(p,q) is such a group.

### 68, `UnitaryIrreducibleAdmissible`

The proposition is `GlobalTheory.Published.UnitaryIrreducibleAdmissible`. Its vocabulary has 19 definitions of the project, and the proof of the theorem `CompanionTheory.Rg.Fl.B.unitaryIrreducibleAdmissible` that states it rests on 1,354 declarations.

Take number fields F and E with E an F-algebra and an F-algebra endomorphism σ of E such that F is totally real, E is totally complex, E has degree 2 over F and τ(σ(x)) is the complex conjugate of τ(x) for every embedding τ of E into ℂ, so that σ is the complex conjugation of the CM extension E/F. Take any n, any n×n matrix J over E with σ(J_ji) = J_ij for all i and j and det J ≠ 0, and any finite place v of F. The group G_v consists of the invertible n×n matrices g over F_v ⊗_F E with g* J g = J, where g* is the transpose of g with σ applied to the E factor of each entry, and it carries the subspace topology of GL_n over the finite F_v-algebra F_v ⊗_F E, so G_v is the group of F_v-points of the unitary group of J. For every complex Hilbert space H and every group homomorphism π from G_v to the bounded operators on H that preserves norms, is strongly continuous and is topologically irreducible (H ≠ 0 and every closed π-invariant subspace is 0 or H), and for every open compact subgroup K of G_v, the space of vectors of H fixed by every π(k) with k in K is finite-dimensional.

```
∀ CM extension E/F with conjugation σ, ∀ n, ∀ J ∈ M_n(E) with σ(J)ᵀ = J and det J ≠ 0, ∀ finite place v of F, ∀ irreducible unitary representation (π, H) of G_v = { g ∈ GL_n(F_v ⊗_F E) | σ(g)ᵀ J g = J }, ∀ compact open subgroup K ≤ G_v, dim_ℂ H^K < ∞
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let G be the group of rational points of a connected reductive group over a non-archimedean local field. Bernstein proved that for every compact open subgroup K of G there is a constant c(K) with dim π^K ≤ c(K) for every irreducible smooth representation π of G, and as a consequence every irreducible unitary representation of G on a Hilbert space is admissible, which means that its space of K-fixed vectors is finite-dimensional for every compact open subgroup K. I. N. Bernstein, All reductive p-adic groups are tame, Functional Analysis and Its Applications 8 (1974).

The first reader takes the proposition for a special case and the second reader for a special case. The check takes it for a special case.

The check confirmed these differences from the Lean text.

- The Lean statement covers only the groups GLoc σ J v, which are the unitary groups of a nondegenerate Hermitian matrix J for a CM extension E/F taken at a finite place v of the totally real number field F, and they are isomorphic to GL_n(F_v) when v splits in E, whereas Bernstein's theorem covers every connected reductive group over a p-adic field.
- The local fields in the Lean statement are the completions v.adicCompletion F of a number field, so they all have characteristic zero.
- Bernstein's theorem gives a bound c(K) on dim π^K that depends only on K and holds for every irreducible representation, while the Lean conclusion FiniteDimensional ℂ (fixed (toRep π) K) claims only that the space is finite-dimensional for each single π.
- The Lean conclusion states admissibility as finite dimensionality of the K-fixed vectors in the Hilbert space H itself, and this agrees with admissibility of the smooth part because every vector fixed by an open subgroup is smooth.
- The Lean statement asks H only to be a complete inner product space and does not assume that it is separable, which changes nothing because an irreducible unitary representation of a second-countable locally compact group lives on a separable space.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. The definitions in the dossier reproduce the standard unitary group with its natural topology, the standard notion of an irreducible unitary representation and the standard space of K-fixed vectors, so the Lean text is the admissibility theorem restricted to these groups.

### 69, `DiscreteSeriesUpqExists`

The proposition is `GlobalTheory.Published.DiscreteSeriesUpqExists`. Its vocabulary has 20 definitions of the project, and the proof of the theorem `CompanionTheory.RgDs.B.discreteSeriesUpqExists` that states it rests on 5,265 declarations.

Take any N, any sign pattern ε in {true, false}^N, and let J_ε be the diagonal matrix with entry 1 where ε is true and −1 where ε is false, so that G = { g ∈ M_N(ℂ) | gᴴ J_ε g = J_ε } is a copy of U(p, q) and K, the unitary matrices that commute with J_ε, is its maximal compact subgroup U(p) × U(q). Take any real vector λ that is strictly decreasing, which makes it dominant and regular for the positive roots e_a − e_b with a < b, and such that every λ_a − (N − 1)/2 is an integer. Then there exist a nonzero complex Hilbert space H and a map σ from N×N complex matrices to bounded operators on H whose restriction to G is a strongly continuous unitary representation that is topologically irreducible, and every matrix coefficient g ↦ ⟨w, σ(g)v⟩ is square integrable for a Haar measure on G. Let ρ_c and ρ_n be the half sums of the roots e_a − e_b with a < b for which ε_a = ε_b and ε_a ≠ ε_b respectively, and call a K-type of highest weight μ any irreducible finite-dimensional K-invariant subspace that contains a nonzero vector on which the diagonal torus acts by the character μ and whose torus weights all lie below μ by nonnegative integer combinations of the compact positive roots. The conclusion further asserts that H has a K-type of highest weight Λ = λ + ρ_n − ρ_c and that every K-type of H with highest weight μ satisfies ‖Λ + 2ρ_c‖² ≤ ‖μ + 2ρ_c‖² for the Euclidean norm on ℝ^N.

```
∀ N, ∀ ε ∈ {±1}^N, ∀ λ ∈ ℝ^N with λ_1 > … > λ_N and λ_a − (N−1)/2 ∈ ℤ, ∃ irreducible unitary (π, H) of G = U(J_ε) with ⟨w, π(·)v⟩ ∈ L²(G) for all v, w, with a K-type of highest weight Λ = λ + ρ_n − ρ_c, and with ‖Λ + 2ρ_c‖² ≤ ‖μ + 2ρ_c‖² for every K-type μ of π
```

The theorem that the name points to, as the first reader states it from its own knowledge. Harish-Chandra proved that a connected real reductive group G with compact center and maximal compact subgroup K has discrete series exactly when it has a compact Cartan subgroup T, and that for every regular λ with λ + ρ integral there is a discrete series representation π_λ with infinitesimal character λ and an explicit character on T, every discrete series arises in this way, and π_λ and π_λ' are equivalent exactly when λ' lies in W_K λ. Schmid and Hecht and Schmid showed that the K-type of highest weight Λ = λ + ρ_n − ρ_c occurs in π_λ with multiplicity one and that every K-type of π_λ has highest weight Λ plus a sum of positive noncompact roots, so Λ minimizes ‖μ + 2ρ_c‖ and is the lowest K-type in Vogan's sense. A. W. Knapp, Representation Theory of Semisimple Groups. An Overview Based on Examples, 1986.

The first reader takes the proposition for a weaker statement and the second reader for a weaker statement. The check takes it for a weaker statement.

The check confirmed these differences from the Lean text.

- The Lean statement treats only the groups U(p, q), written as the sets of matrices g with gᴴ * Jm ε * g = Jm ε for a diagonal sign matrix Jm ε, whereas Harish-Chandra's theorem covers every real reductive group of Harish-Chandra class that has a compact Cartan subgroup.
- The Lean conclusion links the representation to λ only through the K-type of highest weight lam + rhoN ε − rhoC ε, and it says nothing about the infinitesimal character λ or about Harish-Chandra's character formula on the compact Cartan subgroup.
- The Lean statement omits the parts of Harish-Chandra's classification which say that the representations π_λ exhaust the discrete series and that π_λ and π_λ' are equivalent exactly when λ' lies in W_K λ.
- The Lean conclusion claims only that a K-type of highest weight Λ = λ + ρ_n − ρ_c exists, while the published result says that this K-type occurs with multiplicity one.
- The Lean conclusion claims only that Λ attains the minimum of nsq (μ + 2 • rhoC ε) over the K-types, while the published results say that Λ is the unique lowest K-type and that every K-type has highest weight Λ plus a nonnegative integer sum of positive noncompact roots.
- The clause about the lowest K-type goes beyond Harish-Chandra's existence theorem and rests on the later work of Schmid, of Hecht and Schmid, and of Vogan.
- The Lean statement requires every matrix coefficient coefOn σ v w to lie in L² for the Haar measure muG ε, whereas the usual definition asks for one nonzero square-integrable coefficient, and the two conditions agree for irreducible unitary representations.
- The Lean statement takes only strictly decreasing λ, and this loses nothing because ε ranges over all sign patterns, so conjugation by a permutation matrix reaches every Weyl chamber.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is medium. The Lean statement follows from the published theorems for U(p, q) and claims less than they do, but the name points to an existence theorem while the conclusion also contains lowest K-type information from later work, so the choice between weaker and special case depends on which published statement is taken as the reference.

### 70, `FormalAlgebraisation`

The proposition is `GlobalTheory.Published.FormalAlgebraisation`. Its vocabulary has 20 definitions of the project, and the proof of the theorem `PositivityTheory.FormalThickening.formalAlgebraisation` that states it rests on 4,382 declarations.

The proposition is the conjunction of two statements about a noetherian ring R that is complete and separated for the I-adic topology of an ideal I. The first says that if X is proper over R and Z is separated, locally of finite type and quasi-compact over R, then every family of R-morphisms f_e from the thickenings X_e = X ×_R R/I^{e+1} to Z that is compatible with the inclusions X_e → X_{e+1} comes from a unique R-morphism g from X to Z. The second says that if Y_e are proper R/I^{e+1}-schemes with Y_e = Y_{e+1} ×_{R/I^{e+2}} R/I^{e+1} through maps β_e, and N_e are line bundles on Y_e with N_e ≅ β_e^*N_{e+1} and N_0 relatively ample over R/I, then there are a proper R-scheme X with a relatively ample line bundle M and compatible identifications Y_e ≅ X ×_R R/I^{e+1} under which N_e is isomorphic to the pullback of M for every e.

```
Hom_R(X, Z) = lim_e Hom_R(X ×_R R/I^{e+1}, Z) for X proper and Z separated of finite type, and every proper adic system (Y_e, N_e) with N_0 ample equals (X ×_R R/I^{e+1}, M|) for some proper X over R with M ample
```

The theorem that the name points to, as the first reader states it from its own knowledge. Let A be a noetherian ring complete for the I-adic topology and Y = Spec A. If X is proper and Z is separated of finite type over Y, then Hom_Y(X, Z) → Hom(X̂, Ẑ) is bijective, and if X̂ is a proper formal scheme over the completion of Y with an invertible sheaf L̂ whose reduction to X_0 is ample, then there are a projective Y-scheme X and an ample invertible sheaf L whose completions are X̂ and L̂. A standard reference is A. Grothendieck, Éléments de géométrie algébrique III, première partie, Publications Mathématiques de l'IHÉS 11, 1961, Theorems 5.4.1 and 5.4.5.

The first reader takes the proposition for the same statement and the second reader for the same statement. The check takes it for the same statement.

The check confirmed these differences from the Lean text.

- Formal schemes and their line bundles are written as inverse systems of thickenings and of line bundles with level-wise isomorphisms that are not chosen compatibly, which is harmless because any choice of these isomorphisms gives an invertible sheaf on the formal scheme.
- The second part concludes that X is proper with a relatively ample line bundle in place of projective, which is equivalent over a noetherian affine base.
- Relative ampleness is defined by asking that over every affine open of the base some positive power has finitely many sections whose nonvanishing loci are affine, cover the space and have coordinate rings generated over the base by the ratios of the sections, which is relative very ampleness of a power and matches the usual notion for proper morphisms.
- The statement covers EGA III 5.4.1 and 5.4.5 and leaves out the coherent-sheaf form EGA III 5.1.4 from which they are derived.

The check found no emptiness.

The check found no error in the first reader's account of the Lean text.

The first reader's confidence is high. Both parts restate EGA III 5.4.1 and 5.4.5 for an I-adically complete noetherian ring in the language of adic systems, and the encodings of line bundles and of ampleness match the usual notions.
