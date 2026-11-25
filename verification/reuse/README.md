# What the proof holds that can be used elsewhere

The source holds theorems whose statements can be read without the rest of the proof. Of its
611,644 theorems with a public statement, 79,265 have a statement written with constants of
Mathlib, the other packages and Lean alone. Among these are statements that this document reads
as the Kronecker-Weber theorem, Stein factorisation and Zariski's connectedness theorem. The
source also labels 361 propositions as results from the literature. The five theorems of
`Main.lean` reach 292 of the 361, and for 206 of those 292 the source holds a theorem with no
hypotheses whose statement is the proposition itself. 70 of those 206 propositions can be read
with at most 20 definitions of the project, six of them with none. Lean compiled a test file
that imports the module of the Kronecker-Weber theorem alone and uses the theorem.

This folder sorts the theorems by what a reader has to know in order to read their statements.
A statement written with library constants alone can be read without learning any definition
of the project. The folder counts such statements and lists them in a file that git ignores. It
checks no proof. The counts come from the compiled files that `lake exe cache get` downloads,
which this folder trusts as they are. `lake comparator` is the tool that checks the proofs
against the statements, and the [README of the repository](../../README.md#checking-the-proof)
records no complete run of it on the current source.

A language model, Claude, wrote this document on 24 November 2026. It read the Lean text of the
statements that the tables below describe in words, and it read no proof. No mathematician has
checked the descriptions.

## Words used here

- The five theorems are the theorems of [`Main.lean`](../../src/Main.lean), which state the
  Riemann hypothesis and its form for Dirichlet L-functions. A constant mentions another when
  its compiled type or value names it, and the five theorems reach a constant when a chain of
  mentions leads from one of them to it. A theorem is used when the five theorems reach it.
  The [README of the declaration graph](../decl-graph/README.md) describes the graph of
  mentions.
- A declaration is a theorem, a definition or another item of the source text. The declaration
  table is `data/declarations.tsv.gz` of [`../decl-graph`](../decl-graph/README.md), which has
  one row for every declaration of the source text.
- The statement of a theorem is its compiled type. A statement is public when other modules can
  see it. The source has 611,644 theorems and lemmas with a public statement, and 594,168 of
  them are used. Another 57,913 theorems of the source are private or have no public statement
  for another reason, and this folder leaves them out.
- A statement is in library terms when it mentions no constant of the project, so that every
  word of it is a definition of Mathlib, of another package or of Lean.
- A proposition is a definition of the project of type `Prop` that stands for a claim. A
  separate theorem can prove it.
- The vocabulary of a statement is the set of definitions of the project that a reader needs in
  order to read it. [`statements.py`](statements.py) finds it by following mentions from the
  statement. A definition, a structure or a constructor is followed into everything that its
  type and its value mention, and a structure leads to its constructor, whose type holds the
  types of the fields. A theorem that a definition mentions is followed into its statement
  only, because a proof does not change what a definition means. The size of the vocabulary is
  the number of definitions with a row in the declaration table that this search meets.
- A theorem rests on the declarations of the project that its statement and its proof reach,
  the theorem itself included. A proof that rests on one declaration uses the libraries alone.
- An area is a part of Mathlib, named by the folder of the module that holds a library
  constant. A statement touches an area when it or its vocabulary mentions a constant of it.

## Statements in library terms

79,265 theorems have a statement in library terms, 13 % of the theorems with a public statement,
and 77,675 of them are used. The check of [`../redundancy`](../redundancy/README.md) had Lean
compare the statements of the theorems whose source text looked alike. Some of the 79,265 were
among them, and counting once the statements that Lean found equal leaves 72,983 of the
79,265.

Most of these theorems rest on few declarations of the project. The table sorts them by the
number of declarations that the proof rests on.

| The proof rests on | Theorems |
|---|---:|
| 1 declaration, the theorem itself | 54,004 |
| 2 to 10 | 21,858 |
| 11 to 100 | 3,191 |
| 101 to 1,000 | 196 |
| 1,001 to 10,000 | 13 |
| more than 10,000 | 3 |

The three at the bottom are `riemannHypothesis`, one of the five theorems, and the theorems
`rhOfAll` and `critAll` of the library `Supplements`, which lie outside `Main.lean`. The three
state the Riemann hypothesis and its form for primitive Dirichlet characters in Mathlib's terms. The 209 theorems of the two rows above them have a statement in
library terms and a proof that draws on 101 to 10,000 declarations of the project. The next
table describes eight of them, whose statements this session read in full, in the order of the
last column. The five theorems use each of the eight.

| Theorem | What its statement says | Rests on |
|---|---|---:|
| `PositivityTheory.KB.PrincipalPrimes.exists_prime` | For a number field L and a bound B, the ring of integers of L has a prime element π such that the ideal generated by π has norm at least B. | 4,930 |
| `PositivityTheory.KB.PrincipalPrimes.exists_principal` | For a number field L and a finite set T of prime ideals of its ring of integers, there is a prime ideal outside T that is principal. | 4,928 |
| `UpperTheory.V.CF.kwHom` | Every finite abelian extension L of ℚ has an embedding into a cyclotomic field ℚ(ζ_N) with N > 0. This is the form of the Kronecker-Weber theorem. | 4,902 |
| `UpperTheory.V.CF.kw` | For a finite abelian extension L of ℚ inside an algebraically closed field Ω of characteristic zero, some primitive N-th root of unity ζ of Ω has L inside ℚ(ζ). | 4,901 |
| `GlobalTheory.T.stein_factorisation_connected_fibres` | A proper morphism g from X to a locally noetherian scheme Y factors as a morphism a from X to Y′ followed by a finite morphism b from Y′ to Y. The morphism a is proper and surjective, it gives a bijection on the sections over every open set of Y′, and each of its fibres is connected. This is the form of Stein factorisation. | 2,002 |
| `GroundTheory.LocalField.Padic.exists_le_adjoin_rootsOfUnity` | A finite abelian extension of ℚ_p inside a field Ω lies in the field generated over ℚ_p by the N-th roots of unity of Ω, for some N > 0. This is the form of the local Kronecker-Weber theorem. | 1,460 |
| `GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr` | Let f be a morphism from a scheme to the spectrum of a discrete valuation ring that is separated, locally of finite type, quasi-compact, universally open and geometrically irreducible in the sense of Mathlib's `GeometricallyIrreducible`. If the special fibre of f is proper, then f is proper. | 910 |
| `GlobalTheory.T.zariski_connectedness_isPreconnected_fibre` | For a proper morphism a from X to a locally noetherian scheme Y that gives a bijection on the sections over every open set of Y, every fibre is connected. This is the form of Zariski's connectedness theorem. | 905 |

Mathlib writes connected as `IsPreconnected` in these statements, which allows the empty set.
The names of the constants of the pinned Mathlib were searched for six strings, which are
Kronecker followed by Weber, Stein followed by factorisation, Zariski followed by connected,
Ferrero, Hasse followed by norm, and Chebotarev. No name matched. Mathlib can still hold one of these results under another name, and a
later Mathlib can hold more.

[`CATALOGUE.md`](CATALOGUE.md) goes through all 212 theorems in library terms whose proofs
rest on more than 100 declarations. They hold 159 different statements, and for each of them
two readers and a check say what it states and which published result it is. By the check 32
are named theorems, 61 are standard facts of textbooks and 66 are technical steps. Besides the
theorems of the table above, the named theorems include the purity of the branch locus of
Zariski and Nagata, Borel's finiteness of class numbers, Chevalley's theorem on units, the
product formula and Hecke's continuation of the L-functions of ideal characters. The readers
named the published results from the model's own knowledge, and no mathematician has checked
the catalogue.

[`MATHLIB.md`](MATHLIB.md) asks how many of the statements in library terms Mathlib already
holds, as one theorem of its own or within one run of a proof-search tactic. A test gave
statements to Lean with Mathlib loaded and the project left out, and let four proof-search
tactics of Lean try each of them. The tactics proved none of the 159 statements of the
catalogue. They proved 8 of the 2,655 statements whose proofs in the source rest on 11 to 100
declarations, all of which the test posed. They proved 93 of a random sample of 1,000 of the
72,983 statements, and each of the 93 has a proof in the source that rests on at most 10
declarations. Each of these counts is a lower bound for what Mathlib holds. A tactic was
stopped at its limit of work before it finished on 23 statements of the catalogue, 348 of the
2,655 and 95 of the sample, and a tactic can miss a theorem that is there. In a control the
tactic that looks for one fitting theorem found 273 of 279 theorems of Mathlib itself. The same
document searches the text of Mathlib's files for the names of the published results and counts
the modules of the project that a Lean file has to load in order to use a statement of the
catalogue.

`statements.py` writes every theorem with a vocabulary of at most 20 definitions, these 79,265
included, to `data/small_vocabulary.tsv.gz`, and `summary.json` holds the 150 theorems in
library terms with the largest proofs.

## Results from the literature for which the source holds a proof

The source labels 361 propositions as results from the literature, as
[`PUBLISHED.md`](../skeleton/PUBLISHED.md) describes. The five theorems reach 292 of them. For
206 of the 292 the source holds a theorem with no hypotheses whose statement is the proposition
itself. The other 86 are proved from further hypotheses or only taken as a hypothesis by other
theorems, by the count of `PUBLISHED.md`.
The table sorts the 206 by the vocabulary of the proposition.

| Vocabulary | Propositions |
|---|---:|
| none, the proposition is in library terms | 6 |
| 1 to 5 definitions | 19 |
| 6 to 20 | 45 |
| 21 to 100 | 104 |
| 101 to 1,000 | 32 |

The scan of [`../redundancy`](../redundancy/README.md) found 12 definitions of the project that
are the proposition `True` on every input. The vocabulary of none of the 206 propositions holds
one of them.

The six propositions in library terms are `ChevalleyUnits`, `HasseNorm`, `HasseNormSt`,
`IdentityComponentOpen`, `SchurOrthogonalitySquareIntegrable` and `FerreroWashington`. The next
table describes seven propositions whose Lean text this session read. The column Vocabulary
gives the number of project definitions that the proposition needs.

| Proposition | What it says | Vocabulary | The proof rests on |
|---|---|---:|---:|
| `FerreroWashington` | Let l be a prime and K a finite abelian extension of ℚ that holds a primitive l-th root of unity, or a primitive fourth root when l = 2. Then there is an r such that for every n the field K′ obtained from K by adjoining the l^n-th roots of unity has a class group whose quotient by its l-th powers has at most l^r elements. So the l-rank of the class group stays bounded in the cyclotomic l-tower over K. | 0 | 5,560 |
| `HasseNorm` | Let L over K be a cyclic extension of number fields and a ≠ 0 an element of K. If at every finite and every infinite place v of K the element a is a norm from the tensor product of the completion K_v with L, then a is the norm of an element of L. | 0 | 410 |
| `ChevalleyUnits` | For a number field E and m, b > 0 there is an a > 0 prime to b such that every unit of the integers of E that is 1 modulo a is an m-th power of a unit. | 0 | 250 |
| `Linnik` | Constants C > 0 and L > 0 exist such that for coprime a ≥ 1 and q ≥ 1 the number `leastPrimeMod a q` is at most C·q^L. The source defines `leastPrimeMod a q` as the infimum of the primes that are congruent to a modulo q. This is the form of Linnik's theorem. | 2 | 511 |
| `StoneVonNeumann` | For a nonarchimedean local field F in which 2 ≠ 0, a nondegenerate alternating form B on a finite-dimensional space and a nontrivial continuous additive character ψ, a representation of the Heisenberg group of B that meets the condition `IsIrrSmoothOf ψ` exists, and any two such representations are equivalent. | 3 | 49 |
| `ChebotarevDegreeOne` | For a finite Galois extension L of a number field F, an element g of its Galois group and a finite set S of primes of F, there is a prime v of F outside S of residue degree one over ℚ and a place above it, given through the conditions `IsPlaceOver` and `Ine` of the project, with an element σ of the group that the code writes `G F Ω`, for an algebraic closure Ω of F, that meets the condition `IsFrob` for that place and restricts to g on L. | 6 | 236 |
| `ResolutionCharZero` | For a reduced scheme X that is separated and of finite type over a field of characteristic zero, there is a morphism s from X′ to X that meets the condition `IsBlowupSeq`, such that X′ is smooth over the field, s is an isomorphism over the smooth locus of X, and a condition `Snc` holds for the preimage of the complement of that locus. | 7 | 7,699 |

A name says what a proposition is meant to be, and the Lean text says what it states.
[`AUDIT.md`](AUDIT.md) compares the two for all 70 propositions with a vocabulary of at most 20
definitions. For each of them a dossier holds the whole Lean text of the proposition and of
its vocabulary, two readers state what the text says and judge its relation to the published
theorem, and a check compares both with the Lean text. By the check 18 of the 70 state the same
as the published theorem, 34 a special case, 14 something weaker, 2 something stronger and 1
something different, and 1 stays undecided. No reading found an empty proposition. Of the seven
propositions of the table above, the check takes `HasseNorm` and `StoneVonNeumann` for the same
statement as the published theorem, `FerreroWashington` and `ChevalleyUnits` for a special
case, and `Linnik`, `ChebotarevDegreeOne` and `ResolutionCharZero` for a weaker statement. The
readers stated the published theorems from the model's own knowledge, and no mathematician has
checked the comparison.

The count of declarations says how much of the project a proof draws on. It does not say how
long the proof is, since one declaration can be a proof of any length.

## Statements with a small vocabulary

The statement of a theorem needs seven definitions of the project at the median. The table
sorts all 611,644 theorems.

| Vocabulary | Theorems |
|---|---:|
| none | 79,831 |
| 1 to 5 definitions | 207,865 |
| 6 to 20 | 124,835 |
| 21 to 100 | 90,160 |
| 101 to 1,000 | 97,422 |
| more than 1,000 | 11,531 |

The 79,831 without a vocabulary are the 79,265 in library terms and 566 whose statement
mentions only constants of the project that have no row in the declaration table, such as an
instance without a name.

412,531 theorems have a vocabulary of at most 20 definitions, and the proofs of 1,344 of them
rest on more than 1,000 declarations. By their names the largest of the 1,344 concern the
reduction of abelian varieties, the dual abelian scheme and Galois cohomology.
`GlobalTheory.T.potentialGoodReduction_of_lieMult_zero` has a vocabulary of 10 definitions and
a proof that rests on 17,047 declarations. `summary.json` holds the 150 with the largest proofs.

23,099 theorems have a statement that is one proposition of the project and nothing else, as
the theorem `PositivityTheory.GreenCharacters.green` has, whose statement is the proposition
`GlobalTheory.GLq.Green`. For 13,880 of them the vocabulary is at most 20.
`UpperTheory.Gal.Int.Geo.CovMain.stdEx_holds` states the proposition `StdEx` with a vocabulary
of 6 definitions, and its proof rests on 38,504 declarations.

## Where zeta and L-functions enter the statements

Mathlib keeps the Riemann zeta function, Dirichlet L-functions, L-series, Euler products and
the Dedekind zeta function in five folders and files, which form the area zeta and L-series
here. The shares of the table are shares of the 594,168 used theorems.

| | Used theorems | Share |
|---|---:|---:|
| The statement or its vocabulary mentions zeta or L-series | 10,342 | 1.7 % |
| The statement itself mentions them | 481 | 0.1 % |
| The statement or its vocabulary mentions Dirichlet or multiplicative characters | 86,087 | 14.5 % |

The count for characters takes in Mathlib's folders for Dirichlet characters, multiplicative
characters, Gauss sums and the Legendre symbol. 3,739 definitions of the project mention zeta
or L-series in their type or value, or in a definition that those lead to. The other 98.3 % of the used theorems have a statement that
mentions zeta and L-series neither in its own text nor in any definition that it needs. The
figure is about statements. A proof can still use a theorem about L-functions.

The outline of [`../skeleton`](../skeleton/README.md) has 40 lines, each a theorem that marks a
large step of the proof. The 40 lines fall into three groups by whether their vocabulary
mentions zeta and L-series and whether it mentions characters. The vocabulary of the line
`galoisLocalGlobalStrong_recParameter` and of the five lines below it mentions neither zeta and
L-series nor characters. The [commentary of the strategy](../strategy/README.md) reads these
lines as the existence of Galois representations and the steps towards it. The three lines from
`automorphic_window_of_inputs` down mention characters and no zeta or L-series. The other 31
lines mention both, 26 of them through a vocabulary of more than 1,000 definitions.

The next table gives, for some areas, the number of used theorems whose statement or vocabulary
touches the area, and its share of the 594,168. A statement can touch several areas.

| Area of Mathlib | Used theorems | Share |
|---|---:|---:|
| number fields | 202,245 | 34 % |
| complex analysis | 198,968 | 33 % |
| measure theory | 132,752 | 22 % |
| p-adic numbers | 113,409 | 19 % |
| representation theory | 111,187 | 19 % |
| category theory | 102,607 | 17 % |
| algebraic geometry | 96,906 | 16 % |
| zeta and L-series | 10,342 | 1.7 % |
| modular forms | 2,357 | 0.4 % |

`summary.json` has the figures of all 34 areas.

## What the author's note says about further uses

The author of the source announced it in a four-page [note](https://alpo.ge/remark.pdf), and
the note names three further uses. This section reports them as the note states them and says
what the source holds. It tests none of them.

- The note says that the method extends to the generalized Riemann hypothesis and that the
  author expects the extended Riemann hypothesis with more time. The note defines neither name.
  In a common usage the first is about Dirichlet L-functions and the second about the Dedekind
  zeta functions of number fields. The five theorems of `Main.lean` are about the zeta function
  and the Dirichlet L-functions, and none of them is about a Dedekind zeta function.
- The note ends with a timeline of 20 entries. Entry 17 speaks of a substantial weakening of
  the Vandiver conjecture, and a footnote to it says that the author believes that the
  vanishing of several K-groups of ℤ follows. A search of the declaration names of the source
  for Vandiver found none. The commentary of
  the strategy matches the entry with the proposition `VWin`, which bounds sums of lengths of
  Galois cohomology groups. The source derives `VWin` from a proposition `Row` on the existence
  of Galois representations, and it holds a theorem with no hypotheses that states `Row`.
- The note says that the author expects much shorter arguments to follow. This folder does not
  test that. The 36,108 declarations that the five theorems do not use, sorted in
  [`../decl-graph`](../decl-graph/README.md), show only how much of the source the five
  theorems leave aside.

## Using one theorem in another Lean file

A Lean file that imports the module of one theorem loads only the modules that this module
imports, and leaves the rest of the project out. By the `import` lines of the source the
module of `kwHom` imports 410 modules of the project, directly or through others, where
`Main.lean` imports 149,283. [`import_cost.py`](import_cost.py) counts the same for every
statement of the catalogue.

```lean
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom

example (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ N : ℕ, 0 < N ∧ Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) :=
  UpperTheory.V.CF.kwHom L

#print axioms UpperTheory.V.CF.kwHom
```

Lean compiled this file without an error in the compiled checkout on 25 November 2026, with the
command `lake env lean`. Its last line printed that `UpperTheory.V.CF.kwHom` depends on the
axioms `propext`, `Classical.choice` and `Quot.sound`. The run took 174 minutes, of which Lean
computed for 3 seconds. The rest was spent loading the compiled files of Mathlib, of the module
of `kwHom` and of the modules that it imports from a disk image on an external drive. The test ran inside a checkout of this
repository. A project of its own that wants the theorem would have to use the Lean and Mathlib
versions that this repository pins and name this repository as a dependency in its lakefile.
That setup was not tested.

The other theorems of the two tables were not compiled in this way. For them `exact_axioms.py`
of [`../decl-graph`](../decl-graph/README.md) searched the compiled files from each of the
eight theorems of the first table alone, from the theorems that prove the seven propositions of
the second table, and from the theorem that proves the proposition `DeligneRibet` of
`AUDIT.md`. Every one of the 16 searches reached the
axioms `propext`, `Classical.choice` and `Quot.sound` and no other axiom, and every name that a
search met has a compiled entry. The search from `kwHom` reached 112,181 constants of the
project and the libraries, and its answer agrees with the answer of Lean.

## Limits

- The folder covers public statements. The 57,913 theorems of the source without one are left
  out.
- A small vocabulary makes it short to check that a statement means what its name says. It
  does not make the check. The commentary of the strategy found two notions in the branch on
  Galois representations that are weaker than their names.
- A statement in library terms can still have a hypothesis that nothing satisfies, and then it
  says nothing. This session read the statements of the two tables above. The readers of
  `AUDIT.md` and `CATALOGUE.md` read the 70 propositions and the 159 statements that those
  documents cover, and nobody read the other statements.
- No proof was read, and the compiled files come from the build cache of the repository.
- An area is the folder of a library constant, which is a coarse label.
- Equal statements are counted once only where the redundancy check compared them.

## Running it

```bash
python3 -I verification/decl-graph/statement_extract.py /path/to/a/compiled/checkout   # about two hours
python3 -I verification/reuse/statements.py                                           # about three minutes
```

`statement_extract.py` needs the same compiled checkout as the exact graph, and
`statements.py` needs the files of `exact_graph.py` and `exact_axioms.py` of
[`../decl-graph`](../decl-graph/README.md).

## Files

| File | Content |
|---|---|
| `statements.py` | computes the vocabularies, the proof sizes and the areas |
| `summary.json` | the figures of this document, the 150 largest proofs of each kind, the 40 lines of the outline and the 361 propositions from the literature |
| `data/small_vocabulary.tsv.gz` | every theorem with a vocabulary of at most 20 definitions, with its proof size and areas |
| `AUDIT.md` | the 70 propositions from the literature with a small vocabulary, each compared with the published theorem |
| `audit.py`, `briefs/`, `audit.json` | the dossiers, the briefs of the readers and the check, and their answers |
| `CATALOGUE.md` | the 159 statements in library terms with large proofs, each with the published result that it is |
| `catalogue.py`, `catalogue.json` | the dossiers of the catalogue and the answers of its readers and its check |
| `MATHLIB.md` | what Lean's search and automation find in Mathlib of the statements in library terms |
| `MathlibHas.lean`, `mathlib_has.py` | the test of `MATHLIB.md` and its runs |
| `mathlib_has.json`, `mathlib_medium.json`, `mathlib_sample.json`, `mathlib_control.json`, `mathlib_names.json` | the answers for the catalogue, the 2,655 statements with proofs of middle size, the sample and the control, and the files of Mathlib that match a name |
| `import_cost.py`, `import_cost.json` | the modules of the project that come along with each statement of the catalogue |

Git ignores `data/`.
