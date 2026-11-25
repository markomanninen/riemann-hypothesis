# What Lean's proof search finds in Mathlib of the statements in library terms

The Lean text in [`src`](../../src) holds a proof that claims the Riemann hypothesis, and this
document calls it the project. 79,265 of its theorems have a statement that is written with
definitions of the library Mathlib, of the packages that Mathlib uses and of Lean alone. A
comparison by Lean found some of these statements equal, which leaves at most 72,983 different
statements, and fewer if the comparison missed a pair. This document asks how many of the
72,983 Mathlib already holds. Mathlib holds a statement here when one of its theorems gives the
statement or when one of
the four proof-search programs of this test derives it from the libraries in one run. A test
gives a lower bound for this number. It gave a statement to Lean with Mathlib loaded and the
project left out, and the four programs tried it within a fixed limit of work. The number
that they prove is a lower bound, since a program can be stopped at its limit and can miss a
theorem that is there.

The test covered three sets of the statements. Two are chosen by the size of the proof in the
project, and the third is a random sample. A declaration is a named theorem, definition or
other item of Lean text. The proof of a theorem rests on every declaration of the project that
the statement and the proof use, directly or through other declarations, the theorem itself
included. A proof that rests on one declaration thus cites the libraries alone. The first set
is the 159 statements of [`CATALOGUE.md`](CATALOGUE.md), whose proofs rest on more than 100
declarations. The second is the 2,655 statements whose proofs rest on 11 to 100 declarations.
The third is a random sample of 1,000 of the 72,983. The sample shares 4 statements with the
first set and 42 with the second, so the three sets hold 3,768 different statements.

- The four programs proved none of the 159 statements of the catalogue.
- They proved 8 of the 2,655 statements of the second set, which is 0.3 %.
- They proved 93 of the sample of 1,000, which is 9.3 %. Each of the 93 has a proof in the
  project that rests on at most 10 declarations. The 95 % score interval of Wilson for this
  share reaches from 7.7 % to 11.3 %, which is 5,500 to 8,300 of the 72,983 statements after
  rounding outward to the hundred. The four programs thus close at least 5,500 of the 72,983
  statements with 95 % confidence, and the test sets no upper bound on what Mathlib holds.
- For 23 of the 159 statements and 95 of the 1,000 no program found a proof and at least one
  program was stopped at its limit of work, also in a second run with five times the limit. For
  348 of the 2,655 the same holds after one run with the first limit. For these statements the
  search is unfinished.
- In a control the program `exact?`, which looks for one theorem that proves a goal, proved 273
  of 279 theorems of Mathlib itself, which is 97.8 %. The control poses a theorem word for word
  as Mathlib states it, and it measures neither a statement that Mathlib states with other
  definitions nor the other three programs.

Mathlib can also prove the same mathematics in another form, which this sense of holding leaves
out, and the product formula in the section on the text of Mathlib's files is such a case. A statement that Mathlib
lacks can still be a published result, since the test compares the project with one library and
not with the literature.
`CATALOGUE.md` sorts its 159 statements into 32 named theorems, 61 standard facts of textbooks
and 66 technical steps, by a check that a language model made. By that check 29 of the 32 named
theorems correspond to a published result, and several of them can correspond to one result.
The check calls 13 of the 29 the same as the result and 16 a special case or a weaker form of
it. The other three are forms of the Riemann hypothesis, which the project claims to prove.

A Lean file that wants a statement that Mathlib lacks, with the proof of the project, imports
the module of the theorem, and Lean loads other modules of the project with it. For the 156
statements of the catalogue other than the three forms of the Riemann hypothesis these are
between 2 and 19,922 of the 149,397 modules of the project, and for half of the 156 they are at
most 120.

A language model, Claude, wrote the test and this document on 25 November 2026. Of Mathlib it
read the files that the search in the section on the text of Mathlib's files matched. No
mathematician has checked the document.

## Words used here

- The project is the Lean text in `src`. A declaration is a named theorem, definition or other
  item of Lean text, in the project or in the libraries, and a constant is the name of a
  declaration. The proof of a theorem rests on the declarations of the project that the
  statement and the proof use, directly or through other declarations, the theorem itself
  included.
- `Main.lean` is the file of the project that holds its five final theorems, which state the
  Riemann hypothesis and its form for Dirichlet L-functions. One of the five,
  `riemannHypothesis`, has a statement in library terms and is entry 2 of the catalogue. Entries
  1 and 3, `critAll` and `rhOfAll`, are two other forms of the Riemann hypothesis and lie in
  other files of the project.
- Mathlib is the library of mathematics for Lean that the project builds on. The project pins
  one revision of it, the commit `fc4f59e577` of 16 November 2026, and every result of this
  document is about that revision. The libraries are Mathlib, the packages that Mathlib uses
  and the core of Lean. Each module of Mathlib is one file.
- The statement of a theorem is its compiled type. A statement is in library terms when it
  mentions no constant of the project, so that every word of it is a definition of the
  libraries. [`README.md`](README.md) counts 79,265 theorems with such a statement. A
  comparison by Lean, which [`../redundancy`](../redundancy/README.md) describes, found some of
  them equal, and counting those once leaves 72,983 statements. Where theorems with an equal
  statement have proofs that rest on different numbers of declarations, this document sorts
  the statement by the largest of those numbers.
- A tactic is a program of Lean that tries to prove a goal. The test uses four tactics.
  - `exact?` searches the libraries for one theorem whose conclusion fits the goal. It can
    read an equivalence in one direction and turn an equation around. It then tries to meet
    the hypotheses of that theorem with the hypotheses of the goal.
  - `simp_all` rewrites the goal and its hypotheses with the theorems that the libraries mark
    for simplification.
  - `aesop` searches for a proof by applying the rules that the libraries register for it.
  - `grind` reasons from the equalities of the goal and from the theorems that the libraries
    mark for it.
- Mathlib holds a statement when one of its theorems gives the statement or when one run of
  one of the four tactics derives it from the libraries. The test gives a lower bound in this sense and asks for
  no wider one. In a wider sense every statement that the project proves without an axiom of
  its own follows from the libraries.
- A tactic closes a statement when it proves it. It gives up when it ends without a proof
  before its limit of work.
- A heartbeat is the unit in which Lean counts the work of a tactic. A tactic that uses more
  heartbeats than its limit is stopped.
- The catalogue is `CATALOGUE.md`. It lists the 159 statements in library terms whose proofs
  rest on more than 100 declarations. Two runs of a language model, called the readers, and a third run, called the check,
  say for each statement which published result or textbook fact it matches or that it is a
  step of a larger proof. The check sorts the statements into three kinds, 32 named theorems,
  61 standard facts of textbooks and 66 technical steps.
- An interval given with a share is the 95 % score interval of Wilson for that share.

## The test

The test needs a Lean session that holds the libraries and no constant of the project. A
separate folder for Lake, the build tool of Lean, provides it. The folder requires the pinned
revision of Mathlib and nothing else. For one statement the script
[`MathlibHas.lean`](MathlibHas.lean) does four things in that session.

1. It reads the statement from the compiled file of the module that holds the theorem. The
   file is read as data, and the module is not imported.
2. It tests that every constant of the statement exists in the session and that Lean accepts
   the statement as a proposition.
3. It makes the statement a goal and runs each of the four tactics on it, each with a limit of
   400,000 heartbeats, which is twice the limit that Lean sets by default.
4. It writes down for each tactic whether it closed the statement, gave up or was stopped at
   the limit.

For the 159 statements of the catalogue and the 1,000 of the sample, a tactic that was stopped
at the limit ran once more with 2,000,000 heartbeats. The 2,655 statements with proofs that
rest on 11 to 100 declarations and the control ran once, with 400,000. A proof that a tactic
finds in this session uses the libraries alone, since the session holds nothing else.

Lean accepted every statement that the test posed in step 2, the 159 of the catalogue, the
2,655 with proofs that rest on 11 to 100 declarations and the 1,000 of the sample. The session
holds no definition of the project, so by the test of Lean itself these statements need none.

## The control

The control measures how often `exact?` finds a theorem that Mathlib does hold. The script
`mathlib_has.py` drew 300 of the 8,712 modules of Mathlib at random, and `MathlibHas.lean` took
at most one theorem from each. It took the propositions of the module that other modules can
see and left out the lemmas that Lean makes by itself, such as the equation lemmas of a
definition. Of these it took the one whose name has the smallest hash, so the rule ignores what
a theorem says. 21 of the 300 modules hold no such theorem, which leaves 279 theorems.

`exact?` closed 273 of the 279, which is 97.8 %, with an interval from 95.4 % to 99.0 %. In
268 of the 273 the proof that it found is the theorem itself, and in the other five it is
another theorem of Mathlib that gives the same statement. It gave up on three theorems and was
stopped at the limit on three.

The control poses each theorem exactly as Mathlib states it. It therefore measures the search
on statements that Mathlib states word for word, and a statement that Mathlib states with other
definitions is outside what the control measures.

## The 159 statements of the catalogue

No tactic closed any of the 159 statements. The table gives the answers after the second run
with 2,000,000 heartbeats.

| Tactic | Closed | Gave up | Stopped at the limit |
|---|---:|---:|---:|
| `exact?` | 0 | 145 | 14 |
| `simp_all` | 0 | 157 | 2 |
| `aesop` | 0 | 147 | 12 |
| `grind` | 0 | 159 | 0 |

23 statements have at least one tactic that was stopped at the limit of 2,000,000 heartbeats,
and for them the search is unfinished.

The control says how much weight the zero of `exact?` in the column Closed carries. `exact?`
found 273 of the 279 theorems of the control and none of the 159 statements. A statement of the
catalogue that Mathlib stated word for word would most likely have been found, and the 14
statements on which `exact?` was stopped stay open. No control measures the zeros of the other
three tactics.

## The 2,655 statements with proofs of middle size

`README.md` counts 3,191 theorems in library terms whose proofs rest on 11 to 100
declarations. They state 2,656 different statements. One of the 2,656 is a statement of the
catalogue, since a theorem with the same statement has a proof that rests on more than 100
declarations. The test posed the other 2,655.

The tactics closed 8 of the 2,655 statements, which is 0.3 %. `exact?` closed seven of them,
and `simp_all` and `aesop` each closed the eighth. The table gives the answers of the one run
with 400,000 heartbeats.

| Tactic | Closed | Gave up | Stopped at the limit |
|---|---:|---:|---:|
| `exact?` | 7 | 2,406 | 242 |
| `simp_all` | 1 | 2,627 | 27 |
| `aesop` | 1 | 2,514 | 140 |
| `grind` | 0 | 2,652 | 3 |

All four tactics gave up on 2,299 statements. 348 statements have at least one tactic that was
stopped at the limit, and for them the search is unfinished.

Each of the eight closed statements is a general fact that Mathlib proves with one theorem or
by simplification, and the project proves it again with lemmas of its own. The next table gives
the eight with what the tactic found in Mathlib.

| Theorem of the project | What it says | The proof in the project rests on | What the tactic found in Mathlib |
|---|---|---:|---|
| `GlobalTheory.Wick.pderiv_pderiv_comm` | Two partial derivatives of a polynomial in several variables can be taken in either order | 13 | `MvPolynomial.pderiv_comm` |
| `Formalism.L2.FormalSeriesBounds.SelfConjCharts.gen_cc_psubst` | When a power series f in one variable and a power series a in several variables both have the constant term 0, the series f(a) has the constant term 0 | 12 | `PowerSeries.constantCoeff_subst_eq_zero` |
| `Formalism.L2.Th1.B.exp_subst_log` | The exponential series with the series of log(1 + X) put in place of its variable is 1 + X | 19 | `PowerSeries.subst_exp_log` |
| `Formalism.L2.Th1.B.log_subst_exp` | The series of log(1 + X) with exp(X) − 1 put in place of its variable is X | 20 | `PowerSeries.subst_log_exp_sub_one` |
| `FunctorialResolution.EmbeddedResolution.mem_support_iSup_le_nat` | A point of a scheme that lies in the support of each of the ideal sheaves G₀, …, Gₙ lies in the support of their supremum | 15 | A proof by `simp_all` and by `aesop`, both with `AlgebraicGeometry.Scheme.IdealSheafData.support_iSup` |
| `GroundTheory.ProfCoh.finite_addMonoidHom_zmod` | A finite abelian group has finitely many homomorphisms to ℤ/n, for n ≥ 1 | 20 | `DFunLike.finite` |
| `GroundTheory.LocalField.locallyCompactSpace_units` | The group of units of a nonarchimedean local field is locally compact | 26 | `Units.instLocallyCompactSpaceOfT1SpaceOfContinuousMul` |
| `GroundTheory.LocalField.measurable_units_val` | The inclusion of the units of a nonarchimedean local field into the field is a measurable map | 36 | `Measurable.of_comap_le` |

The catalogue and this section together cover every statement in library terms that has a proof
in the project resting on more than 10 declarations, 159 and 2,655, which is 2,814 statements.
The tactics closed 8 of the 2,814, all of them among the statements whose proofs rest on at
most 36 declarations.

## The sample

The sample is 1,000 statements drawn at random, with a fixed seed, from the 72,983 statements
in library terms. The tactics closed 93 of them, and `exact?` closed 53. The table sorts the
sample by the number of declarations that the proof in the project rests on.

| The proof in the project rests on | Statements | Closed by `exact?` | Closed by some tactic |
|---|---:|---:|---:|
| 1 declaration, the theorem itself | 693 | 50 | 89 |
| 2 to 10 | 261 | 3 | 4 |
| 11 to 100 | 42 | 0 | 0 |
| more than 100 | 4 | 0 | 0 |
| All | 1,000 | 53 | 93 |

A proof that rests on one declaration is written in the project and cites the libraries alone.
89 of the 93 closed statements have such a proof. The four tactics closed none of the other 604
statements with such a proof within their limits of heartbeats. For these the project has a
proof from the libraries that the test did not find in Mathlib.

For each of the 53 statements that `exact?` closed, the proof that it found is one line that
applies a theorem of the libraries. In 37 of the 53 the line is one theorem with the variables
and hypotheses of the statement, so the statement is that theorem or a case of it under a
second name. `GlobalTheory.WpFam.TauVal.two_pi_I_ne_zero` is `Complex.two_pi_I_ne_zero`,
`Formalism.L2.Th1.B.psubst_X` is `PowerSeries.X_subst`, and
`GlobalTheory.LKDef.DMove.conj_conj` is `star_star`. In 10 of the 53 the line is one theorem
read in one direction or turned around. In the other 6 it is a general theorem, such as the
equality of two pairs with equal parts, together with a computation that Lean does by itself.

The shares of the sample carry over to the 72,983 statements with a margin. The share that
`exact?` closes is 5.3 %, with an interval from 4.1 % to 6.9 %, which is between 2,900 and
5,100 statements. The share that some tactic closes is 9.3 %, with an interval from 7.7 % to
11.3 %, which is between 5,500 and 8,300 statements. The numbers of statements are rounded
outward to the hundred, and an interval covers the chance of the draw alone.

The second run with 2,000,000 heartbeats closed no statement that the first run had left open.
After it `exact?` was still stopped at the limit on 96 statements of the sample, `aesop` on 7
and `simp_all` on 1. These are 100 different statements, and another tactic closed five of
them. The other 95 have an unfinished search and no proof. The shares count them as not closed,
so a search with a larger limit of heartbeats can only raise both shares.

The sample holds 46 statements whose proofs rest on more than 10 declarations, and the tactics
closed none of them. The 42 with 11 to 100 declarations are among the 2,655 statements of
middle size, and the four with more than 100 are among the 159 of the catalogue.

## The named theorems and the text of Mathlib's files

`exact?` finds a theorem of Mathlib whose conclusion fits the goal, and the other three tactics
rewrite and search with the rules of the libraries. A result that Mathlib states with other
definitions is outside the reach of `exact?`, and the other three tactics reach it only when
those rules turn one form into the other. A second search therefore went through the text of
Mathlib's files, comments included, for the names of the published results that the check of
the catalogue gives for the 29 named theorems other than the three forms of the Riemann
hypothesis. This document groups those names into 16 published results, and a language model
wrote a search pattern for each result from the words of its names. The table gives for each
result the entries of the catalogue, the number of the 8,712 files of Mathlib whose text
matches the pattern, and what those files hold. The patterns are in
[`mathlib_has.py`](mathlib_has.py).

| Published result, as this document groups the names of the check | Entries | Files | What the files hold |
|---|---|---:|---|
| Kronecker-Weber theorem, global and local | 7, 8, 14 | 0 | |
| Stein factorisation | 9 | 0 | |
| Zariski's connectedness theorem | 10, 17, 20 | 0 | |
| Borel's finiteness of class numbers | 26 | 0 | |
| Landherr's classification of hermitian forms | 36 | 0 | |
| Purity of the branch locus | 45, 50, 56, 57, 65 | 0 | |
| Chevalley's theorem on units | 49, 54 | 0 | |
| Serre's vanishing theorem | 59 | 0 | |
| Analytic normality | 62 | 0 | |
| First inequality of class field theory | 78 | 6 | Other uses of the words, such as Markov's inequality under the name of Chebyshev's first inequality |
| Addition theorem and duplication formula of the Weierstrass ℘-function | 95, 100 | 1 | The definition of ℘ and its derivative, their periods, that ℘ is meromorphic with poles of order 2, and the equation ℘′² = 4℘³ − g₂℘ − g₃. The file has no addition theorem and no duplication formula |
| Continuation and nonvanishing at 1 of the L-functions of ideal, ray class and Hecke characters | 104, 118, 154 | 1 | The definition of a Hecke character and of its L-function as an Euler product. The file proves no continuation and no value at 1 |
| Product formula | 108 | 12 | Five files on number fields state the product formula or a part of it with absolute values. Among them are `NumberField.prod_abs_eq_one` and the form `NumberField.AdeleRing.norm_algebraMap_eq_one_of_ne_zero` for the adele ring. The other seven files use the words for other products, such as the Euler product |
| Algebraicity of singular moduli | 126 | 0 | |
| Continuation of the Dedekind zeta function | 138, 148 | 1 | The definition of the Dedekind zeta function and its residue at 1 as a limit along the real line. The file proves no continuation |
| Connectedness of a complex variety | 145 | 0 | |

For 11 of the 16 results no file of Mathlib matches the pattern. For the first inequality the
six files that match use the words first inequality for other inequalities. For three results
Mathlib has the objects and the files that matched stop before the theorem. They define the
℘-function, Hecke characters with their L-functions and the Dedekind zeta function, and they
hold no addition theorem, no duplication formula, no continuation and no value at 1.

The product formula is the one result of the table that this search found proved in Mathlib.
Mathlib states it with absolute values, as a product over all places that equals 1, and with a
norm on the adele ring that equals 1 on the image of a nonzero element. Entry 108 of the
catalogue states it for a number field F with `distribHaarChar`, the factor by which
multiplication by an element scales the Haar measure of the adele ring of F. It says that this
factor is 1 for the image of a nonzero element of F. To pass from Mathlib's form to entry 108
one has to know that the factor is the product of the absolute values. A search of the text of
Mathlib's files for the name `distribHaarChar` matched one file, and the language model read
it. The file defines the factor for a group that acts on a locally compact additive group and
proves general properties of it, and it does not apply the factor to an adele ring. All four
tactics gave up on entry 108 within the first limit of heartbeats. Entry 108 is thus a case in
which Mathlib proves the published result in one form, the project proves it in another, and
the test finds nothing.

## What comes along with a statement

A statement that Mathlib lacks can be used in another Lean file, with the proof of the project,
by importing it from the project or by copying the declarations that its proof rests on. This
section counts what the import brings along. A Lean file that uses a theorem of the project imports
the module of the theorem, and Lean then loads every module that this module imports, directly
or through others. These are the modules that come along with the theorem. This section counts
the modules of the project among them and leaves out the module of the theorem itself.
[`import_cost.py`](import_cost.py) counts them for each statement of the catalogue from the
`import` lines of the project. The project has 149,397 modules, and 149,283 of them come along
with `Main.lean`.

Three of the 159 statements are forms of the Riemann hypothesis, and nearly the whole project
comes along with them, 149,283 modules with `riemannHypothesis`, which lies in `Main.lean`, and
149,281 with each of `critAll` and `rhOfAll`. The other 156 statements bring along between 2
and 19,922 modules. Half of the 156 bring along at most 120 modules, and 124 of them at most
1,000. The table gives the count for the 29 named theorems other than the three forms of the
Riemann hypothesis, with the short names of the Lean theorems.

| Entry | Theorem | Published result, by the check | The proof rests on | Modules that come along |
|---:|---|---|---:|---:|
| 7 | `kwHom` | Kronecker-Weber theorem | 4,902 | 410 |
| 8 | `kw` | Kronecker-Weber theorem | 4,901 | 409 |
| 9 | `stein_factorisation_connected_fibres` | Stein factorisation | 2,002 | 9,131 |
| 10 | `isConnected_closed` | Zariski's connectedness theorem, special case | 1,586 | 124 |
| 14 | `exists_le_adjoin_rootsOfUnity` | local Kronecker-Weber theorem | 1,460 | 96 |
| 17 | `zariski_connectedness_isPreconnected_fibre` | Zariski's connectedness theorem | 905 | 9,121 |
| 20 | `zariskiConnectedness_isPreconnected_fibre_affine` | Zariski's connectedness theorem, special case | 891 | 9,104 |
| 26 | `classNumber_finite_integralLevel_closedSubgroupGL` | Borel's finiteness of class numbers | 530 | 794 |
| 36 | `congr_of_det_norm` | Landherr's classification of hermitian forms, special case | 301 | 1,263 |
| 45 | `etale_atPrime_of_regular_of_isIntegrallyClosedIn` | purity of the branch locus | 254 | 135 |
| 49 | `exists_places` | Chevalley's theorem on units, special case | 251 | 284 |
| 50 | `etale_integralClosure_of_isArtinianRing` | purity of the branch locus | 249 | 128 |
| 54 | `exists_places_of_fg` | Chevalley's theorem on units, weaker | 245 | 284 |
| 56 | `etale_of_etale_height_one_of_regularLocalRing` | purity of the branch locus | 243 | 126 |
| 57 | `finiteRing_sq_sub_mul_sq_eq_of_card` | purity of the branch locus | 241 | 125 |
| 59 | `exists_coboundary_of_fraction_cocycle_homogeneous_ideal` | Serre's vanishing theorem, special case | 225 | 18 |
| 62 | `adicCompletion_isDomain_and_isIntegrallyClosed` | analytic normality, special case | 220 | 127 |
| 65 | `free_of_etale_on_punctured_spectrum` | purity of the branch locus, special case | 209 | 87 |
| 78 | `exists_idele_ne_algebraMap_mul_norm_of_not_isSquare` | first inequality of class field theory, special case | 170 | 81 |
| 95 | `dblA` | duplication formula of the ℘-function | 152 | 36 |
| 100 | `P_add` | addition theorem of the ℘-function | 148 | 105 |
| 104 | `exists_continuous_normCharLFunction_ne_zero_one` | nonvanishing at 1 of the L-function of a ray class character, weaker | 142 | 45 |
| 108 | `rational_units_haar_character_one` | product formula | 135 | 53 |
| 118 | `idealCharacterL_continuation_ne_zero_one` | Hecke's continuation of L-functions, weaker | 126 | 36 |
| 126 | `invariant_isAlgebraic` | algebraicity of singular moduli, special case | 120 | 1,326 |
| 138 | `exists_entire_sub_one_mul_euler_exp_ne_zero_one` | continuation of the Dedekind zeta function, weaker | 110 | 44 |
| 145 | `isPreconnected_points_over` | connectedness of a complex variety, special case | 108 | 2,560 |
| 148 | `dedekindZeta_eulerProduct_mul_sub_one_entire` | continuation of the Dedekind zeta function, weaker | 106 | 31 |
| 154 | `idealCharacter_LSeries_continuation` | Hecke's continuation of L-functions, weaker | 103 | 29 |

The words special case and weaker are the relation that the check of the catalogue gives
between the Lean statement and the published result, and an entry without such a word has the
relation same. 18 of the 29 theorems bring along at most 150 modules.

The two columns of numbers measure different things. The proof of entry 7 rests on 4,902
declarations and brings along 410 modules, and the proof of entry 9 rests on 2,002
declarations and brings along 9,131. A module brings along every module that it imports,
directly or through others, whether or not the proof uses their declarations.

[`README.md`](README.md) reports a test in which Lean compiled a file that imports the module
of `kwHom` alone and uses the theorem. Lean compiled the file without an error and printed
that `kwHom` depends on the axioms `propext`, `Classical.choice` and `Quot.sound` alone. The
other 28 theorems of the table were not compiled in this way.

## Limits

- The results are about one revision of Mathlib, of 16 November 2026. A later Mathlib can hold
  more.
- `exact?` can find a statement only when one theorem of the libraries proves it from the
  hypotheses of the statement. A statement that needs two theorems in a row is outside its
  reach, and so is a published result that Mathlib states with other definitions, as entry 108
  shows.
- The control measures `exact?` on theorems as Mathlib states them. No control measures the
  three other tactics.
- A tactic stopped at the limit has not finished its search. After the second run this
  concerns 23 statements of the catalogue and 95 statements of the sample that no tactic
  closed. The second run repeated 179 stopped runs of a tactic, 41 of the catalogue and 138 of
  the sample, with five times the heartbeats. 47 of them then gave up, 132 were stopped again
  and none closed a statement. The 2,655 statements with proofs of middle size had no second
  run, and 348 of them have a tactic that was stopped at 400,000 heartbeats.
- The search of the text of Mathlib's files goes by patterns that a language model wrote. A
  file of Mathlib can treat a result without matching its pattern. The language model read the
  files that the patterns and the name `distribHaarChar` matched and no other file of Mathlib.
- The published results of the tables are the answers of the check in `CATALOGUE.md`, which a
  language model gave from its own knowledge of the literature.
- The 72,983 statements count equal statements once only where the comparison of
  `../redundancy` covered them, so two of them can still be the same statement under two
  names.
- The compiled files of the project come from the build cache of the repository, and those of
  Mathlib from the cache of Mathlib.
- The modules that come along are counted from the `import` lines of the project, and the count
  was not compared with what Lean loads.

## Running it

The test needs a compiled checkout of this repository and the separate Lake folder, called
PROBE below, whose `lakefile.toml` requires Mathlib at the revision that this repository pins
and whose `lean-toolchain` names the same Lean. `lake exe cache get` in PROBE fetches the
compiled files of Mathlib, which take 6.7 GB.

```bash
python3 -I verification/reuse/mathlib_has.py prepare /path/to/compiled/checkout catalogue
python3 -I verification/reuse/mathlib_has.py prepare /path/to/compiled/checkout medium
python3 -I verification/reuse/mathlib_has.py prepare /path/to/compiled/checkout sample 1000 1
python3 -I verification/reuse/mathlib_has.py prepare PROBE control 300 1
python3 -I verification/reuse/mathlib_has.py run PROBE catalogue 5      # the same for medium, sample and control
python3 -I verification/reuse/mathlib_has.py retry PROBE catalogue 5 2000000   # the same for sample
python3 -I verification/reuse/mathlib_has.py collect catalogue          # the same for medium, sample and control
python3 -I verification/reuse/mathlib_has.py names PROBE
python3 -I verification/reuse/import_cost.py
```

The commands run from the root of the checkout. In the lines with `run` and `retry` the number
5 after the name of the set is the number of Lean sessions that run side by side, and `retry`
takes the limit of heartbeats after it. In the lines with `prepare` the two numbers after
`sample` and `control` are the size of the draw and its seed. A session needs one to three
minutes to load Mathlib. The memory of a session grows with every statement that it tries, so
`run` gives a session at most 150 statements and then starts a fresh one. A session of the
second run, which has no such bound, reached 7.8 GB on the machine of this run. Summed over the
sessions and with the loading left out, the tactics ran for 45 minutes on the catalogue, 3.6
hours on the sample, 3.5 hours on the 2,655 statements of middle size and 2 minutes on the
control.

## Files

| File | Content |
|---|---|
| `MathlibHas.lean` | poses statements to a Lean session with Mathlib alone and runs the tactics |
| `mathlib_has.py` | prepares the lists, starts the runs, collects the answers and searches the text of Mathlib's files |
| `mathlib_has.json` | the answers for the 159 statements of the catalogue |
| `mathlib_medium.json` | the answers for the 2,655 statements with proofs of middle size |
| `mathlib_sample.json` | the answers for the 1,000 statements of the sample |
| `mathlib_control.json` | the answers for the 279 theorems of the control |
| `mathlib_names.json` | the files of Mathlib that match the name of each published result |
| `import_cost.py`, `import_cost.json` | the modules that come along with each statement of the catalogue |
