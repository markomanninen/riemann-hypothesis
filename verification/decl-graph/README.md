# Declaration graph from the source text

The five theorems of [`Main.lean`](../../src/Main.lean) use between 91 % and 98 % of the
836,456 declarations in the project, by the estimate in this folder. Under the widest reading
of the text, 20,193 declarations, 2.4 % of the project, are used by none of the five theorems.

The estimate reads the source text and does not run Lean. The exact graph, read from the
compiled files of the whole project and described below, gives the real figure. The five
theorems use 800,348 of the 836,456 declarations, which is 95.7 %, and 36,108 declarations are
used by none of them. Of the six ways of reading the text, the widest, loose with automation,
gives the fewest wrong answers. It counts as unused 358 declarations that are really used, and
it counts as used 13,746 that are not. Both counts cover the 833,920 declarations that have a
compiled constant. Of the 20,193 declarations that the widest reading leaves unused, 20,184
have a compiled constant, and among those the exact graph leaves 33,572 unused, which is
20,184 plus 13,746 minus 358.

These figures are for the Lean 4.36 source of commit `611ce0b6`. The source as it was first
published, on Lean 4.33.1, had 1,061,531 declarations. The same script reached between 72 % and
82 % of them and left 192,718 unreached. Most of the declarations that the five theorems did not
use are gone from the present source.

## What the script does

A declaration is a `theorem`, `lemma`, `def`, `abbrev`, `structure`, `class`, `instance`,
`inductive` or `alias` command. `build.py` finds every declaration in `src/`, reads the names
that its text mentions and follows those names from the five theorems. A declaration is reached
when a chain of such mentions leads to it from one of the five. The script takes a reached
declaration as used by the five theorems.

The text does not always say which declaration a name means, so the script follows a name in
three ways. Each way reaches every declaration that the way before it reaches, and more.

| Way | What it follows |
|---|---|
| names | A name that resolves, as Lean resolves it, through the namespaces and `open` lines in scope, to a declaration that is visible from the module. A longer name may resolve by its front part, so `Foo.bar.symm` leads to `Foo.bar`. |
| fields | Also a name part after a dot, such as `down` in `s.down h`. Lean finds `down` through the type of `s`, which the text does not state. The script follows `down` to every visible declaration whose name ends in `.down`. The front part of such a name is the type's name, as `BlowupSequence` in `BlowupSequence.down`. When that type is a declaration of the project, the script waits until the type itself is reached. |
| loose | Also a name that did not resolve. The script follows it to every visible declaration whose last name part is that name. This covers an `open` line that the script failed to track. |

A declaration is visible from a module when its own module is among the modules that the first
module imports, directly or through other imports. A private declaration is visible only in its
own module.

Tactics use declarations that the text never names. `simp` uses the lemmas tagged `@[simp]`, and
instance search uses the instances. Each way is therefore run a second time, with automation
counted in. That run takes as reached every instance and every declaration that carries an
attribute a tactic can read, such as `@[simp]` or `@[ext]`, unless the instance or the attribute
is marked `local`. The project has 9,414 such declarations, instances included. Local instances, local notation and `variable` lines count, in every run, for the
declarations that follow them in their module.

## Results

The shares are of the project's 836,456 declarations.

| Way | Declarations reached | Share | Theorems and lemmas reached | Modules with a reached declaration |
|---|---:|---:|---:|---:|
| names | 760,989 | 91.0 % | 616,958 | 143,738 |
| fields | 801,592 | 95.8 % | 646,449 | 145,806 |
| loose | 807,489 | 96.5 % | 650,573 | 146,318 |
| names, with automation | 772,555 | 92.4 % | 621,397 | 144,300 |
| fields, with automation | 812,664 | 97.2 % | 650,648 | 146,222 |
| loose, with automation | 816,263 | 97.6 % | 653,169 | 146,564 |

The project has 149,396 modules, 15,175,520 lines and 666,737 theorems and lemmas. These counts
leave out `Challenge.lean`, a file that this repository added to the submission. The widest run
is the loose way with automation. It leaves 20,193 declarations unreached, and 2,832 modules,
with 194,944 lines, hold no reached declaration at all. Lean still has to load those modules,
because other modules import them.

The next table splits the declarations by library, the top folder under `src/`. Its middle
column is the names way without automation.

| Library | Declarations | Reached by names | Reached by the widest run |
|---|---:|---:|---:|
| Development | 565,741 | 518,101 | 550,117 |
| Formalism | 174,526 | 159,290 | 171,351 |
| GroundTheory | 50,072 | 43,001 | 49,237 |
| ReciprocityTheory | 32,040 | 27,108 | 31,628 |
| CompanionTheory | 10,705 | 10,396 | 10,664 |
| PositivityTheory | 3,124 | 2,869 | 3,027 |
| Lemmata | 235 | 215 | 230 |
| Main, Statements and Supplements | 13 | 9 | 9 |

The four declarations of `Supplements` prove the results of `Main` a second time, and `Main`
does not use them.

## Check against a compiled sample

The check was made on the source as first published, before the port to Lean 4.36, and its
figures are of that source. The module
`Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys` and the 2,680 project modules
it imports were compiled with Lean 4.33.1. They hold 23,043 declarations and
326,641 lines, 1.9 % of the project's lines. None of these modules defines a tactic, a macro or a
command, so compiling them ran only Lean's and Mathlib's own code.

A compiled declaration is a constant, and Lean adds helper constants of its own to a
declaration. `SampleDeps.lean` lists, for every constant of the sample, the project constants
that its type and its proof term contain, and `check_sample.py` assigns each constant to the
declaration it came from. These are the real uses.

`XCSqsys` itself holds five declarations. They stand in for the five theorems of `Main`, which
the sample does not contain. `check_sample.py` follows the real uses from those five, which
really reaches 2,420 of the sample's declarations. It then follows the text from the same five
in each way and compares. It follows the text with the rules of `build.py` and stays inside the
sample.

| Way | Reached in the text | Really reached and in the text | Really reached but missing from the text | In the text but not really reached |
|---|---:|---:|---:|---:|
| names | 2,359 | 2,279 | 141 | 80 |
| fields | 3,124 | 2,415 | 5 | 709 |
| fields, with automation | 5,881 | 2,418 | 2 | 3,463 |
| loose, with automation | 6,287 | 2,418 | 2 | 3,869 |

The table shows three things about the sample.

- The fields way finds 2,415 of the 2,420 really reached declarations and the widest run finds
  2,418. Almost nothing that is really reached lies outside them.
- The names way misses 141 of the 2,420, which is 5.8 %. The misses are declarations called
  through a dot, such as `h.map`. It also reaches 80 declarations that are not really reached.
- The wider ways reach more than is really reached. The fields way reaches 3,124, which is 1.3
  times the real 2,420, and the widest run reaches 2.6 times the real number.

Seen one use at a time, the text misses more. The compiled sample has 120,983 uses of one
project declaration by another, and no way of following the text finds 24,697 of them, which is
20 %. Most of those uses come from types that Lean fills in and the text leaves out. The
declarations they lead to are nearly all reached through another chain, which is why only two
are missing from the widest run.

The sample is one branch of the project and its roots are not the theorems of `Main`, so these
ratios do not carry over to the whole project as they stand. The sample also defines no tactic
or macro, and automation adds a larger share in it than in the whole project. In the sample the
widest run missed two declarations in 2,420 and reached 2.6 times too many. If the whole project
behaves the same way, more declarations are unused than the widest run counts as unreached. The
sample makes that likely and does not prove it.

## The exact graph from the compiled project

The compiled files of the whole project come with `lake exe cache get`, so nothing has to be
built for this graph. `ExactGraph.lean` reads the compiled files of each module without
importing the module into Lean. A module written with Lean's module system keeps its proofs in
a private part, `.olean.private`, which shares objects with the public parts `.olean` and
`.olean.server`, so the script reads the three parts together. For every constant it writes
every project or library constant that the constant's type and value mention. Reading the
149,396 modules took about two and a half hours from an external disk. In a timed run of 1,991
modules Lean computed for 9 of the 246 seconds, so the time is spent waiting for the disk.

`exact_graph.py` then follows these mentions from the five theorems of `Main`. A constant that
Lean creates itself, such as `_proof_1`, `_simp_1` or `match_1`, is followed like any other, so
a use that passes through such a helper counts. An inductive type or a structure also leads to
each of its constructors, because the type of a constructor holds the types of the fields, and
Lean's command `#print axioms` takes the same step. The project has 6,629 such types with 6,880
constructors. The figures below are for commit `611ce0b6`.

| Figure | Count |
|---|---:|
| compiled constants of the project | 1,550,842 |
| of them matched with a declaration of the text | 833,920 |
| of them Lean's helper constants | 716,922 |
| mentions between project constants, the 6,880 steps to constructors included | 16,574,237 |
| declarations of the text that have no compiled constant | 2,536 |
| declarations reached from the five theorems | 800,348 |

The 2,536 declarations without a compiled constant are 2,498 instances without a name, whose
name Lean generates and the text does not know, and 38 others. The exact graph cannot say
whether they are used, and the 36,108 unused declarations above include them. The 800,348
reached declarations are 95.7 % of all 836,456 and 96.0 % of the 833,920 that have a compiled
constant. The library `Supplements` holds four theorems, among them `allChi`, and no theorem of
`Main` uses any of them.

The next table compares each of the six ways of reading the text, described in the section What the script does,
with the exact graph. It counts only the 833,920 declarations that have a compiled
constant, since only those have an exact answer. The figures of `summary.json` count all
836,456 declarations and are therefore a few thousand higher.

| Way | Reached in the text | Reached in both | Only in the text | Only in the exact graph |
|---|---:|---:|---:|---:|
| names | 760,884 | 755,501 | 5,383 | 44,847 |
| names, with automation | 770,045 | 762,602 | 7,443 | 37,746 |
| fields | 801,470 | 791,580 | 9,890 | 8,768 |
| fields, with automation | 810,137 | 797,960 | 12,177 | 2,388 |
| loose | 807,367 | 795,012 | 12,355 | 5,336 |
| loose, with automation | 813,736 | 799,990 | 13,746 | 358 |

The table shows four things.

- The widest run misses 358 of the 800,348 really reached declarations, which is 0.04 %. In the
  compiled sample of the previous section it missed two of 2,420, which is 0.08 %.
- The widest run counts 13,746 declarations as reached that are not, which is 1.7 % more than
  the real number. In the compiled sample it reached 2.6 times the real number. A wrong count
  can only come from declarations that are really unused. In the sample the five roots really
  reach 2,420 of 23,043 declarations, so 20,623 unused declarations are open to a wrong count.
  In the whole project the five theorems really reach 96 % of the declarations, so only about
  33,600 are open to it, and the ratio of the sample cannot recur.
- The names run misses 44,847 really reached declarations, 5.6 % of them, close to the 5.8 % of
  the sample. The fields way, which also follows a name part after a dot such as `map` in
  `h.map`, finds 36,079 of these 44,847.
- The names run also counts 5,383 declarations that the exact graph does not reach. Two causes
  were seen in the cases read by hand. The text resolves a name to the wrong one of two
  declarations with the same last part, as `OrdGe` in
  `GlobalTheory.Poinc.exists_locTuples_theta_of_adm`, which the text takes as
  `GlobalTheory.LocM.OrdGe` while Lean uses `GlobalTheory.Poinc.OrdGe`. And a lemma named in a
  `simp` list that `simp` did not use, as `discreteCoindRep_apply` in
  `GroundTheory.ProfCoh.coindHomotopy_identity_apply`, is no use of that lemma.

The exact graph counts what the compiled terms mention. It does not tell whether a mentioned
declaration could be removed, since a proof could often be rewritten without it.

## The axioms of the five theorems

`exact_axioms.py` follows the constants that each constant's type and value mention further,
through the compiled files of Mathlib, the other packages and Lean's own library, as Lean's
command `#print axioms` does. Like that command it also goes from an inductive type to its
constructors. It read 2,353,852 constants, of which 1,491,315 are reached from
the five theorems of `Main`. Besides the 800,348 reached declarations of the project, these are
Lean's helper constants and the constants of the libraries. Every reached name
has a compiled entry, so the search has no gap.

The five theorems rest on three axioms, which are the three that Lean and Mathlib use
throughout.

| Axiom | One chain of mentions that leads to it |
|---|---|
| `propext` | `riemannHypothesis`, `Claim.zeta`, `propext` |
| `Classical.choice` | `riemannHypothesis`, `Claim.zeta`, `Real.linearOrder`, `Classical.propDecidable`, `Classical.choice` |
| `Quot.sound` | `riemannHypothesis`, `Claim.zeta`, `DirichletCharacter.LFunction_modOne_eq`, `funext`, `Quot.sound` |

The compiled project holds no constant of kind axiom. In Lean 4.36 the tactic `native_decide`
adds an axiom named `_native.native_decide.ax` with a number to the module that uses it, so the
project does not use `native_decide` anywhere. No reached constant leads to `sorryAx`, the axiom
that a `sorry` in a proof leaves behind. The search read `sorryAx` as an axiom of Lean's library
and reports every reached axiom, so it would have found a chain to it if one existed.

## The declarations that the five theorems do not use

[`unused.py`](unused.py) sorts the 36,108 declarations that the exact graph does not reach from
the five theorems of `Main`. They are 4.3 % of the 836,456 declarations, and among them are
20,207 theorems, 10,444 definitions, 2,723 instances, 1,032 abbreviations, 996 structures, 622
lemmas and 84 others. The library `Development` holds 24,867 of them and `Formalism` 7,306.

The table sorts the 36,108 declarations by whether another declaration states the same thing.
Two declarations state the same thing when the table `same_checked.tsv.gz` of
[`../redundancy`](../redundancy/README.md) lists them as a pair whose compiled statements Lean
compared and found equal.

| Sort | Declarations |
|---|---:|
| Has no compiled constant of its own, so the exact graph cannot judge it | 2,536 |
| States exactly what a used declaration states | 1,389 |
| States exactly what only other unused declarations state | 1,671 |
| States a statement of its own | 30,512 |

Of the 2,536 without a compiled constant, 2,498 are instances without a name. Lean compiles
each of them under a name it makes up, and the declaration table `data/declarations.tsv.gz`,
which `build.py` makes from the source text, has no such name to match. The
30,512 with a statement of their own are 17,923 theorems and lemmas, 10,290 definitions and
2,299 others. A theorem among them can still be a weaker form or a special case of a used
theorem, which a comparison of exact statements does not find.

The unused declarations lie almost all in modules that the five theorems import. The import
graph of [`../import-graph`](../import-graph/README.md) puts 35,637 of them in modules that
`Main.lean` imports, directly or through other modules. The other 471 lie in 112 modules that
`Main.lean` does not import, and the build compiles those because the lakefile names every
module of a library. In 3,494 modules no declaration is used, and these modules hold 16,120
of the unused declarations.

### Where the unused part starts

A constant mentions another when its compiled type or value names it. Besides the declarations
of the source, Lean compiles helper constants of its own, such as the equation lemmas of a
definition, and these have no row in the declaration table. The five theorems leave 275,178
constants of the project unreached, the 33,572 unused declarations that have a compiled
constant and 241,606 helper constants.

A top is an unused declaration that no constant of the project mentions. There are 9,021 tops,
6,222 theorems and lemmas, 2,694 definitions and abbreviations and 105 others. A top reaches a
declaration when a chain of mentions through unused constants, helper constants included, leads
from the top to it, and every top reaches itself. 5,513 tops reach no other declaration, and
the other 3,508 do. The 33,572 compiled unused declarations, tops included, divide by how many
tops reach them.

- 24,749 are reached from one top only.
- 7,767 are reached from several tops.
- 1,056 are reached from no top. Each of them is mentioned only by unused helper constants,
  and no top leads to those.

When the direction of a mention is ignored, the compiled unused declarations and the helper
constants between them fall into 7,340 groups. 5,456 groups hold one declaration. Of the 5,513
tops that reach no other declaration, 197 share a group with other declarations, because a
helper constant that such a top mentions is also mentioned by another declaration. The other
5,316 tops are groups of one, and 140 further groups of one hold a declaration that only helper
constants mention.
The largest group holds 11,552 declarations with 721 tops. Most of its declarations lie in
`Development.AbelianVarietyTheory.Proofs` (3,750), in
`Development.AbelianVarietyTheory.Definitions` (3,409) and in
`Development.AutomorphicArithmetic.AutomorphicVarieties` (1,754). The next groups hold 611, 439
and 400 declarations.

The table lists the five tops that reach the most unused declarations. The column Reaches counts
the declarations that a top reaches, itself included, and the column Alone counts those of them
that no other top reaches.

| Top | Reaches | Alone |
|---|---:|---:|
| `GlobalTheory.ThK.Partner.partner_of_big` | 1,045 | 748 |
| `GlobalTheory.ShFam.IsKitOf` | 988 | 266 |
| `UpperTheory.V.Th.core` | 891 | 214 |
| `GlobalTheory.T.weil_convergence_of_kernel` | 752 | 301 |
| `GlobalTheory.ThK.ModelPol.exists_modelChange_pol` | 678 | 153 |

`IsKitOf` is a definition, and the other four are theorems. `weil_convergence_of_kernel` stands
in a module whose name ends in `Statement`. Its proof consists of one other theorem, so the
declarations that it reaches are that theorem and the declarations its proof uses. Three modules
each hold a private theorem of their own with the source name `UpperTheory.V.Sd.EG.core`. These
three theorems are tops, and they reach 522, 496 and 496 declarations, each itself included.

### The supplements and the lemmata

The library `Supplements` has four unused declarations, the theorems `allChi`, `rhOfAll`,
`claimAll` and `critAll` of
[`Supplements/Kernels/MainTheorems.lean`](../../src/Supplements/Kernels/MainTheorems.lean).
`allChi` is the theorem `UpperTheory.FinalTheorems.everyCharacter` under another name, and the
five theorems of `Main` use `everyCharacter`. The other three derive from `allChi` the
following statements.

- `rhOfAll` states the Riemann hypothesis.
- `claimAll` states three claims that the code calls `Claim.HalfPlane`, `Claim.Strip` and
  `Claim.Zeta`.
- `critAll` states that a zero of the L-function of a primitive Dirichlet character in the
  critical strip has real part 1/2.

The five theorems of `Main` use `everyCharacter` and its proof, so the four theorems add no
proof of their own to what the five use, and nothing in `Main` uses the four. The library `Lemmata` has nine unused declarations. Six of them are
theorems named `goal1` in six modules, and three are private helper theorems of those modules.

### The axioms of the unused part

`unused.py` follows the mentions of all 275,178 unreached constants through the project,
Mathlib, the other packages and Lean's own library, as `exact_axioms.py` does from the five
theorems in the section on their axioms. These constants lead to the same
three axioms as the five theorems, `propext`, `Classical.choice` and `Quot.sound`, and every
name met on the way has a compiled entry. Every constant of the project is either reached from
the five theorems or is one of the 275,178 unreached ones, so the two parts together cover the
project, and neither part leads to `sorryAx` or to an axiom of the project. A `sorry` leaves
`sorryAx` behind, and `native_decide` adds an axiom of the project to the module that uses it,
as the section on the axioms of the five theorems says. No compiled declaration of the project
therefore uses `sorry`, `native_decide` or an axiom of its own.

A declaration that no constant reached from the five theorems mentions plays no part in their
compiled proofs. Removing such a declaration could still change what a tactic finds while Lean
builds a proof, for example when `simp` tries it, so only a new build would show that the five
theorems still compile without it.

## Limits

- The script reads text. A layout it does not expect can attach a name to the wrong declaration.
- The script found 126 public names a second time, each in another module. In the first
  published source there were 135, all of them theorems or lemmas, and one pair that was checked
  by hand, `Bl.general_b_fact.goal1`, stood in two files that were the same byte for byte. The
  script takes the copy that the using module imports.
- A `scoped` instance counts as automation everywhere, although Lean uses it only where its
  namespace is open. Such instances make the automation runs reach more.
- The command `cpt_copy_thms` copies declarations under new names when Lean runs. The copies
  are not in the text, so the script follows a name ending in `Cpt` to the original.
- An instance without a name gets its name from Lean. A mention of such a generated name in the
  text is not resolved.
- The exact graph reads the compiled files that `lake exe cache get` downloads. Volunteers'
  machines build those files for the upstream repository, so the graph is as reliable as that
  cache. It does not check any proof.

## Running it

```bash
python3 -I verification/decl-graph/build.py    # about two minutes, 6 GB of memory
```

The exact graph needs a checkout of the same commit with the compiled files in place. The chunks
go to `data/exact`, and an interrupted run continues from the first unfinished chunk.

```bash
lake exe cache get                                                    # in that checkout
python3 -I verification/decl-graph/exact_extract.py /path/to/that/checkout   # about 2.5 hours
python3 -I verification/decl-graph/exact_graph.py                    # about half a minute, 6 GB of memory
python3 -I verification/decl-graph/exact_axioms.py /path/to/that/checkout    # about 20 minutes the first time
python3 -I verification/decl-graph/exact_axioms.py /path/to/that/checkout NAME   # the axioms of one constant
python3 -I verification/decl-graph/unused.py                         # about half a minute, 7 GB of memory
python3 -I verification/decl-graph/statement_extract.py /path/to/that/checkout   # about two hours
```

The check needs a checkout of the first published source in which the sample module is built.

```bash
lake build Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
cp verification/decl-graph/SampleDeps.lean . && lake env lean --tstack=400000 SampleDeps.lean
python3 -I verification/decl-graph/check_sample.py deps.tsv \
  Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
```

## Files

| File | Content |
|---|---|
| `build.py` | the script that builds the graph and runs the six reachability runs |
| `summary.json` | the figures of the six runs, per library as well |
| `SampleDeps.lean` | lists the real uses in a compiled sample |
| `check_sample.py` | compares the text graph with those real uses |
| `sample-check.json` | the figures of the check |
| `data/declarations.tsv.gz` | one row per declaration with its module, kind and whether each run reaches it |
| `data/graph.npz` | the edges of the graph as arrays |
| `data/modules.txt.gz` | the modules in the order the arrays number them |
| `data/sample-deps.tsv.gz` | the real uses of the compiled sample, as `SampleDeps.lean` wrote them |
| `ExactGraph.lean` | reads every constant of the compiled modules with the constants it mentions |
| `exact_extract.py` | runs `ExactGraph.lean` on all modules in chunks |
| `exact_graph.py` | follows the exact graph from the five theorems and compares it with the text runs |
| `exact-summary.json` | the figures of the exact graph and of the comparison |
| `exact_axioms.py` | reads the libraries as well and lists the axioms of the five theorems with a chain to each |
| `exact-axioms.json` | those axioms and chains |
| `unused.py` | sorts the declarations that the five theorems do not use |
| `StatementGraph.lean` | reads, for every public constant, the constants that its type mentions |
| `statement_extract.py` | runs `StatementGraph.lean` on all modules in chunks, for [`../reuse`](../reuse/README.md) |
| `data/exact/types-*.tsv.gz` | the public constants and what their types mention |
| `unused.json` | the figures of that sorting and the 40 tops that reach the most |
| `data/exact/lib-*.tsv.gz` | the constants of each library and their mentions |
| `data/exact/chunk-*.tsv.gz` | the constants and their mentions, as `ExactGraph.lean` wrote them |
| `data/exact_graph.npz` | the exact graph as arrays, with the declaration row of each node and whether it is reached |
| `data/exact_nodes.tsv.gz` | one row per compiled constant with its module, name, kind, declaration row and reach |

Git ignores `data/`. `build.py` writes its three files again on every run. The sample file
comes from the compiled sample and has to be kept, and the chunks of the exact graph take
2.5 hours to write again.
