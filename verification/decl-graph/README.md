# Declaration graph from the source text

The five theorems of [`Main.lean`](../../src/Main.lean) use between 91 % and 98 % of the
836,456 declarations in the project, by the estimate in this folder. Under the widest reading
of the text, 20,193 declarations, 2.4 % of the project, are used by none of the five theorems.

The estimate reads the source text and does not run Lean. A check against a compiled sample of
2,681 modules, described below, shows how far the text can be trusted.

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
- The exact graph needs the compiled files of the whole project. `lake exe cache get` now
  downloads them, so `SampleDeps.lean` could be run for all modules in place of the sample. That
  run has not been made here.

## Running it

```bash
python3 -I verification/decl-graph/build.py    # about two minutes, 6 GB of memory
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

Git ignores `data/`. `build.py` writes its three files again on every run. The sample file
comes from the compiled sample and has to be kept.
