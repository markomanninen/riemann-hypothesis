# Declaration graph from the source text

The five theorems of [`Main.lean`](../../src/Main.lean) use between 72 % and 82 % of the
1,061,531 declarations in the project, by the estimate in this folder. Under the widest reading
of the text, 192,718 declarations, 18 % of the project, are used by none of the five theorems.

The estimate reads the source text and does not run Lean. A check against a compiled sample of
2,681 modules, described below, shows how far the text can be trusted.

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
is marked `local`. The project has 15,347 such declarations, instances included. Local instances, local notation and `variable` lines count, in every run, for the
declarations that follow them in their module.

## Results

The shares are of the project's 1,061,531 declarations.

| Way | Declarations reached | Share | Theorems and lemmas reached | Modules with a reached declaration |
|---|---:|---:|---:|---:|
| names | 763,510 | 71.9 % | 619,011 | 144,369 |
| fields | 819,875 | 77.2 % | 656,675 | 147,909 |
| loose | 849,490 | 80.0 % | 678,144 | 152,811 |
| names, with automation | 787,461 | 74.2 % | 630,041 | 145,836 |
| fields, with automation | 843,752 | 79.5 % | 667,967 | 149,043 |
| loose, with automation | 868,813 | 81.8 % | 686,930 | 153,560 |

The project has 175,187 modules, 17,374,215 lines and 818,755 theorems and lemmas. These counts
leave out `Challenge.lean`, a file that this repository added to the submission. The widest run
is the loose way with automation. It leaves 192,718 declarations unreached, and 21,627 modules,
with 1,553,506 lines, hold no reached declaration at all. Lean still has to load those modules,
because other modules import them.

The next table splits the declarations by library, the top folder under `src/`. Its middle
column is the names way without automation.

| Library | Declarations | Reached by names | Reached by the widest run |
|---|---:|---:|---:|
| Development | 693,010 | 519,703 | 583,431 |
| Formalism | 240,188 | 160,031 | 182,901 |
| GroundTheory | 75,102 | 43,078 | 55,504 |
| ReciprocityTheory | 36,446 | 27,188 | 32,474 |
| CompanionTheory | 11,775 | 10,407 | 10,988 |
| PositivityTheory | 4,746 | 2,870 | 3,267 |
| Lemmata | 251 | 220 | 235 |
| Main, Statements and Supplements | 13 | 13 | 13 |

The library `BuildAid` has five modules and no declarations.

## Check against a compiled sample

The module `Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys` and the 2,680
project modules it imports were compiled with Lean 4.33.1. They hold 23,043 declarations and
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
behaves the same way, the 192,718 unreached declarations are too few. The sample makes that
likely and does not prove it.

## Limits

- The script reads text. A layout it does not expect can attach a name to the wrong declaration.
- The script found 135 public names a second time, each in another module. All 135 are theorems
  or lemmas. One pair that was checked by hand, `Bl.general_b_fact.goal1`, stands in two files
  that are the same byte for byte. The script takes the copy that the using module imports.
- A `scoped` instance counts as automation everywhere, although Lean uses it only where its
  namespace is open. The project has 220 of them, and they make the automation runs reach more.
- The command `cpt_copy_thms` copies declarations under new names when Lean runs. The copies
  are not in the text, so the script follows a name ending in `Cpt` to the original.
- An instance without a name gets its name from Lean. A mention of such a generated name in the
  text is not resolved.
- The exact graph needs the whole project compiled. On the machine used here the sample took
  4 h 13 min for 2,681 modules, and the same pace over 175,187 modules is about 11.5 days. The
  pace was set by the external disk and the 48 GB of memory, since the processors stood idle
  about 80 % of the time.

## Running it

```bash
python3 -I verification/decl-graph/build.py    # about two minutes, 6 GB of memory
```

The check needs a checkout in which the sample module is built.

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
