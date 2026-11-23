# Argument skeleton from the declaration graph

The five theorems of [`Main.lean`](../../src/Main.lean) rest on 760,989 declarations of the
project, by the estimate used here, and 99.9 % of those are reached only through one theorem,
`UpperTheory.FinalTheorems.everyCharacter`. In all, 590 declarations are each the only way from
the five theorems to at least 999 other declarations. These 590 form a tree, which this README
calls the skeleton of the argument.

The figures come from the source text after upstream main was merged into this repository on
2026-11-22. That merge moved the project to Lean 4.36 and removed files, and the source now
holds 836,456 declarations in 149,396 modules, where it held 175,187 modules before. The
scripts read text and do not run Lean. A check against a compiled sample, described below,
measures how well the text agrees with compiled code on one small part of the project.

## Words used here

- A module is one source file of the project.
- A declaration is a `theorem`, `lemma`, `def`, `abbrev`, `structure`, `class`, `instance`,
  `inductive` or `alias` command of the project. Its statement is its text before the proof.
- The declaration graph is the graph of [`../decl-graph`](../decl-graph/README.md). In it a
  declaration points to every declaration of the project that its text names. This README
  follows the names that resolve as Lean resolves them, which that README calls the names way.
- A chain is a path in the declaration graph. A declaration is reached when a chain leads to it
  from one of the five theorems. The names way reaches 760,989 declarations, 91.0 % of the
  project.
- A declaration D dominates another declaration E when every chain from the five theorems to E
  passes through D. The five theorems then depend on E only by way of D.
- The immediate dominator of E is the dominator of E that all the other dominators of E
  dominate. It is the last declaration that every chain to E has to pass.
- The dominator tree holds every reached declaration below its immediate dominator. The script
  adds one start point that points to the five theorems, so every reached declaration has an
  immediate dominator and the tree has one top. The level of a declaration is the number of
  steps from the start point to it.
- A declaration gathers the declarations that it dominates. The number it gathers counts the
  declaration itself as well.
- The skeleton is the set of declarations that gather at least 1,000 declarations. In the
  skeleton each of them hangs from the nearest skeleton declaration that dominates it.
- A wrapper is a skeleton declaration that passes at least 99 % of what it gathers on to one
  skeleton declaration that hangs directly from it. A head is a skeleton declaration that is no
  wrapper.
- The own pool of a skeleton declaration D is the set of declarations that D gathers and that
  no skeleton declaration below D gathers. A declaration that chains through two different
  branches below D both lead to lies in the own pool of D, unless a skeleton declaration below
  D dominates it.

## What the scripts do

[`build.py`](build.py), which lies next to this README, reads the graph that
`../decl-graph/build.py` wrote and
computes the immediate dominator of every reached declaration with the iteration of Cooper,
Harvey and Kennedy. It counts what every declaration gathers, picks the skeleton and reads the
statement of each skeleton declaration from the source with the statement splitter of
[`../explorer/build_statements.py`](../explorer/build_statements.py).

`test_tree.py` runs the dominator routine on 400 random graphs, each with two start nodes, and
compares the result with the routine of the networkx library. All 400 agree.

## Results

The dominator tree is 47 levels deep. The table counts the declarations that gather at least a
given number of declarations.

| Gathers at least | Declarations |
|---:|---:|
| 100,000 | 6 |
| 10,000 | 62 |
| 1,000 | 590 |
| 100 | 5,730 |

Of the 590 skeleton declarations, 588 are `theorem` commands and two are `alias` commands. 248
are wrappers, which leaves 342 heads.

The largest skeleton declaration is `LFunction_ne_zero_of_half_lt_re`, one of the five
theorems, and it gathers 760,227 declarations. The other 762 reached declarations, the four
other theorems among them, lie outside it. Its proof applies the theorem `everyCharacter`, which
gathers 760,225.

[`OUTLINE.txt`](OUTLINE.txt) lists the skeleton declarations that gather at least 10,000
declarations. A line holds the number gathered and the name, and it is indented below the line
of the declaration it hangs from. A run of wrappers is folded, together with the head that the
run ends in, into the line of the first wrapper, whose number the line shows. The square
brackets give the number of the other folded declarations and the name of that head, and the
lines indented below hang from that head. The folds take 24 of the 62 declarations, so the file
has 38 lines. These are the lines that gather at least 40,000.

```
  760,227  LFunction_ne_zero_of_half_lt_re  [1 more to UpperTheory.FinalTheorems.everyCharacter]
  577,248    UpperTheory.FinalTheorems.everyCharacter_of_row
  506,214      UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
  315,443        UpperTheory.Lit.every_character_of_theta_integrals_local_matching
  266,135          UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
   89,671            GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt
   52,094        SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
   55,754      UpperTheory.One.vwin_of_row  [1 more to UpperTheory.One.Join.automorphic_window_of_inputs]
   55,113        UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm  [2 more to UpperTheory.V.HV.DescentVanishingReductions.v_window_of_automorphy_csd_ss_mono_odd]
   47,836          UpperTheory.V.HV.DescentVanishingReductions.vwin_of_hypotheses_H_E_alt
   51,784    UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
   48,992      UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift
   43,403        UpperTheory.Gal.Int.Geo.geoOne_holds
   41,443          UpperTheory.Gal.Int.Geo.geometric_realization_of_weight_one
```

The top of the tree matches the two short proofs in
[`MainConclusion.lean`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean).
`everyCharacter` calls `everyCharacter_of_row` with the theorem
`galoisLocalGlobalStrong_recParameter`. `everyCharacter_of_row` calls
`every_character_of_literature_of_vWin` and `vwin_of_row`. The next table gives, for eight
declarations of the outline, the number each gathers, its share of the 760,989 reached
declarations and the size of its own pool.

| Declaration | Gathers | Share of the reached | Own pool |
|---|---:|---:|---:|
| `UpperTheory.FinalTheorems.everyCharacter` | 760,225 | 99.9 % | 116,470 |
| `UpperTheory.FinalTheorems.everyCharacter_of_row` | 577,248 | 75.9 % | 12,939 |
| `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` | 506,214 | 66.5 % | 89,709 |
| `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` | 315,443 | 41.5 % | 30,658 |
| `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` | 266,135 | 35.0 % | 113,675 |
| `UpperTheory.One.vwin_of_row` | 55,754 | 7.3 % | 1 |
| `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` | 52,094 | 6.8 % | 9,407 |
| `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` | 51,784 | 6.8 % | 13 |

The own pool of `everyCharacter` holds 116,470 declarations. The chains from `everyCharacter`
to any one of them do not all pass through one skeleton declaration below `everyCharacter`.

The large branches of the skeleton spread over several folders of the source, where a folder
is the first two parts of a module name. `skeleton.json` lists for every skeleton declaration
up to four folders, those that hold the largest numbers of the declarations it gathers. Of the
266,135 declarations that `nonempty_hyps_definite_side_of_closed_bound` gathers, 143,873 lie in
`Development.AbelianVarietyTheory`, which is 54 %, and 36,656 in `Formalism.LocalToGlobal`. Of
the 51,784 that `galoisLocalGlobalStrong_recParameter` gathers, the largest folder is again
`Development.AbelianVarietyTheory`, with 18,772 or 36 %. `vwin_of_row` is closer to one folder,
with 41,081 of its 55,754, or 74 %, in `Development.AutomorphicArithmetic`.

## With every repeated statement counted once

[`../redundancy`](../redundancy/README.md) lists the theorems that Lean found to state exactly
what another theorem states. `clean.py` joins such theorems into classes and keeps one theorem of
each class, its keeper. It prefers a keeper that is no forwarding theorem, points every mention
of another member at the keeper, and leaves the other members out with their own proofs. It then
computes the dominator tree and the skeleton of this smaller graph.

| Measure | Whole graph | Repeats counted once |
|---|---:|---:|
| Declarations that the five theorems reach | 760,989 | 694,428 |
| Declarations that gather at least 100,000 | 6 | 5 |
| Declarations that gather at least 10,000 | 62 | 42 |
| Skeleton declarations, which gather at least 1,000 | 590 | 397 |
| Wrappers among them | 248 | 100 |
| Heads among them | 342 | 297 |
| Levels of the dominator tree | 47 | 38 |

The script leaves out 62,905 theorems, the number of repeats that the README of `../redundancy`
reports. Of the 590 skeleton declarations of the whole graph, 139 are left out as repeats, 393
are skeleton declarations of the smaller graph too, and 58 are kept and gather less than 1,000
there. The largest declarations keep their order. `everyCharacter` gathers 693,666,
`everyCharacter_of_row` 524,040 and `every_character_of_literature_of_vWin` 459,773.

The figures estimate what such a cleanup would leave. The source is unchanged, and no part of
the smaller graph has been compiled. A keeper can lie in a module that a user of another member
does not import, which the count ignores. Definitions with the same text are not joined.

## Check against a compiled sample

The sample of [`../decl-graph`](../decl-graph/README.md) is the module
`Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys` and the 2,680 project modules
it imports, compiled with Lean 4.33.1 from the source before the merge. For every compiled
declaration Lean listed the project declarations that its type and its proof term contain.
`check_sample.py` builds two graphs over the 23,043 declarations of the sample. The compiled
graph holds those listed uses, and the text graph holds the uses that the names way finds in
the same source. The
five declarations of `XCSqsys` stand in for the five theorems, and the script computes the
dominator tree of each graph from them.

The skeleton limit of 1,000 is 0.13 % of the reached declarations, which would be 3
declarations in the sample. The check uses larger shares, 1 % and 5 % of the 2,420 declarations
that the compiled graph reaches, which are 24 and 121 declarations.

| | Compiled graph | Text graph | Both |
|---|---:|---:|---:|
| Declarations reached | 2,420 | 2,357 | 2,279 |
| Declarations that gather at least 24 | 64 | 64 | 60 |
| Declarations that gather at least 121 | 14 | 11 | 11 |

Of the 2,279 declarations that both graphs reach, 2,171 have the same immediate dominator in
both trees, which is 95.3 %. For 2,199 of them, 96.5 %, the immediate dominator of the text tree
dominates the declaration in the compiled tree too, as the immediate dominator or as one above
it.

The next figures are about pairs. A pair of a tree is a declaration that gathers at least 24 in
that tree and one of the other declarations it gathers there. A pair holds in the other tree when
the first declaration dominates the second one there, whatever number it gathers there. The
text tree has 8,275 pairs, and 7,746 of them, 93.6 %, hold in the compiled tree. The compiled
tree has 8,362 pairs, and 7,772 of them, 92.9 %, hold in the text tree. For the 60 declarations
that gather at least 24 in both trees, the number gathered in the text tree divided by the
number gathered in the compiled tree has the median 0.99, the lowest value 0.44 and the highest
value 1.20.

The sample is one module with its imports, taken from the source before the merge. Its five
start declarations are not the five theorems, and they reach 2,420 declarations where the five
theorems reach 760,989. The rates above are therefore measured on a small part of the project
and are not rates of the whole skeleton.

## Limits

- The names way misses uses that the text does not name. By the README of `../decl-graph`, it
  found 73 % of the uses that Lean listed in the sample. A missed use can make a declaration
  look dominated when a second chain really reaches it, which makes a number gathered too
  large. It can also leave a declaration unreached, which makes a number gathered too small.
- The names way also follows names that Lean does not use. By the same README, 3 % of the uses
  it followed in the sample were of that kind. Such a use can add a second chain, which makes
  a number gathered too small. It can also reach a declaration that the five theorems do not
  depend on, which makes a number gathered too large.
- The text of a declaration holds its statement and its proof, and the graph does not tell a
  name in the statement from a name in the proof.
- The number gathered counts declarations. It does not measure how hard a theorem is or how
  long its proof is.
- The skeleton tells which declarations the argument passes through and what lies behind each.
  It does not tell why a step holds.
- [`../explorer`](../explorer/README.md) shows the modules of the source before the merge, so
  a skeleton declaration may lie in a module that the explorer does not show or shows in
  another place.

## Running it

```bash
python3 -I verification/decl-graph/build.py      # about two minutes, 6 GB of memory
python3 -I verification/skeleton/build.py        # about 3 s with numba, 13 s without
python3 -I verification/skeleton/test_tree.py    # needs networkx
```

`verification/skeleton/build.py` takes `--min` for the number a skeleton declaration gathers at
least, 1,000 by default, and `--outline` for the same limit of `OUTLINE.txt`, 10,000 by default.

The check needs a graph built from the source that the sample was compiled from, which is
commit `9b08afdedc` of this repository. The commands below copy that commit into a folder,
which takes 1.3 GB of disk, build its graph there and run the check on it.

```bash
mkdir /tmp/before-merge
git archive 9b08afdedc src verification/decl-graph | tar -x -C /tmp/before-merge
(cd /tmp/before-merge && python3 -I verification/decl-graph/build.py)
cp verification/decl-graph/data/sample-deps.tsv.gz /tmp/before-merge/verification/decl-graph/data/
python3 -I verification/skeleton/check_sample.py /tmp/before-merge/verification/decl-graph/data
```

## Files

| File | Content |
|---|---|
| `build.py` | computes the dominator tree and writes the skeleton |
| `summary.json` | the figures of the run and the 40 largest heads |
| `skeleton.json` | the 590 skeleton declarations in `nodes`, the limit in `min` and the index of the top one in `top` |
| `OUTLINE.txt` | the skeleton declarations that gather at least 10,000, as indented lines |
| `check_sample.py` | compares the text tree with the tree of the compiled sample |
| `sample-check.json` | the figures of that comparison |
| `test_tree.py` | tests the dominator routine against networkx |
| `clean.py`, `clean.json` | the skeleton with every repeated statement counted once |
| `data/tree.npz` | the whole dominator tree as arrays, which git ignores |
| `published.py`, `published.json`, `OUTLINE-PUBLISHED.txt` | the statements that the code names as published and their marks on the skeleton, which [`PUBLISHED.md`](PUBLISHED.md) describes |
| `dossier.py`, `briefs/`, `reading.json`, `reading.py` | what each line of the outline states in plain words, which [`READING.md`](READING.md) holds |
| `glossary.py`, `glossary.json` | what the ten definitions are that the readings leave unopened most often, which [`GLOSSARY.md`](GLOSSARY.md) holds |
| `d7.py`, `d7.json` | the record `D7` with a reading of each of the 282 definitions below it, which [`D7.md`](D7.md) holds |

One entry of `nodes` in `skeleton.json` holds these fields. An index counts the entries of
`nodes` from 0.

| Field | Content |
|---|---|
| `name`, `kind`, `module` | the full name, the command and the module of the declaration |
| `parent` | the index of the skeleton declaration it hangs from, or `null` at the top |
| `gathers`, `theorems` | the number of declarations it gathers, and the number of `theorem` and `lemma` commands among them |
| `own` | the size of its own pool |
| `passes` | the share of `gathers` that the largest skeleton declaration hanging directly from it gathers |
| `depth` | its level in the dominator tree |
| `uses` | the indexes of the skeleton declarations that its text names |
| `folders` | up to four folders, each with the number of gathered declarations in it |
| `given`, `claim` | its statement, split at the first colon outside brackets, with the part before the colon in `given` and the part after it in `claim` |
