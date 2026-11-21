# Import graph below `allChi`

`allChi` in [`Supplements/Kernels/MainTheorems.lean`](../../src/Supplements/Kernels/MainTheorems.lean)
is the statement that no Dirichlet L-function vanishes for Re s > 1/2, and the Riemann Hypothesis
follows from it by the functional equation. Its proof is the single term
`UpperTheory.FinalTheorems.everyCharacter`, which lives in the module
[`Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion`](../../src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean).
This folder holds the graph of `import` lines below that module.

The graph is built from the `import` lines at the top of each file and from nothing else. It
shows which files Lean has to load before a file, and so it gives an upper bound on what a proof
can use. Which declarations a proof really uses is a finer question, and the answer needs the built
project or its export.

## Running it

```bash
python3 -I verification/import-graph/build.py
```

The run takes about a minute and peaks at about 250 MB of memory. The script reads `src/` and
writes its results next to itself. A different root module can be given as the first argument.

## Results

| Measure | Value |
|---|---:|
| Modules in the project | 175,188 |
| Modules below `Main` | 175,187 |
| Modules below the root of `allChi` | 175,174 |
| Lines below the root of `allChi` | 17,373,677 |
| Import edges between project modules below the root | 753,544 |
| Longest import chain from the root down | 198 modules |
| Project files that import all of Mathlib (`import Mathlib`) | 155,750 |

The import graph does not shrink the problem. Only 14 modules lie outside the part below the root.
They are the root's caller `Main`, the 12 modules that take `allChi` to RH and to the critical-line
statements (`Statements`, `Supplements.Kernels.*`, `Formalism.GammaFactorNonvanishing.CritLine`
and `RhOfRight`, and six small modules in `CharacterBoxes` and `SmallClassNumbers`) and
`Challenge`, which this repository added. Every other file, and so 99.997 % of the lines, has to
be loaded before `everyCharacter` can be stated.

The root module is 14 lines long and is readable as it stands. It proves `everyCharacter` from
three results:

- `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin`,
- `UpperTheory.Zero.LLC.recTExists`, a statement about the local Langlands correspondence,
- `UpperTheory.One.vwin_of_row` applied to `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`.

Each of the root's five imports already pulls in a large share of the project:

| Import of the root | Modules below it |
|---|---:|
| `…ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow` | 157,604 |
| `…ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin` | 151,286 |
| `…CharacterBoxes.RiemannHypothesisOfEveryCharacter` | 102,080 |
| `…Foundations.GaloisRepresentations.IntegralStructures.RowSrc` | 66,168 |
| `…Foundations.LocalLanglands.LocalCentralUnits.RecTExists` | 26,673 |

The five subgraphs overlap almost entirely, so the import graph offers no small branch that could
be read on its own. The next step towards a readable proof is the declaration graph. It lists, for
`everyCharacter` and the three results above, the declarations their proof terms really mention,
and it can be built from `solution.export` once the Comparator run has produced it.

`groups.tsv` sums the files and lines by the first two parts of the module name. The largest group
is `Development.AbelianVarietyTheory`, with 99,187 files and 8.1 million lines. Together with
`Development.AutomorphicArithmetic` and `Development.AutomorphicSpectrum` it holds about two thirds
of the source.

## Files

| File | Content |
|---|---|
| `build.py` | the script |
| `summary.json` | the figures above, the outside imports by count and the 25 most imported modules |
| `groups.tsv` | files and lines per group of modules, all of them and those below the root |
| `groups.dot` | the graph between groups, in Graphviz format, with the number of import lines on each edge |
| `modules.tsv.gz` | one row per module with its lines, its imports, how often it is imported below the root and the length of its longest import chain |
| `edges.tsv.gz` | every import line of every module below the root |

`groups.dot` has 1,232 edges, so a drawing of it is dense. `dot -Tsvg groups.dot -o groups.svg`
draws it where Graphviz is installed, and the script draws it on its own when `dot` is on the path.
