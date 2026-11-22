# Proof spine explorer

`index.html` shows the modules below `allChi` in two views.

The landscape draws every module as a dot. A dot's place on the ground comes from a circle
packing of the source folders, where a module's circle has its line count as area and a folder's
ring encloses its modules and subfolders. A dot's height is the number of modules in the longest
chain of imports below it. The Map button flattens the dots onto the ground. Selecting a module
colours every module it rests on and every module built on it, and selecting a ring shows that
folder alone.

The page writes module and folder names as words, so `DivisorProofs` reads Divisor Proofs. The
search finds a name with or without the spaces between its words.

Under a selected module, both views list the module's statements. A statement is a declaration as
the Lean source writes it, with the proof left out. A theorem's statement is split into what is
given and what is claimed, a definition also shows its value, and the `variable` lines in scope
stand above the statements that may use them.

The branches view walks the dominator tree of the import graph. A module sits under the nearest
module that every chain of imports from the root to it passes through, so a branch holds the
modules that only its top module needs.

The landscape also plays tours. A tour is a camera run described in a file under `tours/`, such
as a run down the longest chain of imports, seen from outside or from the chain itself. The
Follow chain button plays one in the page, and `record_tour.py` renders one into an MP4 clip for
a video. [ANIMATIONS.md](ANIMATIONS.md) tells how to write a tour and how to record it.

Both views are built from import lines, as in [`../import-graph`](../import-graph/README.md).
They are the module-level prototype. The declaration graph from the Comparator export will
replace the modules with the declarations the proof terms really use.

## Building and viewing it

```bash
python3 -I verification/import-graph/build.py        # if the import graph is missing
python3 -I verification/explorer/build_data.py       # about two minutes, 0.6 GB of memory
python3 -I verification/explorer/build_mountain.py   # about half a minute
python3 -I verification/explorer/build_statements.py # about ten seconds on an Apple M4 Pro
cd verification/explorer && python3 -I -m http.server 8811 --bind 127.0.0.1
```

The scripts write `data/`, which git ignores. `build_data.py` numbers the modules in preorder of
the dominator tree and writes the tree in chunks of 4,000 modules. `build_mountain.py` computes
the map and writes the positions, heights and import lists as gzip in base64 text, 3.3 MB, and
the name index the same way, 2.3 MB. `build_statements.py` reads every source file and writes
the statements of 500 modules per file, 351 files and 93 MB in all, packed the same way. The page
draws the landscape with WebGL in `mountain.js` and loads a tree chunk or a statement file only
when it shows a module from it. `tour.js` plays the tours.

`build_statements.py` works on the text and does not run Lean. It ends a theorem's statement at
the first `:=` outside brackets and splits it at the first colon outside brackets, so a rare
layout can place a split wrongly. With module names as arguments the script prints the statements
of those modules, which shows how a given file was read.

## Figures from the first build

| Measure | Value |
|---|---:|
| Modules | 175,174 |
| Source folders, each a ring on the map | 3,610 |
| Longest chain of imports | 199 modules |
| Modules at heights 0 to 39, the lowest fifth | 86,613 |
| Declarations with a statement | 1,061,375 |
| Theorems and lemmas among them | 818,718 |
| Claims longer than the limit of 3,000 characters, shown shortened | 427 |
| Modules without a declaration | 172 |
| Direct children of the root in the dominator tree | 47,029 |
| Depth of the dominator tree | 34 |
| Share of lines in the root's 14 largest branches | 23.1 % |

In the dominator tree, 76.9 % of the lines sit directly under the root. These are modules that
several branches reach by separate routes, so no single branch owns them. The largest branches
are `RowSrc` with 993,261 lines, `VwinOfRow` with 771,890 and `RiemannHypothesisOfEveryCharacter`
with 728,548.
