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

The branches view walks the dominator tree of the import graph. A module sits under the nearest
module that every chain of imports from the root to it passes through, so a branch holds the
modules that only its top module needs.

Both views are built from import lines, as in [`../import-graph`](../import-graph/README.md).
They are the module-level prototype. The declaration graph from the Comparator export will
replace the modules with the declarations the proof terms really use.

## Building and viewing it

```bash
python3 -I verification/import-graph/build.py        # if the import graph is missing
python3 -I verification/explorer/build_data.py       # about two minutes, 0.6 GB of memory
python3 -I verification/explorer/build_mountain.py   # about half a minute
cd verification/explorer && python3 -I -m http.server 8811 --bind 127.0.0.1
```

The scripts write `data/`, which git ignores. `build_data.py` numbers the modules in preorder of
the dominator tree and writes the tree in chunks of 4,000 modules. `build_mountain.py` computes
the map and writes the positions, heights and import lists as gzip in base64 text, 3.3 MB, and
the name index the same way, 2.3 MB. The page draws the landscape with WebGL in `mountain.js`
and loads a tree chunk only when it shows a module from it.

## Figures from the first build

| Measure | Value |
|---|---:|
| Modules | 175,174 |
| Source folders, each a ring on the map | 3,610 |
| Longest chain of imports | 199 modules |
| Modules at heights 0 to 39, the lowest fifth | 86,613 |
| Direct children of the root in the dominator tree | 47,029 |
| Depth of the dominator tree | 34 |
| Share of lines in the root's 14 largest branches | 23.1 % |

In the dominator tree, 76.9 % of the lines sit directly under the root. These are modules that
several branches reach by separate routes, so no single branch owns them. The largest branches
are `RowSrc` with 993,261 lines, `VwinOfRow` with 771,890 and `RiemannHypothesisOfEveryCharacter`
with 728,548.
