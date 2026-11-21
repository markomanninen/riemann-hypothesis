# Proof spine explorer

`index.html` is a browser view of the dominator tree of the import graph below `allChi`. A module
sits under the nearest module that every chain of imports from the root to it passes through. A
branch then holds the modules that only its top module needs, and the page shows how many lines
each branch holds, which modules it imports and which modules import it.

The tree is built from import lines, as in [`../import-graph`](../import-graph/README.md). It is
the module-level prototype. The declaration graph from the Comparator export will replace the
modules with the declarations the proof terms really use.

## Building and viewing it

```bash
python3 -I verification/import-graph/build.py      # if the import graph is missing
python3 -I verification/explorer/build_data.py     # about two minutes, 0.6 GB of memory
cd verification/explorer && python3 -I -m http.server 8811 --bind 127.0.0.1
```

`build_data.py` writes `data/`, which git ignores. It holds 34 MB in 46 files. The page loads
`meta.json` and the name index `names.json` at the start and each 4,000-module chunk only when it
shows a module from it.

## Figures from the first build

| Measure | Value |
|---|---:|
| Modules in the tree | 175,174 |
| Direct children of the root | 47,029 |
| Depth of the tree | 34 |
| Branches of at least 1,000 modules | 43 |
| Share of lines in the root's 14 largest branches | 23.1 % |

Most of the source, 76.9 % of the lines, sits directly under the root. These are modules that
several branches reach by separate routes, so no single branch owns them. The largest branches
are `RowSrc` with 993,261 lines, `VwinOfRow` with 771,890 and `RiemannHypothesisOfEveryCharacter`
with 728,548.
