# Proof explorer, built for the browser

This branch holds a built copy of `verification/explorer` from the branch `main`, at commit
`05f729f3c`, together with the data that its build scripts make from the published Lean code. GitHub
Pages serves it at <https://markomanninen.github.io/riemann-hypothesis/>.

The landscape draws every file of the code as a dot. A dot's height is the number of files in the
longest chain of imports below it. Selecting a file shows the files it rests on, the files built on
it, and its statements. The source of the page and the scripts that build the data are in
[`verification/explorer`](https://github.com/markomanninen/riemann-hypothesis/tree/main/verification/explorer)
on `main`, and its README describes how to build the data again.
