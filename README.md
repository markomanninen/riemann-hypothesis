# Proof explorer, built for the browser

This branch holds a built copy of `verification/explorer` from the branch `main`, at commit
`78aeec4565`, together with the data that its build scripts make from the Lean code after the
merge of upstream main on 2026-11-22. GitHub
Pages serves it at <https://markomanninen.github.io/riemann-hypothesis/>.

The landscape draws every file of the code as a dot. A dot's height is the number of files in the
longest chain of imports below it. Selecting a file shows the files it rests on, the files built on
it, and its statements. The Argument tab shows the largest steps of the proof with what each
theorem states, as a language model read it from the Lean text. The source of the page and the scripts that build the data are in
[`verification/explorer`](https://github.com/markomanninen/riemann-hypothesis/tree/main/verification/explorer)
on `main`, and its README describes how to build the data again.
