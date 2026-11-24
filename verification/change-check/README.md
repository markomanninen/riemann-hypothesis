# Checking a change to the proof

[`check_change.py`](check_change.py) tells a contributor what a change to the source does to
the five theorems of [`Main.lean`](../../src/Main.lean). `riemannHypothesis` states Mathlib's
`RiemannHypothesis` and `riemannZeta_eq_zero_re` the same written out.
`LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re` and
`LFunction_eq_zero_re_of_isPrimitive` state three claims about the zeros of Dirichlet
L-functions, as the [README of the repository](../../README.md#what-is-claimed) lists them. A change leaves the five theorems proved as before when all three of these points
hold.

1. Lean still compiles every module that the change touches and every module that imports a
   touched module, directly or through other modules, and that `Main.lean` imports. Lean's kernel checks each proof while it
   compiles a module, and Lake compiles those modules again after a change, so a passing build
   means that the kernel accepted every changed proof and every proof that depends on one.
2. The five theorems still state what they stated. Their statements are written in `Main.lean`
   and [`Statements.lean`](../../src/Statements.lean) with definitions of Mathlib, whose version
   the files `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` pin.
   [`Challenge.lean`](../../src/Challenge.lean) states the same five theorems with `sorry`, in a
   file that imports only Mathlib, as the reference to compare with.
3. The five theorems still rest on no axiom other than `propext`, `Classical.choice` and
   `Quot.sound`. A `sorry` or a new `axiom` in any module that they import would add a fourth.

The commands `build` and `axioms` of the script check the first and the third point. For the
second, the command `plan` warns when the change touches one of the files that point 2 names.
`lake comparator`, as the README of the repository describes under
[Checking the proof](../../README.md#checking-the-proof), checks the second and the third point
completely against `Challenge.lean`, where the script only warns about the second.

The script needs git and Python 3, and for the build also Lean's `lake`, which elan installs
with the toolchain that `lean-toolchain` names. Checking a pull request
needs the GitHub command `gh` as well. Run every command from the root of a checkout of this
repository.

## What a build is here

The project has 149,397 modules, and `Main.lean` imports 149,284 of them, directly or through
other modules. Compiling a module means that Lean elaborates its source, checks every proof
with its kernel and writes the result to compiled files under `.lake/build`. A build from
scratch, without downloaded files, takes 7 to 10 hours on a machine with 48 cores and 503 GB of
memory, as [`NOTES.md`](../NOTES.md) records. `lake exe cache get` downloads the compiled files
for the checked-out commit in place of that build. After a change Lake compiles only the modules
whose source, or the source of a module they import, differs from that commit. Volunteers'
machines built the downloaded files, partly from pull requests that nobody had reviewed, and
the download checks only that the files are the ones that were uploaded. The files therefore
make a build fast and are no evidence that the proof holds.

How much a change costs depends on how many modules import the changed module, directly or
through others. In a sample of 400 modules of the import graph in
[`../import-graph`](../import-graph/README.md), a change of one module made Lake compile 76
modules again at the median. For the tenth of modules with the largest effect it was more
than 9,229, for the hundredth with the largest effect more than 44,070, and at most 72,406. A
change in the module `TopShapeAlt`, which defines the statement `TopShapeAlt` that the theorem
`UpperTheory.Top.shape_closed_link_n_of_green` proves, makes Lake compile 9 modules, far fewer
than the median.

Before Lake compiles anything, it reads the trace file of every module that the build targets
import. A trace file lies beside the compiled files of a module and records the hashes of its
source and of its imports, so Lake sees from it which modules are up to date. Even a small change costs this reading. In a test
on a Mac whose compiled files lay in a disk image on an external drive, `lake build --no-build`
of `TopShapeAlt` read the traces of the 45,839 modules that `TopShapeAlt` imports, directly or
through other modules, in 54 minutes, almost all of it waiting for the disk. The axiom check
loads the compiled files of every module that `Main.lean` imports, and its `import Main` had
not finished after two hours on the
same disk. Keep the compiled files on a fast internal disk. On that Mac a test of the script
applied a patch that adds the false theorem `2 + 2 = 5` with the proof `rfl` to `TopShapeAlt`.
The build failed after 36 minutes with Lean's message that the two sides are not
definitionally equal, and the script ended with exit code 1.

## Use

### Plan, without a build

```bash
python3 -I verification/change-check/check_change.py plan              # change against HEAD
python3 -I verification/change-check/check_change.py plan --base main  # change against main
python3 -I verification/change-check/check_change.py plan --what-if src/Statements.lean
```

The change is the difference between a commit, HEAD unless `--base` names another, and the
working tree, untracked new files included. The plan lists the changed files and reads the
`import` lines of every source file of the working tree, which takes a few seconds to a minute.
From those imports it counts the modules that Lake has to compile again and how many of them
`Main.lean` imports. A change that reaches no module that `Main.lean` imports cannot affect the
five theorems, as long as the plan read every import, as the limits below describe.
`--what-if FILE` counts as if the named files had changed, so the checkout can stay as it is.

The plan ends with one of these exit codes.

- 0 when it found nothing to warn about.
- 1 when a module still imports a module that the change deletes, which would break the build.
- 2 when the change touches `Main.lean`, `Statements.lean`, `Challenge.lean`, `lakefile.toml`,
  `lake-manifest.json` or `lean-toolchain`. A passing build then no longer shows that the same
  claim is proved, so run `lake comparator` before relying on the change.

### Build and axioms

The build needs a second checkout, at the commit that the change starts from, with its compiled
files downloaded. The commands below make one in `~/rh-build`. `git merge-base HEAD main`, run
in the checkout that holds the change, prints that commit when the change starts from main.

```bash
git clone https://github.com/leanprover-community/riemann-hypothesis.git ~/rh-build
cd ~/rh-build && git checkout <the commit that the change starts from>
lake exe cache get
lake build --no-build     # exits with an error if any module still needs compiling
```

If the last command exits with an error, run `lake build` there once, which compiles the
missing modules.

Then run the build from the checkout that holds the change.

```bash
python3 -I verification/change-check/check_change.py build --project ~/rh-build
```

The script refuses to run when the `src` folder of `~/rh-build` differs from that of the commit
that the change starts from, which is HEAD or the commit that `--base` names, or when
`~/rh-build` has uncommitted changes in `src` or in the build files. It runs the plan and
stops before changing anything when the plan ends with exit code 1. Otherwise it applies the change to `~/rh-build` and runs `lake build Main` there. That compiles the
changed modules and every module that both imports a changed module and is imported by
`Main.lean`. It then runs `#print axioms` on the five theorems `riemannHypothesis`,
`riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re` and
`LFunction_eq_zero_re_of_isPrimitive`, and prints the axioms of each. The build ends with exit
code 0 when the build and the axiom check pass, 1 when either fails and 2 when both pass but
the plan warned about the statements. `--all` runs `lake build` in place of `lake build Main`.
The full build also compiles the 113 modules that `Main.lean` does not import.

The change stays applied in `~/rh-build`, and the script prints the command that removes it.
After that removal, the next build compiles the changed modules again, so that the compiled
files match the original source again.

A pull request can be checked without applying its change to your own checkout. `gh pr diff`
prints the change of a pull request as a patch. `--patch FILE` applies that patch to
`~/rh-build` in place of the working-tree change, so the command can run from any checkout of
this repository. With `--patch` the script cannot know the commit that the pull request starts from, so it
checks only that the patch applies to `~/rh-build`. Check out there the commit that the pull
request starts from, which `gh pr view 123 --json baseRefOid` prints, and run the command from
a checkout at the same commit, because the plan reads the imports of the checkout it runs in.

```bash
gh pr diff 123 --repo leanprover-community/riemann-hypothesis > pr123.patch
python3 -I verification/change-check/check_change.py build --project ~/rh-build --patch pr123.patch
```

`--target MODULE ...` builds only the named modules in place of `Main.lean` and skips the axiom
check. A module is named as Lean names it, for example
`Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShapeAlt`.
A pass then shows only that those modules compile, so it serves for a quick first look and is
no check of the five theorems.

`axioms` runs the axiom check alone, on a checkout in which `lake build Main` has passed.

```bash
python3 -I verification/change-check/check_change.py axioms --project ~/rh-build
```

## Limits

- The plan reads `import` lines from the source text, before the first command of a file and
  outside comments. An import that a file wrote in another way, for example after a command
  that the plan takes for the end of the imports, would be missed, and the plan would count too few modules and could say wrongly that the
  change reaches nothing that `Main.lean` imports. The build reads the imports through Lake and
  compiles every module that it has to.
- The script does not check that the statements of the five theorems are unchanged. It warns
  when the files that fix them change, and `lake comparator` checks them against
  `Challenge.lean`.
- The build trusts the downloaded compiled files of every module that it does not compile.
- With `--patch` the plan counts the modules from the imports of the checkout that the command
  runs in, before the patch, so an import that the patch adds or removes is not counted.
