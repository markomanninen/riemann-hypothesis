# State of upstream main on 28 November 2026

Upstream is the repository `leanprover-community/riemann-hypothesis`, which holds a Lean
formalisation of a proof of the Riemann hypothesis and of the generalized Riemann hypothesis for
Dirichlet L-functions. This fork follows it under the git remote name `upstream`. On 25 November
2026 upstream replaced the whole history of its branch `main` with a condensed edition of the
proof, and the community has been cleaning that edition up since then. An open issue reports that
upstream main has failed the check that upstream's README gives for the whole proof since 26
November, and the proposed fix was still unmerged when this note was written. This note records
where upstream main stood on 28 November 2026, when its head was the commit 38dc5337b92.

A language model, Claude, read the state from git and from GitHub between 10:24 and 10:50 UTC on
that day. Lean was not run and nothing was built. The last section names the commands behind the
figures.

## The change of 25 November

Until 25 November upstream main held the version of the proof that Levent Alpöge released, together
with the cleanups the community had made to it. This note calls that line of commits the old text.
This fork merged the old text on 22 November at upstream commit 611ce0b6301, and the source in
[`src`](../src) of this fork is still that commit.

Upstream main now starts from the commit 72fead102f6, which Luke Sernau made on 25 November in the
repository `lsernau/grh-lean`. That commit holds a condensed form of the proof in two folders, a
readable edition `grh` and a compact edition `grh-compact`. Upstream kept the readable edition and
moved it to the repository root. This note calls the result the new edition.

| Measure | Old text at 611ce0b6301 | New edition at 38dc5337b92 |
| --- | ---: | ---: |
| Lean files in `src` | 149,098 | 802 |
| Lines in the Lean files of `src` | 15,175,546 | 479,304 |
| Lean version | 4.36.0 | 4.37.0-rc1 |

The new edition divides `src` into two folders beside `Main.lean` and `Statements.lean`. The folder
`src/Lib` has 495 files of background results, and the folder `src/New` has 305 files that hold the
argument. `src/Main.lean` states five theorems with the same names as in the old text, and its
theorem `riemannHypothesis` is the term `New.zeta_zeros_on_line New.grh`.

The old text continues on the upstream branch `alpoge`. That branch ends at the commit 0ca81d6329f
of 26 November, which lies 9,235 commits after 611ce0b6301 and has 58,726 Lean files in `src`. The
upstream branch `original` keeps Alpöge's release as upstream retrieved it on 20 November, without
the community's cleanups.

## Work on the new edition

Upstream brings most changes to main in batches. A batch is a pull request that collects pull
requests a reviewer has approved and merges them into main in one step. Up to the head commit, main
had received 56 batches and 15 pull requests merged one by one. Fifty of the batches carry numbers
from m1 to m52, with m5 and m7 absent, and the other six carry the names ci-8789, ct1, fx1, rb1,
tc1 and tc2. The merge commits inside the batches name 2,266 pull requests.

The next table counts the commits that arrived on main on each day in UTC. A merge counts with
every commit it brought.

| Day in UTC | Commits that arrived on main |
| --- | ---: |
| 25 November | 24 |
| 26 November | 4,897 |
| 27 November | 54 |
| 28 November until 10:24 | 13 |

The four days add up to the 4,988 commits of upstream main. New pull requests kept arriving after
26 November. GitHub's search counted 821 pull requests opened and 31 merged between 27 November
00:00 UTC and 28 November 10:39 UTC.

Of the 4,988 commits, 2,547 are changes and the other 2,441 are merges. The merges are of three
kinds. 71 lie on main itself, the 56 batches and the 15 single pull requests. 2,268 merge a pull
request into a batch, and they name the 2,266 different pull requests counted above. The other 102
lie inside the branches of pull requests, and 90 of them name main or upstream in their titles, as
a merge that brings main into the branch does.

Most titles of the 2,547 changes follow the convention of Mathlib, the community library of
mathematics for Lean, in which a prefix names the kind of change. 1,808 titles begin with
`refactor`, 235 with `perf`, 205 with `style`, 69 with `doc` or `docs`, 65 with `chore` and 32 with
`ci`. These six prefixes cover 2,414 of the 2,547 titles. The other 133 titles carry another
prefix, such as `rebase` or `fix`, or begin with a plain verb such as Share or Use.

A sample of 43 titles, every sixtieth in the order of `git log` from the newest title on, shows
four recurring kinds of change. One kind proves once, as a lemma, an argument that appeared several
times. A second kind removes declarations that nothing uses. A third kind clears linter warnings,
and a fourth speeds up slow proofs.

The size of the source stayed nearly the same through these changes. The Lean files of the readable
edition lay under `grh/src` at the root commit and had 477,124 lines there. At the head they lie
under `src` and have 479,304 lines. A diff between the two folders changes 791 files, removes 12
and adds 11, with 47,942 lines added and 45,762 lines removed.

Three further changes concern the tools and the rules of the work:

- The root commit used Lean 4.35.0. Pull request #5769 moved upstream main to Lean 4.37.0-rc1 on 26
  November, and pull request #5768 of the same day turned the source files into Lean modules, which
  are files that carry the line `module`. 801 of the 802 Lean files in `src` carry that line.
- Upstream main now depends on Tau Ceti, the Lean library at `github.com/TauCetiProject/TauCeti`,
  pinned at its commit 2a9233e5 of 27 November. 294 files of `src` import Tau Ceti directly, and
  220 open pull requests carry the label `tauceti-refactor`.
- On 26 November upstream added `AGENTS.md`, its instructions for coding agents. The file names the
  aim as a proof that people can read. It lists the changes upstream wants, among them the use of a
  result from Mathlib or Tau Ceti in place of a proof of the same result in the upstream
  repository. It turns away changes that make the code shorter or faster but harder to read, such
  as inlining a lemma into its only caller.

## Open matters

### The kernel replay of main

Issue #7560 reports that upstream main fails `lake comparator`. Upstream's README describes `lake
comparator` as the check that `Main.lean` proves exactly the five statements that
`src/Statements.lean` holds, that it uses only the axioms `propext`, `Quot.sound` and
`Classical.choice`, and that Lean's kernel and the independent checker nanoda accept the proof. For
the last part the tool exports the proof terms of `Main` and gives them to the kernel again, and
this note calls that step the kernel replay.

The issue says that the kernel replay has rejected main since pull request #5768, the change that
turned the source files into Lean modules, and that the error is `deep recursion detected`. The
issue explains the failure as follows. The rejected proofs use the tactic `grind` on real numbers
with large numerals. A proof inside a module sees only the part of Mathlib's real arithmetic that
Mathlib exposes, and this note calls that the module view. The `grind` proofs pass in the module
view. The kernel replay checks each proof with all definitions visible, which this note calls the
full view, and in the full view the kernel exceeds its recursion limit. Pull request #5769, the
upgrade to Lean 4.37.0-rc1, reached main first, at 02:11 UTC on 26 November, and replaced these
`grind` proofs with a macro named `scale_arith`. Pull request #5768 reached main at 03:39 UTC and
took the macro out again. According to the issue, upstream's CI builds the files in the module view
and leaves the kernel replay out, so the build passes while the replay fails.

A commenter on the issue checked each declaration of main at the commit 8c828eda of 27 November in
the full view and found 362 of 60,851 declarations rejected, in 62 modules under `src/New`. The
proposed fix is pull request #8358, which restores `scale_arith` and was open at 10:42 UTC on 28
November. The same commenter merged #8358 into 8c828eda as a test and found none of 59,099
declarations rejected. The test merge thus held 1,752 fewer declarations than 8c828eda. The author
of #8358 measured a fall of 2,042 declarations on an earlier commit and explains the fall by
auxiliary proofs that `grind` generates and that are gone after the fix. Another commenter reported
on 28 November that Lean's `leanchecker` accepted the full export of that test merge.

Two merges reached main after 8c828eda, the later of which is the head 38dc5337b92, and #8358 is in
neither. The comments read for this note end before the later of the two merges, so none of them
measures the present head. This fork has run none of these checks.

### The queue of pull requests

GitHub showed 1,416 open pull requests at 10:50 UTC and 33 open issues at 10:39 UTC. A count by
label was read between 10:26 and 10:28 UTC, when GitHub's search counted 1,394 open pull requests.
It gave 265 pull requests with the label `inbox`, 33 with `approved`, 57 with `awaiting-author` and
220 with `tauceti-refactor`. At most 355 of the 1,394 carried one of the first three labels, so at
least 1,039 carried none of them. `AGENTS.md` explains one of the labels, `awaiting-author`, which
a reviewer sets when handing a pull request back to its author. By size label, 391 pull requests
were `extra_small`, 830 `small`, 164 `medium` and 4 `large` or `extra_large`. These four counts add
up to 1,389, five fewer than the 1,394 pull requests counted two minutes before.

### Other open issues

The titles of all 33 open issues were read. Most of the titles concern build speed, duplicated
declarations and tooling. Three further matters bear on the proof or on how it is checked:

- Issue #8343 reports that two pull requests which changed import lines also changed the terms that
  Lean builds for some intermediate statements and definitions, and that Lean raised no error. The
  issue counts 80 such declarations in pull request #6788 and 114 in pull request #7455, and both
  pull requests are in upstream main. The issue says that none of the changed declarations is in
  `Main.lean` or `Statements.lean`.
- Issue #9222 asks for a documented answer to a paper by J. L. Nielsen at `philarchive.org`.
  According to the issue the paper argues that the proof depends on heights built from functions
  that assume the Riemann hypothesis. The issue had one comment and no answer when this note was
  written.
- Issues #8738 and #8747 announce in their titles independent checks of the commit 72fead102f6.
  This note has read only the two titles.

## Which source the work in this fork studies

The checks and readings in this folder, `verification`, study the source in [`src`](../src) of this
fork, which is the old text at 611ce0b6301. The main branch of this fork and upstream main share no
commit.

One of the readings is the strategy commentary in [`strategy/README.md`](strategy/README.md), which
describes the proof in nine steps. The report
[`new-edition-comparison.md`](review/strategy-route-check/new-edition-comparison.md) places those
nine steps on the new edition as it stood at the commit 7c4ccbd64d0 of 27 November. Three merges
with 16 commits reached upstream main after 7c4ccbd64d0, the first of them 8c828eda. In `src` the
three merges remove 132 lines in 56 files and add none.

The strategy commentary has read none of the 9,235 commits that the branch `alpoge` has after
611ce0b6301.

## How the figures were read

The figures come from three kinds of reading:

- The git figures describe upstream main after `git fetch upstream main` at 10:24 UTC. The figures
  for the branch `alpoge` come from the copy that an earlier fetch stored in this checkout, and the
  head of that copy matched `git ls-remote upstream` at the time of reading. Counts of commits,
  merges and files come from `git rev-list --count`, `git log --first-parent`, `git ls-tree -r` and
  `git diff --shortstat`. Line counts come from `git archive` of the folder, passed through `tar
  -xO` and `wc -l`. The prefix counts and the sample of titles come from `git log --no-merges
  --pretty=%s`, the counts of files that import Tau Ceti and of files with the line `module` from
  `git grep -l`, the Lean versions from the file `lean-toolchain` of each commit, and the pin of
  Tau Ceti from `lakefile.toml`. The presence of pull requests #6788 and #7455 in upstream main
  comes from the titles of `git log --merges`.
- The counts of pull requests and issues come from GitHub's search through `gh api search/issues`,
  with the qualifiers `is:open`, `is:merged`, `label`, `created` and `merged`.
- The contents of issues #7560, #8343 and #9222 come from `gh issue view`, the titles of issues
  #8738 and #8747 from `gh issue list`, and the titles and states of pull requests #5768, #5769 and
  #8358 from `gh pr view`.
