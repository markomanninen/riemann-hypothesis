# The nine steps of the strategy compared with the Numberphile interview

This report compares the nine steps of the strategy commentary in
[`README.md`](../../strategy/README.md) with a recorded interview. The video is "No-one was
close to solving The Riemann Hypothesis", on the YouTube channel Numberphile at
<https://youtu.be/FMJrEzK1wz4>. It was published on 27 November 2026 and runs 19 minutes. By the
description of the video the guest is James Maynard, a Fields medalist at the University of
Oxford. The transcript does not name the interviewer.

The text is YouTube's automatic English transcript, stored unchanged in
[`numberphile-maynard-video-transcript.srt`](numberphile-maynard-video-transcript.srt). It has
timestamps, and this report cites it by minute and second. A line that begins with `>>` is a
change of speaker. The automatic transcript garbles names. It writes Riemann as "reman" and
"rumin", Deligne as "Delene" and "Delen", Weil as "vague" and Grothendieck as "growth".

A run of the model Claude made the comparison on 28 November 2026. It read the whole transcript,
the tables of the literature search in [`SEARCH.md`](../../novelty/SEARCH.md) and the sections
of the commentary named below. It did not open the Lean text. No mathematician has checked this
report.

## Verdict for each step

The interview is about the guest's reaction, about credit and about the future of mathematics.
It does not describe the route of the proof, and it does not state the target of Step 1.

| Step | Verdict |
|---:|---|
| 1 to 9 | not covered |

Three statements of the guest concern the content of the proof as a whole.

## Statements that the repository can be compared with

- Analysis and algebra together. The guest says that the proof combines "very deep algebraic
  and arithmetic ideas coming from algebraic number theory" with "very serious analytic
  ingredients" (4:40 to 5:10). In the commentary Steps 2 and 3 are analytic, with the Landau
  argument, a count of zeros and a mean square bound, and Steps 5 to 8 are arithmetic, with
  lattices, theta lifts and slopes. The statement agrees with that division and adds no detail.
- A new proof of Deligne's work. The guest says that inside the proof there is "a actually
  remarkably simple proof" of Deligne's proof of the Weil conjectures, "using completely
  different and new ideas that are somehow much more concrete", that several mathematicians had
  tried to produce such a proof without success, and that the proof of the Riemann hypothesis
  carries that new proof over to the integers (5:20 to 7:10). The repository holds four things
  on this point, and none of them confirms the statement for the Lean text.
  - The commentary quotes the note of the author of the Lean source, which calls the argument
    "a descendant of Stepanov's". Stepanov's method proves the Riemann hypothesis for curves
    over finite fields. Deligne's theorem covers varieties of every dimension.
  - The note itself names Deligne. Entry 3 of its timeline, dated 19 October 2026, gives an
    identity q·N = M^k + R for a sum over a quadric of path shape, and the second page of the
    note calls it the "sign-only proof of Weil and Deligne" and says that with it the author
    saw that the problem "would fall". The guest's statement therefore has a source in the
    note. The note says this of the path to the proof and does not say that the Lean text
    contains that proof.
  - The literature search gives entry T1 of the note's timeline, a Stepanov-style interpolation
    determinant, the class K of results published before, and entry T3, which it compares with
    Deligne's article of 1974, the class A of a known technique in a new use.
  - The old text has a folder `src/Development/EtaleCohomology/WeilConjectures` with 16 Lean
    files and a folder `src/Development/WeilBound` with 6,798. The commentary reads neither
    folder, so this repository does not say what they prove or whether the route of the nine
    steps uses them.
- No one was close. The guest says that the proof is "much more on the extraordinary end" and
  that no one was "thinking along the same lines" (6:25 to 7:15). The literature search asks a
  different question, where each unit of the proof has a published source. Of the 20 entries of
  the note's timeline it puts 2 in class K, 14 in class A, 2 in class N, for which it found no
  source, and 2 in class U, which it could not compare. The two in class N are T10, the lower
  bound on the valuation of period values after a chain of theta lifts, and T20, the conclusion
  itself. A proof whose parts are mostly known techniques in a new use can still be far from
  what anyone was attempting, so the two findings do not contradict each other.
- The quasi-Riemann hypothesis. The guest says that the proof builds on ideas of a recent proof
  of the quasi-Riemann hypothesis (7:15 to 7:35). The World Science Festival conversation dates
  that result to late September or early October 2026
  ([`wsf-kontorovich-video-comparison.md`](wsf-kontorovich-video-comparison.md)). This
  repository holds nothing on it. The comment of the literature search on entry T14 mentions an
  "announced earlier 2/3 barrier" of the note, for which it found no derivation.
- The announcement. The guest says that at first "there was just this lean code" and no
  document for a human reader, and that a comment mentioned 250,000 pages (1:25 to 1:35, 2:20 to
  2:35). The conversation of the World Science Festival gives the same number of pages, and
  its report quotes the footnote of the note that the number comes from. The guest's account,
  that only Lean code was published, agrees with the note.
- The author. The guest says that the author of the Lean source works at Anthropic (1:10 to
  1:20), and that he "had a non-trivial input, but a huge amount of the really deep heavy
  lifting was done by AI" (8:55 to 9:05). The commentary quotes the note, in which the author
  says that Claude provided the timeline.
- A second proof. The interviewer names an incomplete proof by a human author, whom the
  transcript spells "Misulu" and "Msulo", and the guest says that the author is open that it is
  not complete (11:15 to 12:15). The World Science Festival conversation reports that the
  author's advisor thinks the proof is right. The two videos differ on this point, and this
  repository holds nothing on that paper.

## What the interview offers for explainers

- A caution on uniqueness of the new mathematics. An episode that says which part of the proof
  is new has the guest's two candidates, the new proof of Deligne's work and its transport to
  the integers. Both need a check against the Lean text before a script states them, starting
  with the two folders named above.
- The comparison with a zero-knowledge proof. A proof that is known to be correct and tells
  nothing would "be completely unsatisfying" (14:00 to 14:35). This states the purpose of a
  reading guide to a formal proof.
- The remark that reading an answer does not give understanding, and that a simple special case
  builds intuition (15:20 to 16:30).

None of these is a claim about the Lean text.
