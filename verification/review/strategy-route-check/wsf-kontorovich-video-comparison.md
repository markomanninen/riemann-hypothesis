# The nine steps of the strategy compared with the World Science Festival conversation

This report compares the nine steps of the strategy commentary in
[`README.md`](../../strategy/README.md) with a recorded conversation. The video is "AI Summits
The Mount Everest Of Math", on the YouTube channel of the World Science Festival at
<https://youtu.be/VHsi0G2g4GY>. It was published on 28 November 2026 and runs 40 minutes. By the
description of the video Brian Greene speaks with Alex Kontorovich, professor of mathematics at
Rutgers University. The description links the four-page note of the author of the Lean source,
which the commentary calls the note.

The text is YouTube's automatic English transcript, stored unchanged in
[`wsf-kontorovich-video-transcript.srt`](wsf-kontorovich-video-transcript.srt). It has
timestamps, and this report cites it by minute and second. A line that begins with `>>` is a
change of speaker. The automatic transcript garbles names. It writes the author of the Lean
source as "El iezer", "Levitan", "Alpog" and "Leontyne Applegate".

A run of the model Claude made the comparison on 28 November 2026. It read the whole transcript
and did not open the Lean text. No mathematician has checked this report.

## Verdict for each step

The conversation is about the history of the problem and about what the result means for
mathematics. It does not describe the route of the proof.

| Step | Verdict | Where in the transcript |
|---:|---|---|
| 1 | the target only, for the zeta function | 5:15 to 5:55, 10:10 to 10:45 |
| 2 to 9 | not covered | |

The one sentence on the content of the proof says that it uses "basically the entire … Langlands
program", topology, geometry and analysis (24:50 to 25:10). The commentary places the Langlands
side in the supply branch `Row`. The conversation names no object of Steps 2 to 9, such as the
prime sum, the auxiliary field, the lattice, the theta lifts or the number m.

## Statements that the repository can be compared with

- Size. The conversation gives "about 17 million lines of code" for the Lean text and "a
  quarter of a million pages" for a text in natural language that came before it (1:00 to 1:15,
  3:10 to 3:20). Robin Zhang's talk gives the same 17 million
  ([`zhang-video-comparison.md`](zhang-video-comparison.md)). The commentary counts 149,098 Lean
  files in the old text and does not count lines, and this report did not count them. The text
  in natural language is not in this repository.
- Checking. The guest says that the proof was "within hours certified as a correct complete
  proof" and "checked in a thousand different ways", and that its correctness is "not … in
  doubt" among the people he talks to (20:20 to 21:35). The [README](../../../README.md) of this
  repository describes the check `lake comparator` and, by the commentary, records no complete
  run of it on the source of this fork. The two statements are about different runs, and this
  repository holds no record of the runs that the guest means.
- Understanding. The guest says that no human understands the proof and that the author says so
  himself (21:55 to 22:20). The commentary quotes the note to the same effect.
- A second proof. The conversation reports a paper of about 940 or 960 pages by a student of
  Brian Conrad at Stanford, released on the same day and written without AI, and says that
  efforts to formalise it are under way (25:20 to 28:35). The transcript spells the author
  "Alessandro Massolo" and "Massulo". Zhang's talk mentions "the Mazur proof" (line 3367 of its
  transcript), which may be the same paper. The automatic transcripts do not fix the name, and
  this repository holds nothing on that paper.
- Earlier results of 2026. The conversation names a result of August that two thirds of the
  zeros lie on the critical line, and a result of late September or early October that the
  zeta function has no zero with real part above 7/8 (13:20 to 17:10). The guest says that the
  first makes no progress towards the Riemann hypothesis, because a share of 100 % of the zeros
  in the limit leaves room for zeros off the line (14:05 to 16:00). This repository holds
  nothing on either result.
- The date of the note. The guest says that the note was posted "on Friday" (2:45, 17:35).
  The commentary dates the old text to 22 November 2026, which was a Sunday. The note and the
  Lean text may have been posted on different days, and this report did not check it.

## What the conversation offers for explainers

- The history from Euclid and Gauss through Riemann in 1859, the prime number theorem of 1896,
  Hilbert in 1900, Hardy in 1914, Selberg, Levinson and Conrey to the Clay problems of 2000
  (8:40 to 12:30). Each date is the guest's statement and needs a source of its own before a
  script uses it.
- Two formulations for a general audience. The Riemann hypothesis says that the main term of
  Gauss gives the first half of the digits of the number of primes (4:55 to 5:05), and a
  zero-free strip above 7/8 gives the first eighth (17:00 to 17:10).
- The example of the perfect squares for the difference between 100 % in the limit and all
  (14:25 to 14:50).
- The picture of the formal proof as a compass that points the way without giving
  understanding (24:15 to 25:20).

None of these is a claim about the Lean text.
