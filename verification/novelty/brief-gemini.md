# Brief for the literature search on what is new in the proof

You are comparing the steps of a proof with the published literature. The proof is a Lean 4
formalisation that claims the Riemann hypothesis and its form for Dirichlet L-functions, and
its author announced it on 20 November 2026. Your task is to say for each step whether its
mathematics was published before that date, and where.

## What you read

- `verification/novelty/units.json` holds the units in twelve batches. A unit of the kind
  `claim` is one row of `verification/strategy/CLAIMS.md`. Its field `states` says what the
  Lean text states, and `declarations` names the Lean declarations. A unit of the kind
  `timeline` is one entry of the timeline in the author's note, with a paraphrase.
- `verification/strategy/CLAIMS.md` and `verification/strategy/README.md` explain every claim.
  Read the section of a step before you judge its units.
- The author's note is at <https://alpo.ge/remark.pdf>. Read its timeline on pages 3 and 4
  before the two timeline batches.
- The Lean source under `src/` settles what a declaration states. Open a declaration when a
  row leaves you unsure what is claimed.
- The published literature, which you search on the web. Use the original papers, standard
  textbooks and monographs, and the arXiv. Use a survey or an encyclopedia page to find them.

## What you write

Write one file for each batch, `verification/review/gemini-novelty/<batch>.json`, where
`<batch>` is the name of the batch in `units.json`, such as `claims05` or `timeline01`. Write
only into that folder. Each file holds one JSON array with one object for each unit of the
batch, in the order of the batch.

```
{
 "id": the id of the unit, such as "5.3" or "T12",
 "technique": one or two sentences that name the mathematical result or technique of the unit
              in the terms of the literature,
 "class": "K", "A", "N", "G" or "U", as defined below,
 "nearest": a list of up to three sources, nearest first, each an object
   {"citation": authors, title, journal or publisher, year,
    "url": the address that you opened,
    "locator": the theorem, section or page of the source,
    "says": one sentence on what the source states at that place,
    "quote": at most 25 words copied from the source at that place},
 "difference": one to three sentences on what differs between the unit and the nearest
               source, in the object, the generality, the hypotheses or the constants,
 "searches": the search phrases that you used for this unit,
 "confidence": "high", "medium" or "low",
 "why": one sentence that gives the reason for that confidence,
 "specialist": one sentence on what a specialist should check first
}
```

The classes are these.

- K, a known result. A source published before 20 November 2026 states the result of the
  unit, up to notation.
- A, a known technique in a new place. A source published before that date has the technique,
  and the unit applies it to another object, in another range or in a new combination. The
  field `difference` says which.
- N, no precedent found. Your searches found no source that states the result or uses the
  technique. The field `searches` then holds at least four phrases, and `nearest` holds the
  closest source that you did find.
- G, glue. The unit is bookkeeping of the proof, such as a split into cases or the passing of
  premises, and carries no mathematical technique of its own.
- U, undecided. The unit is written in the vocabulary of the project to a degree that leaves
  no statement to compare with the literature. The field `why` says what would have to be
  opened first.

When all twelve files are written, write `verification/review/gemini-novelty/synthesis.json`
with one object that has these fields.

```
{
 "counts": the number of units of each class, for the claims and for the timeline apart,
 "new_core": the ids of the units of class N and of class A that carry the route, most
             important first, each with one sentence on why the route needs it,
 "note_agrees": one to three sentences on whether the units of class N and A are the ones that
                the author's note presents as new,
 "open": the questions that a specialist in automorphic forms or analytic number theory would
         have to settle before this classification can be relied on
}
```

## How you work

1. Judge what the unit states. A name in the code that resembles a known theorem is a hint,
   which you then confirm from the row, the commentary or the Lean text.
2. Cite a source only after you opened it in this run, and give the address that you opened.
   Take the quote from the page that you opened.
3. Prefer the paper that first proved a result. Add a textbook when it states the result in
   the form of the unit.
4. Judge only whether the mathematics was published before 20 November 2026. Whether the proof
   is correct is outside this task.
5. Writings about this proof, such as notes and posts that appeared after the announcement,
   are commentary. Use them to understand a unit and keep them out of `nearest`.
6. When a unit joins two known results in a way that you find in no source, class it A and
   name both sources.
7. Say in `confidence` how sure you are of the class. Low is the right answer when the unit
   rests on definitions that you could not open.
8. Write every text field in full sentences. Use a full stop where a colon or a semicolon
   would stand.

Read the files named above and write only the thirteen files of
`verification/review/gemini-novelty/`. Leave every other file as it is.
