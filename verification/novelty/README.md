# Which part of the mathematics is new

This folder prepares a search of the published literature for each step of the proof. The
search is to say for every step whether its mathematics was published before 20 November 2026,
the day the proof was announced, and where. No result is in yet. The task
`rh-novelty-literature-search` waits for a run of Gemini in the Antigravity editor.

A step is called a unit here. There are 64 units of two kinds.

- 44 units are the rows of the tables of [`CLAIMS.md`](../strategy/CLAIMS.md), which list what
  the Lean text states at each step of the route from the five theorems down to the bounds on
  one lattice.
- 20 units are the entries of the timeline in the [note](https://alpo.ge/remark.pdf) of the
  author of the source, each with a paraphrase that [`units.py`](units.py) holds.

The brief [`brief-gemini.md`](brief-gemini.md) asks for one answer for each unit. An answer
names the technique of the unit in the terms of the literature, gives up to three sources with
the place and a short quote, says what differs between the unit and the nearest source, and
puts the unit in one of five classes.

| Class | Meaning |
|---|---|
| K | a source published before the announcement states the result |
| A | the technique is published, and the unit uses it on another object or in a new combination |
| N | the searches found no source with the result or the technique |
| G | the unit is bookkeeping of the proof without a technique of its own |
| U | the unit is too much in the project's own vocabulary to compare |

The answers go to `verification/review/gemini-novelty/`, one file for each of the twelve
batches of `units.json` and one file with a synthesis. After that a second model opens every
cited source and checks the quote, as the readings of [`../skeleton`](../skeleton/READING.md)
were checked by two makers' models. A class N says that a search found nothing. It does not
say that nothing exists, and the judgement of a specialist stays open.

## Where the labelled results end

[`KNOWN.md`](KNOWN.md) is a result that needs no search of the literature. It places the 296
results that the source labels as known, or that the catalogue of `../reuse` names, on the
outline of the proof and counts the declarations that their proofs use. They are 26.9 % of the
declarations that the five theorems use, and 0.1 % of the branch that carries the route of the
proof.

## Files

| File | Content |
|---|---|
| `units.py` | collects the units from `CLAIMS.md` and holds the paraphrases of the timeline |
| `units.json` | the 64 units in twelve batches |
| `brief-gemini.md` | the brief of the literature search |
| `KNOWN.md`, `known.py`, `known.json` | the known results placed on the outline of the proof |
