# Theorems that add little, found in the source text

Of the project's 818,755 theorems and lemmas, 66,185 have a proof that is one other declaration
and nothing more, 22,421 are proved by `rfl` or another proof of one word, and 78,892 repeat a
statement that another theorem of the project already states. Fifty-nine have a statement that is
true by its form alone. The scan in this folder finds them by reading the source text. It does
not run Lean.

A theorem of these kinds is not an error, and Lean accepts each one. The scan counts the
theorems whose form usually adds no mathematical content. It does not judge any single theorem.

## What the scan looks for

`scan.py` reads every theorem and lemma in `src/` and splits it into its statement and its
proof. The statement is the text before the first `:=` outside brackets and the proof is the
text after it. The scan compares texts once runs of whitespace are reduced to one space.

A theorem's statement gets one of three classes.

| Class | The statement, after its leading `∀` and its premises |
|---|---|
| reflexive | is `X = X`, `X ↔ X`, `X ≤ X` or `X ⊆ X`, with both sides written the same |
| restates a premise | is written the same as one of the theorem's own premises |
| true | ends in the proposition `True` |

A theorem's proof gets one of four classes.

| Class | The whole proof |
|---|---|
| rfl | is one of 23 fixed proofs such as `rfl`, `Iff.rfl`, `le_rfl`, `trivial` and `by rfl`, which Lean accepts when the claim holds by definition or by the reflexivity of a relation |
| one tactic | is `by` and one of 26 tactics without arguments, such as `by simp` or `by omega` |
| returns a premise | is the name of one of the theorem's own premises |
| forward | is one other declaration, applied to nothing or to variables of the theorem or of its section |

The sets `RFL` and `ONE_TACTIC` at the top of `scan.py` list those proofs and tactics. The
project writes many forwarding proofs in one fixed form, which the scan also counts as
forward.

```lean
by first | exact @X | exact X | (intros; apply X <;> assumption)
```

Two theorems have the same statement when their statements are the same text after their bound
variables are numbered in order of binding, and when the `variable` lines in scope are the same
text too. A duplicate group is a set of two or more theorems with the same statement.

## Results

The declaration graph of [`../decl-graph`](../decl-graph/README.md) estimates which declarations
the five theorems of [`Main.lean`](../../src/Main.lean) use. A declaration is used when a chain
of mentions in the text leads to it from one of the five. The names estimate follows only the
names that resolve as Lean resolves them and reaches 619,011 theorems and lemmas. The widest
estimate also follows field names, unresolved names and the lemmas that tactics pick up by
themselves, and it reaches 686,930. The second and third columns of the table count the theorems
of each class that these two estimates take as used.

| Class | Theorems | Used, by the names estimate | Used, by the widest estimate |
|---|---:|---:|---:|
| reflexive | 2 | 1 | 1 |
| restates a premise | 57 | 25 | 27 |
| true | 2 | 0 | 0 |
| rfl | 22,421 | 13,755 | 17,791 |
| one tactic | 697 | 506 | 562 |
| returns a premise | 353 | 207 | 227 |
| forward | 66,185 | 49,952 | 53,730 |
| any of the seven | 89,662 | 64,423 | 72,313 |

A theorem can carry two or three classes at once, so the last row is smaller than the sum of
the rows above it. The first three rows hold 59 different theorems for the same reason. The 89,662 are 11.0 % of all theorems and lemmas.

### Forwarding theorems

The next table splits the 66,185 forwarding theorems by the declaration they pass on.

| The forwarded declaration | Theorems | Used, by the widest estimate |
|---|---:|---:|
| is a declaration of the project with the same statement | 39,793 | 32,103 |
| is a declaration of the project with another statement | 21,256 | 17,182 |
| is not a declaration of the project, so it comes from Lean or Mathlib | 5,136 | 4,445 |

The scan takes the forwarded name as a declaration of the project when the declaration graph
resolves it to one, also when a part such as `.symm` or `.le` follows the name.

The first row is a plain renaming. The project often keeps a theorem in one module and states it
again in a second module whose name ends in `Statement`, with the fixed forwarding proof shown
above. Four of the five theorems of `Main.lean` are forwards too. `riemannHypothesis` and
`riemannZeta_eq_zero_re` forward `rhOfAll`, `LFunction_ne_zero_of_half_lt_re` forwards `allChi`
and `LFunction_eq_zero_re_of_isPrimitive` forwards `critAll`. The fifth, `LFunction_eq_zero_re`,
takes a part of `claimAll`. `allChi` in turn forwards
`UpperTheory.FinalTheorems.everyCharacter`.

### Statements that are true by their form

Twenty-eight of the 59 theorems with a statement class are used by the widest estimate. The first
example below is reflexive. The second ends in `True` and also restates its premise. The third
restates a premise.

```lean
theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card

theorem bridge_true : True → True := id

theorem llOf_alt : RecTExists → LocalConverseGL → DepthZeroInduction → BrauerDegreeZero →
    ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma →
    BernsteinZelevinskyFiniteness → RecTExists :=
  fun h _ _ _ _ _ _ _ _ _ _ _ => h
```

The third, `UpperTheory.One.M.New.llOf_alt`, takes twelve premises and returns the first one. A
theorem that forwards it is named `recTExists_of_published_inputs`, and one of the eleven other
premises, `GlobalArtinReciprocity`, lies in a namespace that the project calls `Published`. The name
reads as a derivation of `RecTExists` from those eleven, while the proof uses none of them. Both
estimates take `llOf_alt` as used by the five theorems of `Main.lean`. Whoever calls it must
already hold a proof of `RecTExists`, so the call adds nothing to the final proof.

The source shows where that proof comes from. `UpperTheory.FinalTheorems.everyCharacter_of_row`
in `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` builds the structure
`OpenLiteratureStatements`, whose field `localLanglandsExists` has the type `RecTExists`, and it
fills that field with the theorem `UpperTheory.Zero.LLC.recTExists`. That theorem has no
premises and a proof of its own in
`Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean`.
`llOf_alt` then passes the field's value on unchanged. `RecTExists` is therefore proved inside
the project and is not an assumption of the five theorems.

Of the 57 theorems that restate a premise, 52 also have a proof that returns that premise, in
the form `(h : P) : P := h`.

### Duplicate statements

| Group of | Groups | Theorems in them | Copies beyond the first of each group | Largest group |
|---|---:|---:|---:|---:|
| theorems with the same statement | 65,279 | 144,171 | 78,892 | 186 |
| of those, theorems with the same proof text as well | 14,682 | 33,617 | 18,935 | 35 |

A forwarding theorem with the same statement as its target forms a duplicate group with that
target, so the two findings overlap. Without all 66,185 forwarding theorems, 26,732 groups
remain, with 37,844 copies beyond the first of each group. The widest estimate counts 29,071 of
those copies as used by the five theorems.

The largest group states 186 times, in 186 modules, that the map of spectra of a composite ring
homomorphism is the composite of the maps of spectra. The project defines `spMap` more than
once. By the `open` lines of their modules, 179 of the copies mean one definition and 7 mean
another, so this group holds two statements and not one.

```lean
theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f)
```

Definitions repeat too. The project has 5,520 groups of `def` and `abbrev` declarations with the
same text, statement and value together, which hold 12,963 definitions, 7,443 of them beyond the
first of each group. The largest group has 22 members.

### Length of proofs

The median proof of a theorem or lemma is 36 words long, counted as runs of text between spaces.
Proofs of at most five words number 94,387, which is 11.5 % of the theorems, and 41,772 proofs
have more than 500 words.

## Limits

- The scan compares text. Two statements with the same text mean different things when a name
  in them resolves to different declarations, as in the largest group above. An independent
  review drew 35 duplicate groups at random and found one such group among them. The duplicate
  counts are therefore somewhat too high. Duplicates that are written differently, with
  reordered variables or a moved premise, are missed, which makes the counts too low on the
  other side.
- The classes rest on fixed patterns. The same review found two false members of the statement
  classes and three false forwards in a sample of 35, all from two faults that are corrected in
  the figures above. It also found that 13 of 110 theorems without a class are one-step proofs
  that the patterns miss, such as `by simp [f]` or a forward with a compound argument. The
  class counts are therefore closer to lower bounds than to exact counts.
- A proof by `rfl` can still state a useful fact, for example a rewriting rule that unfolds a
  definition. The rfl class counts such proofs and does not judge them.
- The scan reads 1,057,878 declarations, 3,653 fewer than the declaration graph, because it
  leaves out `alias` commands and declarations without a name.
- Removing a forwarding theorem with the same statement removes a second name and nothing else.
  A copy with a proof of its own is different. It can have helper lemmas that only it uses, and
  they would go with it. The scan counts the copies and does not measure how much of the
  project would go with them.

The review is in [`../review/antigravity-review.md`](../review/antigravity-review.md). It was
written against the earlier figures of this page and of the declaration graph.

## Running it

```bash
python3 -I verification/decl-graph/build.py     # first, for the two estimates of use
python3 -I verification/redundancy/scan.py      # about 40 seconds
```

## Files

| File | Content |
|---|---|
| `scan.py` | the scan |
| `summary.json` | the figures of the scan |
| `data/findings.tsv.gz` | one row per theorem with a class, with its module, name, classes and forwarded declaration |
| `data/theorems_same_statement.tsv.gz` | the duplicate groups of theorems, one row per member |
| `data/definitions_same_text.tsv.gz` | the duplicate groups of definitions, one row per member |

Git ignores `data/`, which `scan.py` writes again on every run.
