# Theorems that add little, found in the source text and checked by Lean

This repository holds a Lean formalisation that claims the Riemann hypothesis, and its five
main theorems are in [`Main.lean`](../../src/Main.lean). Of the project's 666,738 theorems and
lemmas, 51,364 are forwarding theorems. The whole proof of a forwarding theorem is one other
declaration, its target. Another 14,838 are proved by `rfl` or by another fixed proof of that
kind. Lean could compare 47,110 forwarding theorems with their targets, and 42,737 of them state
exactly what the target states, so each of those is a second name for one theorem. Across all
theorems, Lean confirms 50,502 that repeat the statement of an earlier theorem. This figure
includes the forwarding theorems whose statement text equals the text of their target.

The scan in this folder reads the source text and finds the theorems that look redundant, the
candidates. A second script then has Lean compare the compiled statements of the candidates.

A forwarding theorem, a repeated statement or a proof by `rfl` is not an error, and Lean
accepts each one. The scan counts the theorems whose form usually adds no mathematical content.
It does not judge any single theorem.

The figures are for the Lean 4.36 source of commit `611ce0b6` of the upstream repository
[`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis).
The source as first published had 818,755 theorems and lemmas, and the section "The first
published source" gives its figures.

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
forward. In it `X` is the forwarded declaration.

```lean
by first | exact @X | exact X | (intros; apply X <;> assumption)
```

Two theorems have the same statement when their statements are the same text after their bound
variables are numbered in order of binding, and when the `variable` lines in scope are the same
text too. A duplicate group is a set of two or more theorems with the same statement.

## Results of the text scan

The declaration graph of [`../decl-graph`](../decl-graph/README.md) estimates which declarations
the five theorems of [`Main.lean`](../../src/Main.lean) use. A declaration is used when a chain
of mentions in the text leads to it from one of the five. The names estimate follows only the
names that resolve as Lean resolves them and reaches 616,958 theorems and lemmas. The widest
estimate also follows field names, unresolved names and the lemmas that tactics pick up by
themselves, and it reaches 653,169. The second and third columns of the table count the theorems
of each class that these two estimates take as used. A used theorem cannot be deleted without
changing the proof of the five, so these columns show how much of each class is part of that
proof.

| Class | Theorems | Used, by the names estimate | Used, by the widest estimate |
|---|---:|---:|---:|
| reflexive | 1 | 1 | 1 |
| restates a premise | 31 | 25 | 26 |
| true | 0 | 0 | 0 |
| rfl | 14,838 | 13,638 | 14,499 |
| one tactic | 546 | 510 | 538 |
| returns a premise | 227 | 206 | 216 |
| forward | 51,364 | 49,402 | 50,425 |
| any of the seven | 66,978 | 63,759 | 65,681 |

A theorem can carry two or three classes at once, so the last row is smaller than the sum of
the rows above it. The 66,978 are 10.0 % of all theorems and lemmas.

The scan also groups theorems by the text of their statement.

| Group of | Groups | Theorems in them | Copies beyond the first of each group | Largest group |
|---|---:|---:|---:|---:|
| theorems with the same statement text | 51,332 | 113,097 | 61,765 | 156 |
| theorems with the same statement text and the same proof text | 11,198 | 25,489 | 14,291 | 30 |
| definitions with the same text, statement and value together | 3,425 | 7,922 | 4,497 | 88 |

## What Lean says about the candidates

The same text can mean two things. The project defines some names more than once, and which
definition a name means depends on the `open` lines of the module. `check_same.py` therefore
hands every candidate to Lean. `CheckSame.lean` reads the compiled file of each module and
compares the statements as Lean stores them, with every name resolved. Two statements count as
the same when the stored terms are equal. No definition is unfolded, so the answer "same" is
exact, and the answer "different" still allows two statements that become equal once a
definition is unfolded.

The check reads the public part of each compiled module. It does not find a declaration marked
`private`. Of the 215,239 candidate declarations, 11,665 were not found, and 11,648 of those are
private.

### Forwarding theorems

The scan resolves the forwarded name to a declaration of the project for 47,240 forwarding
theorems. For 47,110 of them the proof names the target itself, and for the other 130 it names a
part of the target such as `.symm`. The table gives Lean's answer for the 47,110.

| The text of the two statements | Pairs | Same statement | Different statement | A constant not found |
|---|---:|---:|---:|---:|
| is the same | 30,456 | 30,157 | 170 | 129 |
| is not the same | 16,654 | 12,580 | 3,536 | 538 |
| all pairs | 47,110 | 42,737 | 3,706 | 667 |

Lean confirms 42,737 pairs as the same statement, while the texts agree in 30,456 pairs. In
12,580 pairs the two texts differ and the compiled statements are still equal. In 170 pairs the
texts are equal and the compiled statements are not.

Of the 42,737 confirmed pairs, 35,411 have their forwarding theorem in a module whose name
ends in `Statement`. The project keeps a theorem in one module and states it again in such a
module, with the fixed forwarding proof shown above.

Two of the five theorems of `Main.lean` are forwards. `LFunction_ne_zero_of_half_lt_re`
forwards `UpperTheory.FinalTheorems.everyCharacter`, and `riemannZeta_eq_zero_re` forwards
`riemannHypothesis`. The other three are short as well, though they are not forwards by the
definition above. `riemannHypothesis` and `LFunction_eq_zero_re` each apply one theorem to
`LFunction_ne_zero_of_half_lt_re`, and `LFunction_eq_zero_re_of_isPrimitive` applies
`LFunction_eq_zero_re` to its own variables.

### Duplicate statements

| | Theorems | Definitions |
|---|---:|---:|
| Groups with the same text | 51,332 | 3,425 |
| Groups in which Lean finds one statement | 42,666 | 1,315 |
| Groups in which Lean finds two or more statements | 3,675 | 1,889 |
| Groups with a member that was not found | 5,038 | 224 |
| Copies beyond the first of each statement, by Lean | 50,502 | 1,808 |

A group with a member that was not found can also hold two or more statements, so the three
middle rows add up to a little more than the first row. The last row counts, inside every
group, the members that share their compiled statement with an earlier member. These 50,502 theorems are confirmed duplicates. The figure includes the
forwarding theorems that have the same statement text as their target.

Lean finds two or more statements in 7 % of the groups of theorems and in 55 % of the groups of
definitions. A likely cause, which was not examined, is that a copied definition refers to
copied helper definitions of its own namespace. Such copies may still be equal once the helpers
are unfolded, which this check does not try.

The largest group of theorems holds one statement in most members and a second statement in a
few. It holds 156 theorems with the text below, which says that
the map of spectra of a composite ring homomorphism is the composite of the maps of spectra.
Lean finds one statement in 141 of them and another statement in 5, since the project defines
`spMap` more than once. The other 10 are private.

```lean
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f)
```

### Statements that are true by their form

Thirty-two theorems have a statement class, and the widest estimate takes 27 of them as used.
Twenty-eight of the 31 that restate a premise also have a proof that returns that premise, in
the form `(h : P) : P := h`. After a run of the scan, the 32 are the rows of
`data/findings.tsv.gz` whose classes include `reflexive` or `premise`. Two examples follow.

```lean
theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card

theorem llOf_alt : RecTExists → LocalConverseGL → DepthZeroInduction → BrauerDegreeZero →
    ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma →
    BernsteinZelevinskyFiniteness → RecTExists :=
  fun h _ _ _ _ _ _ _ _ _ _ _ => h
```

The second, `UpperTheory.One.M.New.llOf_alt`, takes twelve premises and returns the first one. A
theorem that forwards it is named `recTExists_of_published_inputs`. The name reads as a
derivation of `RecTExists` from the eleven other premises, while the proof uses none of them.
Both estimates take `llOf_alt` as used by the five theorems of `Main.lean`. Whoever calls it
must already hold a proof of `RecTExists`, so a proof that calls `llOf_alt` could use that proof
of `RecTExists` directly.

The source shows where that proof comes from. `UpperTheory.FinalTheorems.everyCharacter_of_row`
in `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` builds the structure
`OpenLiteratureStatements`, whose field `localLanglandsExists` has the type `RecTExists`, and it
fills that field with the theorem `UpperTheory.Zero.LLC.recTExists`. That theorem has no
premises and a proof of its own. One caller of `llOf_alt`, in
`EveryCharacterOfLiteratureOfVWin.lean`, takes the structure as an argument and passes a proof
drawn from it to `llOf_alt` as the first premise. In the source text,
`RecTExists` is therefore proved inside the project and is not an assumption of the five
theorems. Whether that proof holds is for Lean's kernel to check, which this folder does not
do.

## What follows and what can be done

None of these findings shows a fault in the proof of the five theorems. They concern its size
and how it reads.

- A forwarding theorem with the same statement as its target adds a second name and nothing
  else. It can be removed by pointing its uses at the target. A module whose name ends in
  `Statement` may be meant as the place where a result is stated for readers, and then it has
  a use that the second name alone does not show.
- A confirmed duplicate with a proof of its own is compiled once per copy. One copy can be kept
  and the others removed, with their uses pointed at the kept one, as pull request #116 of the
  upstream repository does for one directory. `data/same_checked.tsv.gz` lists the members of
  every group with Lean's answer and can serve as the list of candidates for that work.
- A theorem of the form `(h : P) : P` can be removed. `recTExists_of_published_inputs` promises
  a derivation by its name and gives none, so it and `llOf_alt` are candidates for removal or
  for a new name.
- Every removal has to be compiled before it is trusted. A text scan misses uses that only Lean
  sees, as the build failures reported in issue #3 of the upstream repository show.

## Limits

- The scan compares text and the patterns are fixed. The review named in the next section
  found in the first published source that 13 of 110 theorems without a class were one-step proofs that the
  patterns miss, such as `by simp [f]` or a forward with a compound argument. The class counts
  are therefore closer to lower bounds than to exact counts.
- Duplicates that are written differently, with reordered variables or a moved premise, are not
  candidates and are missed.
- Lean's check compares stored terms. It reads the compiled files that `lake exe cache get`
  downloads. Volunteers' machines build those files for the upstream repository, so the check
  is as reliable as that cache. It does not check any proof.
- A proof by `rfl` can still state a useful fact, for example a rewriting rule that unfolds a
  definition. The rfl class counts such proofs and does not judge them.
- The scan counts the copies and does not measure how much of the project would go with them.
  A copy with a proof of its own can have helper lemmas that only it uses.

## The first published source

The same scan on the source as first published, on Lean 4.33.1, found 66,185 forwarding
theorems among 818,755 theorems and lemmas, 22,421 proofs of one word, 59 statements with a
statement class and 78,892 copies beyond the first among theorems with the same statement text.
Lean's check was not run on that source. An independent review of those figures and of the
scripts is in [`../review/antigravity-review.md`](../review/antigravity-review.md), and the
faults it found are corrected here.

## Running it

```bash
python3 -I verification/decl-graph/build.py     # first, for the two estimates of use
python3 -I verification/redundancy/scan.py      # under a minute
```

Lean's check needs a checkout of the same commit with the compiled files in place.

```bash
lake exe cache get                               # in that checkout
python3 -I verification/redundancy/check_same.py /path/to/that/checkout
```

The check opens about 96,000 compiled files. It took about an hour on the machine used for these figures, from a slow external disk.
After an interruption, the option `--resume` continues from the groups already answered.

## Files

| File | Content |
|---|---|
| `scan.py` | the text scan |
| `summary.json` | the figures of the scan |
| `check_same.py` | collects the candidates, runs Lean on them and counts the answers |
| `CheckSame.lean` | compares the compiled statements |
| `same-check.json` | the figures of Lean's check |
| `data/findings.tsv.gz` | one row per theorem with a class, with its module, name, classes and forwarded declaration |
| `data/forward_pairs.tsv.gz` | the forwarding theorems with their resolved targets |
| `data/theorems_same_statement.tsv.gz` | the groups of theorems with the same statement text, one row per member |
| `data/definitions_same_text.tsv.gz` | the groups of definitions with the same text, one row per member |
| `data/same_checked.tsv.gz` | every candidate with Lean's answer, as a number that members with the same statement share |

Git ignores `data/`, which the scripts write again on every run.
