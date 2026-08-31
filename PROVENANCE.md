# Exercise provenance

Which CSwFP exercise each `CSwL` exercise comes from. This mapping used to live
in the book's own prose, as `Ref. CSwFP/4, exercício 4.9 (p. 74)` lines; the
book must be self-contained and never name its source, so those lines are
removed and the correspondence is kept here instead.

This file is for the instructor: checking coverage (which of the book's
exercises are ported, which are still missing) and finding the original
statement when an exercise needs revising. It is documentation *about* the
project, not part of the book.

The `CSwL id` column holds each exercise's `(name := …)`. Since the rename of
2026-08-30 these are English mnemonics carrying no number, so **this file is
now the only link between an exercise and the passage it comes from**. Keep it
in step with any further rename.

`prose` marks an exercise whose answer is given in prose rather than stated in
Lean. In the source these carry a `✎` marker, which is otherwise undocumented.

## A correction to the numbers

The 17 references in `Sets.lean` were all off by one chapter: they read
`CSwFP/2, exercício 3.N` where the book has **Exercise 2.N**. The page numbers
they cite were right, which is what makes the shift visible — CSwFP's
Exercise 2.1 is on p. 17, and the file cited "exercício 3.1 (p. 17)". The book's
chapter 2 has exercises 2.1 to 2.17, and there are exactly 17 of them.

The table below carries the corrected numbers. `IntroCS.lean`, `Logic/PL.lean`,
`Logic/FOL.lean` and `Morphology/Phonemes.lean` were checked against the same
source and are correct.

## Exercises taken from CSwFP

### `IntroCS.lean` — CSwFP/1

| CSwL id | Rating | CSwFP | Page |
|---|---|---|---|
| `possibilities` | 1 | Exercise 1.1 | 6 |
| `sentence-go-on` | 1 | Exercise 1.2 | 8 |

CSwFP Exercise 1.3 (infinitely many sentences, p. 8) is not ported.

### `Morphology/Phonemes.lean` — CSwFP/3.14

| CSwL id | Rating | CSwFP | Page |
|---|---|---|---|
| `yawelmani-harmony` | 3 | Exercise 3.19 (Yawelmani vowel harmony) | 61–62 |

`feature-value` (rating 2) and `append-suffix-text` (rating 3) have no counterpart:
CSwFP hands `feature-value`/`fMatch` to the reader as given code, and `CSwL` turns
them into exercises.

### `Sets.lean` — CSwFP/2 (exercises `twice` and `adjective-types` moved on
with CSwFP/2.4 and 2.5, to `IntroL.lean` and `English.lean`)

| CSwL id | Rating | CSwFP | Page | Notes |
|---|---|---|---|---|
| `empty-subset` | 1 | Exercise 2.1 | 17 | |
| `empty-vs-singleton` | 1 | Exercise 2.2 | 17 | prose |
| `double-complement` | 2 | Exercise 2.3 | 17 | prose |
| `cartesian-square` | 2 | Exercise 2.4 | 18 | |
| `successor-composition` | 2 | Exercise 2.5 | 18 | |
| `converse-subset` | 2 | Exercise 2.6 | 18 | |
| `which-are-transitive` | 2 | Exercise 2.7 | 19 | |
| `transitive-iff-comp` | 2 | Exercise 2.8 | 19 | |
| `transitive-not-idempotent` | 2 | Exercise 2.9 | 19 | |
| `successor-as-relation` | 1 | Exercise 2.10 | 21 | |
| `leq-as-function` | 1 | Exercise 2.11 | 21 | |
| `graph-is-functional` | 2 | Exercise 2.12 | 21 | |
| `twice` | 1 | Exercise 2.13 | 26 | |
| — | — | Exercise 2.14 | 26–27 | prose; not in an `:::exercise` block |
| — | — | Exercise 2.15 | 28 | prose; not in an `:::exercise` block |
| — | — | Exercise 2.16 | 28 | prose; not in an `:::exercise` block |
| `adjective-types` | 1 | Exercise 2.17 | 30 | |

Note that 2.14, 2.15 and 2.16 sit in the prose without an exercise directive,
so they get no rating, no solution elision and no autograding.

Exercises 2.1, 2.2 and 2.3 (`empty-subset`–`double-complement` above) stay with this chapter when it
moves after `Logic.lean`; 2.3 (`Ā̄ = A`) is the one that needs classical
reasoning, and is the reason for the move.

### `Logic/PL.lean` — CSwFP/4.4

| CSwL id | Rating | CSwFP | Page |
|---|---|---|---|
| `translate-sentences` | 1 | Exercise 4.9 | 74 |
| `exclusive-or` | 1 | Exercise 4.10 | 74 |
| `unique-readability` | 2 | Exercise 4.11 | 74 |
| `count-operators` | 1 | Exercise 4.12 | 75 |
| `formula-depth` | 1 | Exercise 4.13 | 75 |
| `collect-atoms` | 2 | Exercise 4.14 | 75 |

The chapter also names two of the book's results in its prose — Theorem 4.1
(structural induction) and Proposition 4.2 (equal number of parentheses). Those
attributions are removed from the book; the results themselves stay.

### `Logic/FOL.lean` — CSwFP/4.5–4.7

| CSwL id | Rating | CSwFP | Page | Notes |
|---|---|---|---|---|
| — | — | Exercise 4.15 | 77 | prose; a `#` heading, not an `:::exercise` block |
| — | — | Exercise 4.16 | 77 | prose; heading |
| — | — | Exercise 4.17 | 78 | prose; heading |
| `closed-form` | 1 | Exercise 4.18 | 81 | inside a `##` heading also numbered 4.18 |
| — | — | Exercise 4.19 | 82 | heading |
| — | — | Exercise 4.20 | 82 | heading |
| — | — | Exercise 4.21 | 83 | prose; heading |
| — | — | Exercise 4.22 | 84 | heading |
| — | — | Exercise 4.23 | 84 | heading |
| `open-form` | 1 | Exercise 4.24 | 84 | |

Nine of these are plain headings carrying the book's page number rather than
exercise directives. Both problems — the page in the heading and the missing
directive — are recorded in `TODO.md`.

## Exercises original to CSwL

No CSwFP counterpart. Listed so that "absent from the table above" is not read
as an oversight.

| File | CSwL id | Rating |
|---|---|---|
| `Morphology/Phonemes.lean` | `feature-value` | 2 |
| `Morphology/Phonemes.lean` | `append-suffix-text` | 3 |
| `Morphology/SwedishPlural.lean` | `swedish-plural` | 2 |
| `English.lean` | `preposition-phrase` | 1 |
| `English.lean` | `complex-relative-clauses` | 1 |
| `Sets.lean` | `five-in-above2` | 1 |
| `Sets.lean` | `one-not-in-above2` | 1 |
| `Sets.lean` | `above5-subset-above2` | 1 |
| `Sets.lean` | `union-contains` | 1 |
| `Sets.lean` | `intersection-contained` | 1 |
| `Games/Mastermind.lean` | `four-turn-game` | 1 |
| `Games/Mastermind.lean` | `chess-grammar` | 1 |
| `Games/SeaBattle.lean` | `game-over-grammar` | 2 |
| `Games/SeaBattle.lean` | `defeated-last` | 3 |
| `Games/SeaBattle.lean` | `add-ship` | 3 |
| `Games/SeaBattle.lean` | `sunk` | 2 |
| `Games/SeaBattle.lean` | `grice-maxims` | 1 |
| `IntroL.lean` | `sum-of-squares` | 1 |
| `IntroL.lean` | `building-terms` | 1 |
| `IntroL.lean` | `p-implies-q-implies-p` | 1 |
| `IntroL.lean` | `implication-transitivity` | 1 |
| `IntroL.lean` | `apply-several-premises` | 1 |
| `IntroL.lean` | `unfold-direct-proof` | 1 |
| `IntroL.lean` | `unfold-conjunction` | 1 |
| `IntroL.lean` | `cases-on-or` | 1 |
| `IntroL.lean` | `sum-to` | 1 |
| `IntroL.lean` | `sum-list` | 1 |
| `IntroL.lean` | `count-zeros` | 1 |

CSwFP's chapter 3 exercises 3.1–3.18 are not ported: they are about Haskell
itself (types of Haskell functions, Haskell programs to read). Exercise 3.18
(the type of `vh`, p. 54) belongs with Finnish vowel harmony and is the one
worth reconsidering.

## Section-level references

These were also `Ref.` lines in the book's prose. The chapter-level mapping now
lives in `DEVIATIONS.md`; this table records the finer-grained pointers that
existed inside chapters.

| File | Section | CSwFP | Page |
|---|---|---|---|
| `IntroCS.lean` | chapter opening | CSwFP/1 Formal Study of Natural Language | — |
| `IntroL.lean` | Tipos indutivos | §3.13 | 55 |
| `IntroL.lean` | Recursão | §3.5 | 40 |
| `IntroL.lean` | Listas | §3.6, and §3.4 for polymorphism | 41, 39 |
| `IntroL.lean` | `map`/`filter` | §3.7, §3.8 | 42–43 |
| `IntroL.lean` | Type classes | §3.9 | 45 |
| `IntroL.lean` | Strings | §3.10 | 47–48 |
| `Sets.lean` | chapter opening | CSwFP/2 Lambda Calculus, Types, and Functional Programming | — |
| `Morphology/Phonemes.lean` | chapter opening | §3.14 | 58–61 |
