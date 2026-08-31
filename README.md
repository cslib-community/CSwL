# CSwL — Computational Semantics with Lean

[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-v4.33.0-purple.svg)](https://lean-lang.org)
[![Try it live](https://img.shields.io/badge/live.lean--lang.org-try%20it-orange)](https://live.lean-lang.org/)

A [Lean 4](https://lean-lang.org) adaptation of *Computational Semantics with
Functional Programming*, by Jan van Eijck and Christina Unger (Cambridge
University Press, 2010) — inspired by the book's path through the material,
not a translation of it. Definitions are rewritten from scratch in idiomatic
Lean, exercises are code or proofs, and the presentation is reorganized wherever Lean's own resources (dependent types, tactics, formal proof) call for a different order or a different exercise than the original Haskell allowed.

It follows van Eijck & Unger but diverges whenever adapting to Lean or to this course asks for it — see [Deviations from CSwFP](#deviations-from-cswfp) below.

Exercises live inside each chapter, right where the corresponding book
section is discussed — see [Exercises](#exercises) below.

## Getting started

To run locally: [install Lean](https://lean-lang.org/install), then 

```bash
lake exe cache get
```
(downloads prebuilt Mathlib — without it, `lake build` would compile
the whole library from scratch) and `lake build`.

Or, to build and browse the book locally:

```bash
make serve   # serves at http://127.0.0.1:8000/
```

## Chapters

- [X] The formal study of natural language — [source](CSwL/IntroCS.lean)
- [X] Introduction to Lean — [source](CSwL/IntroL.lean)
- [~] Applications (Finnish vowel harmony, Swedish plural, phonemes) —
  [source](CSwL/Applications.lean) (sections in
  [`CSwL/Applications/`](CSwL/Applications))
- [~] Foundations — [source](CSwL/Foundation.lean)
- [~] Grammars for games (Sea Battle, Mastermind) —
  [source](CSwL/Games.lean) (sections in [`CSwL/Games/`](CSwL/Games))
- [~] A fragment of English — [source](CSwL/English.lean)
- [~] Logics (propositional and predicate) — [source](CSwL/Logic.lean)
  (sections in [`CSwL/Logic/`](CSwL/Logic))
- [ ] Formal semantics of fragments
- [ ] Model checking with predicate logic
- [ ] The composition of meaning
- [ ] Extension and intension
- [ ] Parsing
- [ ] Relations and scope
- [ ] Semantics in continuation passing style
- [ ] Discourse representation and context
- [ ] Communication as informative action

## Exercises

Exercises live inside the file for the section they correspond to (see
[Chapters](#chapters) and [Conventions](#conventions)), right after the book
section. Each `sorry` is an item left to complete (or `example`, for
exercises not reused later in the chapter itself).

## Conventions

Mnemonic file names. A short chapter is a single file (`CSwL/Foundation.lean`,
`namespace Foundation`); a chapter whose sections are long enough to deserve
their own file is a "glue" file (`CSwL/Games.lean`) that only gathers, via
`{include 1 ...}`, sections living in a same-named directory
(`CSwL/Games/SeaBattle.lean`, `CSwL/Games/Mastermind.lean`) — the same pattern
used by [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/). Each content file has its own `namespace`, 
mnemonic and necessary: the book redefines the same names in different chapters.

CSwL developments connect with those in [CSLib](https://github.com/leanprover/cslib/) where possible. We aim to reuse CSLib and contribute to CSLib.

## Deviations from CSwFP

`CSwL` is inspired by CSwFP, not a 1-to-1 port of it: chapters get
renumbered, sections and exercises get reordered, adapted or added,
whenever presenting the material well in Lean or in this course asks
for it. See [DEVIATIONS.md](DEVIATIONS.md) for the detailed,
chapter-by-chapter log of where and why.

## License and rights

The book is © Jan van Eijck and Christina Unger, 2010, Cambridge University
Press. This repository is an independent, adapted work: original code and
prose, inspired by the book's themes and order but not a translation or
reproduction of its text.
