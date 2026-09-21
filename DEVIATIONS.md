# How CSwL uses CSwFP

`CSwL` is not a section-by-section translation of CSwFP. It reorders the material so that the
presentation is natural in Lean, under one hard constraint:

> **Nothing is used before it is presented.**

Names of files, chapter, section tags, and exercises are English mnemonics. The prose is in
Portuguese; the identifiers inside Lean blocks are in English.

The prose never explains the CLwL material by contrast with CSwFP. Those reasons belong in this
document.  The line to hold is not "never mention an alternative". It is:

- a **technical consequence in Lean** is content, because the reader will meet it. "A constructor
  holding a `List Form` makes the type a nested inductive, and a nested inductive has no `induction`
  tactic" states a fact about Lean that the chapter then depends on;
- an **editorial preference** is meta. "We preferred to keep `Game` as it is", "the columns could
  have been modelled like the rows, but we chose the usual convention" — these report what the
  authors decided, which is this document's subject and not the book's.

The test: would the sentence still be worth writing if this book had no source and no alternatives?
A fact about Lean survives that; a preference does not.

A chapter that translates keeps the original's structure — its section boundaries, its order, its
sentence boundaries and its punctuation. Subheadings that the source does not have are not added,
and headings the source has are not merged, unless something in this document says so and says why.

Most chapters, though, are mixed: part translated, part written here because Lean makes something
sayable that the source could not say. In a mixed chapter the rule applies section by section. A
translated section follows the original; a new section has a structure of its own, chosen for what
it teaches. Which sections are which is recorded per chapter below — a reader of this document
should never have to guess whether a heading came from the source or from us.

Any divergence from this plan is stated when it is made. A silent divergence is worse than a wrong
one: a wrong decision can be argued with, an unrecorded one cannot.

"Presented" has one deliberate loosening and one exception.

The loosening: Lean's own basic types may be introduced *where they are first needed*, in a sentence
or two, with a citation of the Lean Language Reference (`{citep Bib.LLR}[]`), instead of being
pushed back into `IntroL.lean`. `Fin` in `SeaBattle.lean` is the case. `IntroL.lean` presents what
the book builds on repeatedly; a type used in one chapter is better introduced there, next to its
use. The loosening covers types the language already gives us — never a construct this book defines,
and never one that needs more than a short paragraph.

The exception: `IntroCS.lean`, described in that chapter's section below. Everywhere else, a
construct in a code block is one an earlier chapter has presented.

This document is the migration plan: which CSwFP sections each `CSwL` chapter consumes, in which
order, and what each chapter presupposes. The order below is the book's order; the dependency
columns are what justify it. Everything through CSwFP/6 is settled — where a section records a
decision, that decision is made, not proposed. What remains is execution, tracked in [GitHub
issues](https://github.com/cslib-community/CSwL/issues). Exercise-level correspondence with CSwFP is
in `PROVENANCE.md`.

The current state of CSwL need major review to fulfill all decisions from this document.

## Why the order changes at all

CSwFP runs 1, 2 (sets, relations, lambda, types), 3 (Haskell), 4 (syntax), 5 (semantics), 6 (model
checking). That works in Haskell because CSwFP/2 is *pure prose*: nothing in it is mechanised, so it
owes nothing to the chapter that introduces the language. In Lean the same material is mechanisable,
which inverts the dependency and forces the reordering below.

CSwFP/2 also cannot be split cleanly, because its sections form a definitional chain: 2.3 opens
"Functions are relations with the following special property", so it needs 2.2, which needs 2.1; 2.4
opens "We already talked about functions informally", so it needs 2.3; 2.5 builds on the terms of
2.4. The chapter is therefore *dissolved* rather than moved — 2.3, 2.4 and 2.5 into `IntroL.lean`,
2.1 and 2.2 into `Sets.lean`, and the natural-language examples scattered through 2.4 and 2.5 into
`English.lean`.

## Chapter order

*Requires* means the chapter does not stand without it — material it uses that the earlier chapter presents. *Best after* is placement by preference: the chapter would still work earlier, but reads better here. Only the *Requires* column is a constraint.

| # | `CSwL` chapter       | CSwFP sections                                    | Requires | Best after |
|---|----------------------|---------------------------------------------------|----------|------------|
| 1 | `IntroCS.lean`       | 1.1–1.6                                           | —        | —          |
| 2 | `IntroL.lean`        | 3.1–3.10, 3.13; 2.3, 2.4                          | 1        | —          |
| 3 | `Logic.lean`         | 4.4, 4.5, 4.6, 4.7, 5.2, 5.3, 5.5                 | 2        | —          |
| 4 | `Sets.lean`          | 2.1, 2.2                                          | 2, 3     | —          |
| 5 | `SeaBattle.lean`     | 4.1, 5.1                                          | 2, 3     | 4          |
| 6 | `Morphology.lean`    | 3.11, 3.14                                        | 2        | 3          |
| 7 | `InfEngine.lean`     | 4.3, 5.7                                          | 2, 3     | 4          |
| 8 | `English.lean`       | 6.1, 4.2, 6.2, 6.3–6.4; 5.6                       | 2, 3     | 4          |

`Sets.lean` requires `Logic.lean` because its exercises are proofs, and the tactics they need — quantifiers, `cases`, `by_contra` — arrive there. `SeaBattle.lean` requires `Logic.lean` for the same reason: it proves theorems about `WellFormed` by induction on an inductive predicate, which no earlier chapter has the machinery for. `English.lean` required `Sets.lean` while it carried a categorial section interpreting a transitive verb over `Sets.Entity` and `Sets.likesR`. That section is gone (see the chapter's entry below), the chapter declares its own domain, and the import with it: `Sets.lean` is now only *best after*, because the fairy-tale model is built from characteristic functions and that is the representation choice `Sets.lean` makes.

`Morphology.lean` requires only `IntroL.lean` — its three sections are programs, and the proofs in them are `rfl` on concrete values. It is placed after `SeaBattle.lean` rather than at its old position right after `IntroL.lean` so that its exercises may use the tactics `Logic.lean` presents, rather than being confined to what `IntroL.lean` alone allows.

## Reusing Mathlib and CSLib

Reusing Mathlib and CSLib is a declared intention of this project, and contributing back to CSLib is another. So the default is to reuse, and every place where this book defines something a library already has needs a reason. Two such places are recorded here; both are decisions for the chapters through CSwFP/6, and both are revisited in "Beyond CSwFP/6".

What is reused today is modest and worth stating plainly: Mathlib supplies `Set`, `Rel`, `Setoid`, `Finset` and `Fintype` to `Sets.lean`, `List.Chain` to `SeaBattle.lean`, and the tactic library throughout. No chapter imports CSLib yet.

### Propositional logic: why not CSLib's, for now

CSLib has, in `Cslib.Logic.PL`:

- `Proposition Atom` — `atom`, `and`, `or`, `imp`, with `¬A := A → ⊥` and `⊤` as derived notions;
- `Theory.Derivation : Ctx Atom → Proposition Atom → Type` — sequent-style natural deduction, `Finset` contexts, rules `ax`, `ass`, `andI`, `andE₁`, `andE₂`, `orI₁`, `orI₂`, `orE`, `implI`, `implE`, with `Γ ⊢ A` and `T⇓(Γ ⊢ A)` notation;
- weakening, cut and substitution as derived rules; `IsIntuitionistic` and `IsClassical` as *theories*, yielding `byContra`, `lem` and `pierce`.

That is a complete natural deduction system, ready to use, and `PL.lean` does not use it. Three reasons:

1. **It would put a third object in front of the reader at once.** The chapter already has to separate `p ∧ q : Prop` from `Form.conj p q : Form`, and that separation is the section glued to the `inductive`. Adding `Γ ⊢ A ∧ B` makes it a three-way distinction in the chapter where the reader meets all three for the first time. This is a pedagogical cost, not a technical one: CSLib solves the notation clash with a wrapper tag naming the logic (`Modal[m,w ⊨ φ]`), stated as a principle in `Cslib/Logics/README.md`.
2. **The connectives do not line up.** `CSwL`'s `Form` takes `neg`, `top` and `bot` as constructors and derives `impl` and `equi`; CSLib's `Proposition` takes `imp` as primitive and derives negation and `⊤`. Adopting CSLib's type rewrites 4.4, 5.2, 5.3 and every exercise in the chapter; keeping both means maintaining a translation between them. Note that CSLib itself does not insist: its modal chapter declares its *own* `Proposition` rather than reusing the propositional one — precedent for `CSwL` keeping its own `Form` and instantiating the interfaces around it.
3. **CSLib's presentation is minimal logic**, with intuitionistic and classical strength added as *axioms of a theory* rather than as deduction rules. The module itself notes that this differs from most on-paper presentations, and the design is still under discussion upstream. It is a defensible formalisation and an odd first contact with natural deduction for a course that is not about proof theory.

Reasons 1 and 3 are about this book's audience and would not change if CSLib changed. Reason 2 is ours to remove, by taking `imp` as primitive in `Form`; that is the cheapest route into CSLib if the decision is ever reopened.

**What CSLib does not have, and what its house style already prescribes.** There is no semantics for propositional logic — no valuation, no truth tables, no soundness — and no first-order logic at all (`Cslib/Logics/` holds propositional, modal, HML and linear logic). So CSwFP/5.2, 5.3 and 5.5 have nothing to reuse, and the reuse question does not even arise for `FOL.lean`.

The *shape* such a semantics should take is not open, though. CSLib treats proof systems and semantics uniformly, both instantiating `InferenceSystem`, and the modal chapter is the worked example: `Satisfies m w φ` is an ordinary recursive function into `Prop`, bundled as a `Judgement` with `instance : HasInferenceSystem`, and the object/meta bridge is stated as theorems like

    Satisfies.and_iff_and : ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∧ ⇓Modal[m,w ⊨ φ₂]

which is exactly the bridge that `PL.lean` promises, in modal clothing.

Decision: `PL.lean` defines a plain `eval : Valuation → Form → Bool` and states the bridge as ordinary theorems, without the `Judgement` wrapper, the `HasInferenceSystem` instance or a `⇓LP[v ⊨ F]` notation. The course is not about Lean and introduces only what the material needs, and this is the reader's first logic chapter; library machinery there is machinery the book would have to explain. Adopting the shape later is mechanical — `Satisfies` is itself an ordinary recursive function, and the bundling is one structure, one instance and one notation on top of it, with nothing about `eval` changing. Packaging this chapter's semantics for CSLib is a separate deliverable from the book, and belongs in a separate module.

### Grammars: Mathlib's `ContextFreeGrammar`, deferred

`SeaBattle.lean` presents a BNF grammar in prose, and then models it not as a grammar but as a handful of ordinary Lean types: enumerations for the terminal categories (`Colour`, `Answer`, `Column`, `Ship`), a `structure` for each rule with a fixed shape (`Turn`, `Attack`, `Move`), and `List`, `Vector` or a subtype where the BNF recurses or bounds a length (`abbrev Game := List Turn`, `abbrev Guess := Vector Colour 4`, `Reaction := { r : List Answer // r.length ≤ 4 }`).

This flattens the grammar. The BNF rule `game ::= turn | turn game` is recursive; `List Turn` is that recursion already collapsed, and nothing in the chapter connects the two — the correspondence between the displayed BNF and the types below it is asserted in prose and nowhere checked. Sea Battle then adds `inductive WellFormed : Game → Prop` by hand, which is a well-formedness judgement written out because the type alone does not carry it.

Mathlib has `Mathlib.Computability.ContextFreeGrammar`, which models the missing side:

- `ContextFreeRule T N` — `input : N`, `output : List (Symbol T N)`;
- `ContextFreeGrammar T` — a nonterminal type `NT`, an `initial : NT`, and `rules : Finset (ContextFreeRule T NT)`;
- `Produces` (one rewriting step), `Derives` (its reflexive-transitive closure), `Generates`, and `language : Language T`;
- `Language.IsContextFree`, with closure results such as closure under reversal.

The two are not the same object, and the difference is the point. An `inductive` type *is* the parse tree — this holds for `Form` in `PL.lean` and for the `Sent`/`NP`/`VP`/`RCN` fragment in `English.lean`, where a value is a derivation already built and there is no string. `ContextFreeGrammar` is about generating strings: `Derives` is a `Prop`-valued rewriting relation over `List (Symbol T NT)`, and `w ∈ g.language` says a word is generated.

So the library supplies exactly what neither encoding in the book states today:

- that a grammar *generates* a given sentence, as a theorem rather than as a `#eval` — and in `SeaBattle.lean` this is the missing link between the BNF in the prose and the types below it;
- derivation in the grammar sense, a sequence of rewriting steps, which is what a BNF actually describes and what `Derives` is. `SeaBattle.lean`'s hand-written `WellFormed` is a partial substitute for it;
- unique readability, which `PL.lean` gives up precisely because there is no string to disambiguate. Against a `ContextFreeGrammar` there is one again, and the claim recovers its content: that `toString` lands in the language, and is injective.

Deferred all the same, for now. Carrying both representations means giving each grammar twice, which is the duplication this book avoids; `Finset` rules and `Symbol T NT` are heavy machinery for the chapter right after the introduction to Lean; and proving `w ∈ g.language` for a concrete word means building `ReflTransGen` chains, which is real work with no payoff before CSwFP/6. Nothing in CSwFP/1–6 requires it, and the flattened types are what the rest of the chapter computes with.

Taken up after the pending work is done, the natural form is a closing section of `SeaBattle.lean` — one grammar given twice, as the flattened types the chapter computes with and as a `ContextFreeGrammar` value, with the bridge theorem between them — and a back-reference from `PL.lean`'s unique-readability discussion, which is the same question in a different chapter.

## Chapter by chapter

### 1. `IntroCS.lean` — CSwFP/1

Kept in the original presentation and section order. Sections 1.7 (Overview of the Book) and 1.8 (Further Reading) are omitted.

**The one exception to the constraint.** CSwFP/1 has no code; this chapter has some, and all of it uses Lean that `IntroL.lean` only presents later — `example … := by rfl`, a recursive definition matching on `0`/`n + 1`, an `inductive` with `deriving Repr`, and a proof by `induction … with` using `rw`. This is deliberate and stays: the code is there to provoke the reader's curiosity, showing at the outset what the book will be able to say precisely, and the reader is not expected to write it or to follow it in detail.

What makes the exception legitimate is that this chapter *presents* nothing. Every construct it displays is presented properly later, and the prose has to say so at the point where the code appears — that the code will be explained in the chapters that follow, and that reading it now is optional. Without that sentence the chapter is not a teaser, it is an unannounced prerequisite.

The exception is this chapter only, and only for code that presents nothing. It does not extend to later chapters: `Fin`, `Vector` and subtypes are covered by the loosening stated at the top of this document, and `instance` and `mutual` are introduced where the sections above say.

*Migration*: this chapter is to be rewritten as a faithful translation of CSwFP/1, section by section; the current file departs from the original's presentation and organisation. The code stays for now — it is illustrative, and the formalisations in it are slight — but it is not what the chapter is for, and the rewrite decides how much of it survives. Two things are needed either way: the framing sentence, which is not in the prose yet, and the replacement of the chapter's numeric cross-references.

### 2. `IntroL.lean` — CSwFP/3, plus 2.3, 2.4

Presents Lean as a functional programming language. Translated aggressively, adapting to Lean style and primitives.

Scope and order of presentation: terms and types, functions, expressions (`let`, `if-then-else` as terms), `structure`, inductive types, recursion, `List` and polymorphism, `Option`, list processing (`map`, `filter`, `foldl`, `all`, `any`), function composition, type classes, strings, and a closing section on Lean and the lambda calculus. Only what the rest of the book actually uses.

- 3.1 and 3.2 merge into a single section about Lean.
- 3.12 (Identifiers in Haskell) and 3.15 (Further Reading) are omitted.
- 3.13 contributes inductive types and pattern matching; its `Subject`/ `Predicate` example is dropped here, because a fragment of natural language introduced this early collides with the fragments presented later. It is absorbed into `English.lean`.

**2.3 and 2.4 live here; 2.5 does not.** CSwFP presents lambda calculus and types before the programming language, as preliminaries justifying a language the reader has not seen. With Lean already on screen the direction inverts: `#check fun x => x * x` exhibits the lambda abstraction of 2.4, and the closing section gives the term BNF of the lambda calculus with `Lam` as the inductive that mirrors it. The chapter becomes the theory of what the reader has just written.

2.5 — the type BNF `τ ::= b | (τ → τ)` and the three typing rules — was here and is now `English.lean`'s, with the rest of 2.5 that chapter already carries. See the note in its section below.

Two consequences of moving 2.3 here:

- CSwFP defines a *function as a special kind of relation* (2.3), so 2.3 depends on 2.2. In Lean `A → B` is primitive, so the definition is not needed to introduce functions. When relations arrive in `Sets.lean`, "a function is a functional relation" stops being a definition and becomes a statement to prove — new text that CSwFP does not have.
- The linguistic example of 2.4 — lambda abstraction for word formation — is not presented here, because word formation collides with `Morphology.lean`. It is in `English.lean`.
- The demonstration of the typing rules went with 2.5. It had already been adapted once — it read `opaque happy : Entity → Prop`, and `Entity` is declared in `Sets.lean`, which now comes after this chapter, so it became `opaque restful : Day → Prop` over the inductive this chapter declares itself. Whichever entity the rules are demonstrated over in `English.lean`, that constraint no longer applies there.

**`instance` is presented here.** The chapter's "Classes de tipos" section shows type classes only from the *use* side — the `[BEq α]` in a signature, and the difference between `BEq` and `DecidableEq`. But instances are declared from `Logic.lean` onwards: `FOL.lean` gives three, `Repr` for `Variable`, `Term` and `Formula`, and `English.lean` fifteen, all of them `ToString`. Declaring an instance is a small step from the section already there, and it is the last piece of type classes the book actually needs — no chapter declares a `class` of its own.

**`Prop` is no longer presented here.** It once was, minimally — proposition-as-type, proof-as-term, and `rfl`, `intro`, `exact`, `decide` — and the argument was one of necessity rather than preference: inductive types bring `deriving DecidableEq` and `decide`, which display `Prop`, and `SeaBattle.lean` derives `DecidableEq` in its first code block. The student would see `Prop` whether or not it was introduced.

That argument fell with the chapter reordering. `Proof.lean` is now part of `Logic.lean`, the third chapter, and every chapter that displays `Prop` — `Sets.lean`, `SeaBattle.lean`, `Morphology.lean` — comes after it. Nothing meets `Prop` unintroduced any more, so the minimal presentation had no work left to do and went out with the revision. The chapter is left deliberately pre-proof, as the `Logic.lean` section below records.

**Three sections left the chapter in the revision of 2026-09-14.** It had grown to fifteen sections and roughly a thousand lines, and what went out was the material that theorised rather than taught the language:

- *As duas leituras de uma função* — the extensional/intensional distinction, with `funext`. Moved to `Proof.lean`, as the section "Extensionalidade de Funções": `funext` is a tactic, and a chapter that presents no tactics is the wrong home for it.
- *Tipos na gramática e na computação* — the type BNF and the three typing rules, which is 2.5, moved to `English.lean` as recorded above.
- *Tipos como disciplina* — a closing page arguing that "this combination of words is not well formed" and "this program does not typecheck" become the same sentence. It is the book's thesis, not this chapter's content, and it reads better where a grammar is actually being typed.

Only the third was dropped outright; the other two moved. Gone with them: the `leanOutput` blocks throughout, and `#reduce`. The surviving *Lean e o Cálculo Lambda* keeps the term BNF, the `Lam` inductive, β-reduction as what `#eval` does, and variable capture — the part the later chapters draw on. It also keeps `λx ↦ x x`, but as the observation that its reduction loops and that Lean rejects it, without the step-by-step derivation of `σ = σ → τ` that the removed section gave. Recorded because a reader tracing CSwFP/2.4 and 2.5 through this book would otherwise look for these sections and find no note of where they went.

2.6 (Functional Programming) exists in CSwFP to motivate its chapter 3 from its chapter 2 — "functional programming languages actually are lambda calculi". With the order inverted, that bridge is not needed and the section is absorbed.

2.7 (Further reading) is omitted.

### 3. `Logic.lean` — CSwFP/4.4–4.7, 5.2, 5.3, 5.5

Three files: `Proof.lean` (proving in Lean), `PL.lean` (propositional logic)
and `FOL.lean` (predicate logic), included in that order.

Doing logic in Lean is doing deduction — `intro` is →-introduction, `constructor` is ∧-introduction, `cases` on ∨ is ∨-elimination. CSwFP reaches deduction only in its inference engine (5.7); here it arrives with the logic itself. Deduction lives at the meta level, in `Prop` and the tactics.

The chapter could carry a third object: a proof system *as data*, an inductive of derivations `Γ ⊢ A` over `Form`. CSLib already has one, so leaving it out is a decision rather than an omission — argued in "Reusing Mathlib and CSLib" above, and revisited in "Beyond CSwFP/6".

**What is translated and what is written here.** Parts 2 and 3 below are
translations — CSwFP/4.4 for the syntax, 5.2 and 5.3 for the semantics — and
follow the original's structure. Parts 1 and 4 have no source: the first
condenses `logic_and_proof`, the second states a bridge the original cannot
state. Those two carry a structure of their own, and part 1's subheadings, one
per connective, are that structure — a connective's introduction and elimination
rules are what the section teaches.

**The chapter's opening example was not CSwFP's, and is now removed.**
`PL.lean` used to open with a potassium/chlorine example adapted from
Enderton's *A Mathematical Introduction to Logic* — `K` for "traces of
potassium were observed", `C` for "the sample contained chlorine", four
compound sentences, and a truth table over them. It had no counterpart in
CSwFP, whose chapter 4 opens with Sea Battle. It went out with the chapter
reorganization of 2026-09-13: it taught the basics of propositional logic,
which `Proof.lean` now declares a prerequisite, and the chapter's own subject
is formalizing rather than logic itself. The `enderton2001` entry is left in
`Bib.lean`, unused. Recorded because a reader checking coverage might look for
a source passage for the old opening and find none.

**The dresses puzzle moved to `Proof.lean`.** It was a `:::quiz` in `PL.lean`'s
introduction, and the section "Lógica Proposicional em Lean" — now in
`Proof.lean` — formalized it, opening with "Continuando a partir do quiz
anterior". The move broke that reference, so the puzzle goes with the section
that solves it, no longer as a quiz but as the worked example that opens it.

Two divergences inside the translated part. CSwFP gives the semantics in two
sections, "Semantics of Propositional Logic" and "Propositional Reasoning in
Haskell"; here they are one, because the separation does not survive the move:
the definitions are already Lean from the first line, so there is no later point
at which implementation begins. And the discussion of what an empty conjunction
should be worth does not arise, since `top` and `bot` are constructors.

**`Formula.eval` is split in two, so that Exercise 5.12 costs one argument
instead of a second evaluator.** CSwFP's 5.12 asks the reader to reimplement
the semantics with `[String]` for valuations, presence in the list standing for
truth, and its own answer (`Sols`, 5.12) is `altEval` — the whole recursion
written out a second time. Reproducing that here would put two near-identical
six-case recursions in the chapter, which is work for the reader and confusing
to read.

Only the `atom` case of the recursion ever consults the valuation; the other
five combine the truth values of subformulas. So the recursion is
`Formula.evalWith`, which takes the atom lookup as a parameter
(`String → Bool`), and `Formula.eval` is the one-line case that looks the atom
up in the list of pairs. `eval` keeps its signature, so `allVals`, `tautology`,
`satisfiable`, `implies`, `update`, `denote` and every existing exercise are
untouched, and the exercise becomes: define the new lookup, pass it. The cost
is paid in the metatheorem proofs, whose `simp` sets now need `evalWith`
alongside `eval` to reach the constructor cases.

The exercise stops at evaluation and does not ask for `tautology` or
`satisfiable` over the new representation. `genVals` *produces* valuations, and
the analogue for `List String` is the powerset — a genuinely different function,
needing a second parameter threaded through `allVals`. That is where
parameterizing stops being cheaper than duplicating, and it is past what the
exercise is for. `Formula.denote` is left alone for a different reason: it is
about the `Formula`→`Prop` reading, not about how a valuation is represented.

**Proving in Lean is a section of its own, and it comes first.** The meta
level used to be presented three times: `IntroL.lean` introduced `Prop`, and
then `PL.lean` and `FOL.lean` each opened with the tactics for their own
connectives before reaching their actual subject. `Proof.lean` now holds all of
it — `Prop`, what counts as a proof, the tactics as the rules they are
(`apply`; `constructor` and anonymous constructors for ∧ and ↔; `left`, `right`
and `cases` for ∨; `False.elim` and `absurd` for ¬; `by_contra`, `by_cases` and
`em`; `intro`/`apply` for ∀, `use` and `obtain` for ∃), and proof by induction.
`IntroL.lean` is left deliberately pre-proof: it uses `example`, `theorem` and
`rfl` only as the shape an exercise's tests take, and says so.

The consequence is that `PL.lean` and `FOL.lean` now have the same three-part
shape, and neither teaches Lean tactics:

1. **Syntax as data** — BNF, then the `inductive` (4.4 for `Form`, 4.5–4.7 for `Formula`). Glued to it in `PL.lean`, the section that separates the two levels: `Form.conj p q` is data, `p ∧ q` is a proposition. Glued, not deferred — the confusion is born the instant the `inductive` appears. This is a cost Lean creates and Haskell does not have: there the meta level is invisible, living in the prose, so `data Form = ...` cannot be confused with it.
2. **Computable semantics** — 5.2 and 5.3 for `Form.eval` over valuations; 5.5 for `Formula.eval` over a model.
3. **The bridge** — interpreting the syntax into `Prop` (`denote`) and proving that the two readings agree. CSwFP cannot have this section.

**`FOL.lean` gained its bridge section.** It previously had only a `Prop`-valued
`Formula.holds` and no computable semantics at all, so the chapter did not in
fact mirror `PL.lean` — there was nothing to bridge *from*. It now follows the
same shape: `Interp` returns `Bool` and `Formula.eval` computes, `Denot` returns
`Prop` and `Formula.denote` interprets, and `Formula.eval_iff_denote` relates
them. The bridge theorem needs a hypothesis `PL.lean`'s does not: `eval` decides
a quantifier by walking a list `dom`, so it agrees with the `∀` of Lean only
when `dom` lists every element of the domain. That hypothesis is the formal
counterpart of a real limitation, and the prose says so.

**The model in `FOL.lean` is Enderton's, not CSwFP/6's.** Chapter 6's
fairy-tale model (`src/Model.hs`) was pulled forward for a while, to give 5.5
something concrete to evaluate against. It is not any more, for two reasons.

The first is that it belongs to CSwFP/6, which lands in `English.lean`: the
model exists to interpret the English fragment, so presenting it here and again
there would break the rule in `STYLE-WRITING.md` against presenting a
definition that a later chapter rephrases under the same name. It also arrived
unmotivated — ten named entities and eight predicates, several chapters before
anything linguistic.

The second is that the section needs far less. What it teaches is that deciding
a quantifier means walking the domain, and eight predicates do not teach that
better than one does. The model is now the four-vertex directed graph of
{citep Bib.enderton2001}[]: a domain `{a, b, c, d}` and a single binary
predicate `E` with `E = {⟨a,b⟩, ⟨b,a⟩, ⟨b,c⟩, ⟨c,c⟩}`. Four formulas are
evaluated against that one fixed model rather than a fixed formula against
varying predicates, which is the tighter comparison; `d`, isolated, is the
witness that makes `∃x ∀y ¬E y x` true, and Enderton's own remark that the
symbolic version reads more easily than the English one survives the move.

Removing the fairy-tale model also removed the `FOL.Entity` / `Sets.Entity`
name collision that `Sets.lean` carried a dev note about.

**The domain is an `inductive` plus a `List`, and a theorem joins them.**
Declaring four constructors and then repeating them in `vertices` is a
duplication, and a silent hazard: a list that omits a constructor makes `eval`
run over a smaller domain than intended, with nothing to catch it. So the
chapter proves `mem_vertices : ∀ v, v ∈ vertices` by `cases v <;> decide`.
That one line is exactly the `hdom` hypothesis `eval_iff_denote` requires, so
`eval_iff_denote_B` instantiates the bridge theorem on the model with no
hypothesis left to discharge. The completeness of the domain is thereby visible
in the source rather than assumed.

**`Fintype` was considered for this and rejected.** The alternative was to drop
`dom : List D` and decide quantifiers with `[Fintype D]` and
`decide (∀ d : D, …)`. It works — the resulting bridge theorem has no `hdom`
and both quantifier cases close by a bare `simp` — and it is still the wrong
choice, because `Fintype.decidableForallFintype` is *defined* as
`decidable_of_iff (∀ a ∈ Finset.univ, p a)`: a fold over a finite set, walking
every element exactly as `List.all` does. It is the same mechanism with the
hypothesis relocated into an instance where the reader can no longer see it, at
the cost of a type class, a hand-written instance and a duplicated recursion.

Three findings from building it, recorded so the question is not reopened:
`deriving Fintype` fails on this toolchain (`enumList_nodup` type mismatch), so
the instance must be written by hand and repeats the constructors anyway; there
is no computable route from a `Fintype` to a `List` of its elements
(`Finset.univ.toList` and `Multiset.toList` are noncomputable, and
`Finset.univ.val.unquot` is unsafe); and `Fintype Nat` is refutable in one line
(`not_finite Nat`), so that route reaches infinite domains no better than the
list one does.

**One evaluator, parameterized, where CSwFP has two.** CSwFP writes `eval` for
`Formula Variable` and a near-identical `evl` for `Formula Term`, differing
only in how a term is valued. Here `Formula.eval` and `Formula.denote` take
that as a parameter, `tval : Assign D → α → D`, and one definition serves both:
`varVal` for variables, `liftAssign fint` for structured terms. The parameter
takes the assignment and not just the term because the quantifier cases update
`g` and the term valuation has to see the update. This mirrors
`Formula.freeVars`, which the chapter already parameterizes over how to extract
a term's variables, and it leaves `eval_iff_denote` unchanged — same statement,
same proof, now quantified over `α`.

**Two families of validity, because there are two formula types.** CSwFP
states validity and consequence once, for closed formulas of predicate logic,
and never has to say over what the definition ranges — it has no types to
range over. Here `Formula` is parameterized, so the definition has to pick:
`Formula.Valid`, `Formula.Satisfiable` and `Formula.Implies` are stated for
`Formula Variable`, and `Formula.ValidT` and `Formula.ImpliesL` for
`Formula Term`. The pair is not redundant. A structure for a language without
function symbols is `(D, I)`, and for one with them it is `(D, I, F)`; the two
definitions are exactly that difference, and `ValidT` is what makes the third
component visible. The pairing is deliberately incomplete: `Satisfiable` gains
no `Term` counterpart, because nothing in the chapter needs one.

Unifying on `Formula Term` was measured before being rejected. The three
`Variable` definitions are used in 11 places, all inside `FOL.lean` — nothing
in `Sets.lean`, `InfEngine.lean` or any later chapter — and porting the seven
affected proofs is mechanical (`x` becomes `tx`, one extra binder in `intro`,
`liftAssign` for `varVal`); all seven still close. What decided it is the
recurring cost rather than the one-off one. Every counterexample over a
formula without function symbols would have to invent an inert
`FInterp` just to satisfy the signature, and `Formula Term` reintroduces the
unchecked pairing between a quantifier's `Variable` binder and its body's
`Term`s — in `Formula Variable` the two are the same object. Both prices are
paid on every future exercise, not once.

**Consequence from a list of premises.** CSwFP generalizes `P ⊨ C` to
`P₁, …, Pₙ ⊨ C` in the prose between 5.24 and 5.25 without new machinery.
`Formula.ImpliesL` does the same, via `Formula.conjs`, and mirrors
`PL.Formula.impliesL` from the previous chapter — which is likewise an
exercise (`implies-from-list`, CSwFP/5.10) that later exercises then call.

**CSwFP/6.5's `[0..]` becomes a theorem.** The original evaluates over the
infinite domain `[0..]`, relying on Haskell's laziness, and observes that the
procedure "will keep on trying candidates". That cannot be ported: Lean is not
lazy and `[0..]` is not constructible, so the computation cannot even start.
What the chapter says instead is stronger, and proved — `no_list_lists_Nat`
shows `∀ dom : List Nat, ∃ n, n ∉ dom`, so `eval_iff_denote`'s `hdom` is
*unsatisfiable* over `Nat` and no domain list exists to supply. `denote`
meanwhile needs no list, and `forallExistsR_true` proves `∀x ∃y R[x,y]` for any
interpretation reading `R` as `<`. The difference worth stating in the prose is
epistemic rather than a claim of superiority: in Haskell the limitation is
demonstrable, in Lean it is provable.

The helper `le_foldr_max` is proved inline rather than imported. Mathlib's
`List.single_le_sum` needs an `IsOrderedAddMonoid` instance that the chapter's
imports do not carry, and widening them for one side remark costs more than the
five-line induction.

**`Formula` is binary too.** Its `conj` and `disj` take two arguments, with `top` and `bot` as constructors and `Formula.conjs`/`Formula.disjs` recovering the n-ary notation — the same design as `Form`, for the same reason. A constructor holding a `List (Formula α)` would make the type a nested inductive, costing `induction` and `deriving`. The `List α` in `atom name (args : List α)` does not: `α` is a parameter, not the type being defined, so an atom may still take any number of arguments. With that, the definition of truth in 5.5 is a plain recursion, one case per constructor, instead of three mutually recursive functions. The one `mutual` block left in the chapter belongs to `Term`, where a list of terms inside `Term` is what function symbols of arbitrary arity require.

**`mutual` is introduced here.** Its first use in the book's order is `FOL.lean`, and `English.lean` then uses it six times over for the fragment's mutually recursive categories. A note right after that first block — why a group of types that refer to one another has to be declared together, and what `mutual` therefore does — is enough; it does not need a section of its own, and it does not belong in `IntroL.lean`, where nothing would motivate it.

**What is taken from `logic_and_proof`.** Only the chapters that teach *proving in Lean*; the ones that present logic on paper are already CSwFP's job, and covering the same ground twice is exactly the duplication this book avoids. Reference: <https://leanprover-community.github.io/logic_and_proof/>.

| `logic_and_proof` chapter                   | Taken                                                                                |
|---------------------------------------------|--------------------------------------------------------------------------------------|
| `propositional_logic`                       | no — CSwFP/4.4 and 5.2 do this                                                       |
| `natural_deduction_for_propositional_logic` | the rule names only, to present each tactic as the rule it is                        |
| `propositional_logic_in_lean`               | yes, condensed — this is the core of `PL.lean`'s first section                       |
| `classical_reasoning`                       | yes — needed for the two-valued valuation of 5.2, and for `Sets.lean`'s Exercise 2.3 |
| `semantics_of_propositional_logic`          | no — CSwFP/5.2 and 5.3 do this                                                       |
| `first_order_logic`                         | no — CSwFP/4.5–4.7 do this                                                           |
| `natural_deduction_for_first_order_logic`   | the rule names only                                                                  |
| `first_order_logic_in_lean`                 | yes, condensed                                                                       |
| `semantics_of_first_order_logic`            | no — CSwFP/5.5 does this                                                             |

`sets_in_lean` and `relations_in_lean` are the corresponding reference for `Sets.lean`, not for this chapter.

**Representation note.** 5.5 is prose in CSwFP — a model is `M = (D, I)` with `I(P) = {1,3}` and `I(R) ⊆ D²`, and the text points back at the Cartesian product of 2.2. Mechanised here, before `Sets.lean` exists, the interpretation is represented by function types (`D → Prop`, `D → D → Prop`), which `IntroL.lean` already provides. This is also what CSwFP itself does once it writes code: `Model.hs` uses `type OnePlacePred = Entity -> Bool`. Mathlib's `Set` and `Rel` are deliberately *not* used here; they arrive in `Sets.lean`.

**Two syntactic results of 4.4 change content, not just position.** Structural induction is not a theorem to state — it is the recursor that `inductive` generates.

Unique readability is the other. In CSwFP it is a claim about *strings*: a formula written out as a sequence of symbols has exactly one parse tree, so the notation is unambiguous. In Lean there is no string to disambiguate — a term of type `Form` already *is* the tree, and `Form.conj p q` cannot be read two ways. The claim has nothing left to assert.

Decision: `PL.lean` does not state unique readability as a theorem. What it states instead is what survives the translation — that the constructors are injective and pairwise disjoint, provable by `injection`, which is what Exercise 4.11 already does. The prose says why the original statement dissolves: the ambiguity it rules out is a property of writing formulas down, and the type never writes them down. Recovering the original claim would take a string to disambiguate — either a parser `String → Option Form` with a round-trip theorem, or the grammar stated as a `ContextFreeGrammar` so that `toString` can be shown to land in its language and to be injective. Both are deferred for the same reason: parsing and grammars-as-data are topics of their own, and nothing before CSwFP/6 needs either. See "Reusing Mathlib and CSLib"; it is the same question this chapter and `SeaBattle.lean` both run into.

### 4. `Sets.lean` — CSwFP/2.1, 2.2

What is left of CSwFP/2 after 2.3, 2.4 and 2.5 moved to `IntroL.lean` and `English.lean`: sets and relations. Renamed from `Foundation.lean`, which promised a foundations chapter that no longer exists. `Sets` covers both halves honestly, because CSwFP/2.2 *defines* a relation as a subset of A × B — a relation is a set — and because what the chapter adds in Lean is precisely the representation choice for `Set α`.

**What the chapter is.** Sets and relations are presupposed notation from CSwFP/1 onwards, as in any mathematical text — which is why 5.5 can speak of `I(R) ⊆ D²` before this chapter exists. This chapter is where they are *mechanised in Lean*, and its opening has to say so, or it promises the wrong thing. That is also what makes it worth having: Lean forces representation choices — `Set α` vs. the predicate `α → Bool` vs. `Finset`, `Rel` vs. a list of pairs, decidability — and those choices determine how the fairy-tale model of `English.lean` is built.

**Why after `Logic.lean`.** Nothing downstream requires this chapter — no later chapter fails to compile without it — but the chapter itself requires `Logic.lean`, and that is what fixes its position. Both reasons are about the exercises:

- The chapter's point in Lean is *proving* theorems about sets and relations, which needs quantifiers and the connective tactics. `IntroL.lean`'s minimal `Prop` does not reach them; `Logic.lean` does.
- CSwFP's Exercise 2.3 is "check that A̿ = A". In Lean one direction requires classical reasoning (`¬¬P → P` does not hold constructively). Placed early, the third exercise of the book would force a conversation about the nature of negation before any truth table exists. After `Logic.lean`, `by_contra` and `em` are already presented and the exercise is routine.

`Logic.lean` must therefore not use `Set` or `Rel` — see the representation note above.

From the `logic_and_proof`, the chapters `sets_in_lean` and `relations_in_lean` can give some exercises or ideas on how to present sets and relations in Lean.

### 5. `SeaBattle.lean` — CSwFP/4.1, 5.1

Syntax and semantics are presented one after the other, instead of split across two chapters: 4.1 for the grammar, 5.1 for the state-transition semantics.

The grammar here is flattened into ordinary types — enumerations, `structure`s and `List` — rather than given as a value of Mathlib's `ContextFreeGrammar`; that is a decision, argued in "Reusing Mathlib and CSLib" above.

**`Fin` is introduced here, not in `IntroL.lean`.** It is one of Lean's own basic types, needed by this grammar and nowhere else: `Fin 10` for a board row. `DEVIATIONS.md` states this as a general loosening of "presented" — a type needed in exactly one place is introduced where it is used.

**The chapter comes after `Logic.lean` and `Sets.lean`.** Its exercises prove theorems about `WellFormed` by induction on an inductive predicate, which needs the tactics `Logic.lean` presents. Placing it earlier would mean either weaker exercises or a chapter that uses what the book has not shown.

**Mastermind was removed.** CSwFP/4.1 carries the syntax of two games and 5.4 gives Mastermind's implementation, and an earlier arrangement of this book had both. It is dropped: the section was disconnected from the Sea Battle material that preceded it, and it announced a semantics in propositional logic that it never delivered — 5.4 opens by calling itself an application of propositional logic, but the propositional content is about eighteen lines that the implementation never uses. Reinstating Mastermind would mean writing that encoding rather than translating it. `PROVENANCE.md` records the exercises that went with it.


### 6. `Morphology.lean` — CSwFP/3.11, 3.14

`Applications` is too vague a name; the chapter is about morphology. Section 3.11 is split into two sections, `FinnishVowelHarmony` and `SwedishPlural` (CSwFP covers Swedish plural inside 3.11, pp. 54–55). Section 3.14 becomes `Phonemes`.

A short introduction should note that although the book is not about morphology, these examples exercise the Lean concepts just learned.

*Migration*: check that every Lean feature used here was presented in `IntroL.lean`.

### 7. `InfEngine.lean` — CSwFP/4.3, 5.7

The language for talking about classes (4.3) and the inference engine over it (5.7), together instead of split across two chapters.

4.3 is literally about classes, which is what makes it the chapter immediately after the one that mechanises them:

| 4.3 fragment         | 2.1 vocabulary |
|----------------------|----------------|
| `All PN are PN`      | `A ⊆ B`        |
| `No PN are PN`       | `A ∩ B = ∅`    |
| `Some PN are PN`     | `A ∩ B ≠ ∅`    |
| `Some PN are not PN` | `A \ B ≠ ∅`    |

CSwFP's `derive kb stmt` is proof search over syllogisms. Read as deduction over set inclusion, the validity of the syllogisms becomes provable in Lean — where CSwFP can only implement and test it.

This chapter is independent of the English fragment: `InfEngine.hs` imports nothing from the syntax module.

**What is translated and what is written here.** CSwFP/4.3 and the theory in 5.7 — Aristotle, the square of opposition, the knowledge base as inclusion and non-inclusion, the inference rules — are translated, and so is the engine: `rSection`, relational composition, the reflexive-transitive closure, `subsetRel`, `nsubsetRel`, `derive` and `tellAbout`. The closing section, which proves the syllogisms valid over `Set`, has no source: it is the payoff the plan promises, and the reason the chapter sits after `Sets.lean`.

Three divergences. The least fixed point is computed with a fuel bound rather than by iterating until the value stops changing, because the latter has no structural termination argument; the bound is the square of the domain size, which is beyond what the closure can need. Relations are `List (α × α)`, named `Relation` rather than `Rel`, so that Mathlib's `Rel` — which `Sets.lean` introduces and this chapter's closing section uses through `Set` — keeps its name. And CSwFP/5.7's natural-language *input* is not ported: the parser, the file I/O and the `chat` loop are the only place in the book that would need `IO`, and the chapter states its interface through `ToString` on `Statement`, which is the output half.

### 8. `English.lean` — CSwFP/6.1, 4.2, 6.2, 6.3–6.4

The chapter has four sections, in this order: 6.1 (linguistic form and translation into logic), 4.2 (the fragment of English), 6.2 (predicate logic as representation language), and 6.3 together with 6.4 (the model, and evaluation in it). The order is forced. CSwFP/6.2 translates the 4.2 grammar category by category — the text says so, and `MCWPL.hs` imports the syntax module and opens with `lfSent :: Sent -> LF` — so the grammar has to exist first. 6.1 is the argument that motivates the translation at all, so it opens the chapter.

**CSwFP/2.4, 2.5 and 3.13 are no longer here.** Earlier drafts carried the `likes` example of 2.4, the `Subject`/`Predicate` example of 3.13, and all of 2.5 — the type BNF `τ ::= b | (τ → τ)`, the three typing rules, and a categorial section that named the semantic types `e` and `t` (so as not to collide with the `inductive`s that *are* the syntactic categories) and interpreted a transitive verb over `Sets.Entity` and `Sets.likesR`. The rewrite of 2026-09-20 dropped all of it. CSwFP/6.1 makes the same point that section made — *Goldilocks* translates not as the constant `g` but as `λP ↦ P g`, "a function from properties to truth values", and *no one* has the same type — and making it twice, once as an informal argument and once over Lean types, is the fragmented presentation the writing guide rules out. `adjective-types` (CSwFP/2.17) went with that section; `PROVENANCE.md` records it. The chapter no longer imports `CSwL.Sets`.

**Totality changes the inventory.** Haskell lets a translation function be partial, and `MCWPL.hs` uses that licence four times: `lfDET` has no clause for `Most`, `lfRCN` none for `RCN3` (the adjective rule), `lfTV` none for `Caught`, and `lfNP` none for `Everyone`/`Someone`. A Lean function has to be defined everywhere, so each gap is a decision:

- **`most` is not in `DET`.** CSwFP's own 4.2 grammar does not have it either; it is in the Haskell data type and then goes untranslated, because — as 6.2 says — *most* has no first-order translation at all. Keeping it would mean either a false translation or making `lfDET` return `Option LF`, which turns every function in the family `Option`-valued and buries the linguistics in plumbing. The limitation is stated in the prose instead, where 6.2 states it. `a` goes the other way: CSwFP's `data DET` does not have it, but 6.2's prose lists it among the five determiners it treats, and the preposition-phrase exercise needs *a dwarf*, so `DET` carries it.
- **`AV`, `To`, `INF` and `TINF` are not in the grammar.** CSwFP throws them in "for purposes of illustrating intensionality" in a chapter this book does not plan, and 6.2 gives them no translation. They are also the one part of the 4.2 fragment that CSwFP/6 never needed.
- **`ADJ` stays, and is translated intersectively.** `RCN` uses it, and *happy* and *evil* — CSwFP/4.6, absorbed into the presentation — really are conjunctive: a *happy wizard* is happy and a wizard. *Fake* is not, and the prose says so: the translation exists because the function must be total, not because it is right.
- **`caught` gets an atom like every other transitive verb.** The model does not interpret it, so every sentence using it is false; the prose points at this, since `FOL.lean` already established that an uninterpreted symbol evaluates to `false`.

**The grammar is extended by wrapping, not by redeclaring.** CSwFP/4.7 and 4.8 ask the reader to extend the fragment, and in Haskell the answer is to rewrite the whole `data` group. An `inductive` is closed in the same way, but a mutually recursive group does not have to be redeclared to be extended: a *new* category that contains the old one — `| base (np : NP)` — plus the constructors for the new rules does the job, and the functions already written over the old types keep working. The chapter presents the technique on sentence coordination (`SentAnd`, three lines) and both exercises apply it. Two consequences, neither hidden: the extension is not recursive, so a prepositional phrase cannot contain another one and a coordinated relative clause cannot contain a coordinated relative clause; and the new constructors are shaped so that they never overlap with the old ones, or the extended grammar would derive the *unextended* sentences twice, which would wreck an exercise about counting derivations.

The distinction the chapter draws is between adding a *word* and adding a *rule*. Adding a word is adding a constructor to a leaf category, and no wrapping reaches it, so the lexicon is complete from the declaration — which is why CSwFP/4.6 is absorbed rather than set as an exercise.

**Naming.** The constructors are `npDet`, `npDetRel`, `rcnSubj`, `rcnObj`, `rcnAdj`, `vpTrans`, `vpDitrans`, not `NP1`, `NP2`, `RCN1`, `RCN2`, `RCN3`, `VP1`, `VP2`. The numbers are positions in a Haskell `data` declaration and say nothing; `rcnSubj` and `rcnObj` say which position the relative clause's gap is in, which is the distinction the coordination exercise turns on.

**The model.** CSwFP/6.3's fairy-tale model arrives here, next to the grammar it interprets, rather than in `FOL.lean` — the reason is in the `Logic.lean` section above. Three differences from `Model.hs`. Predicates are `Entity → Bool` and built from lists, as in the source, but `admire` and `defeat` are written as the conditions they are (`person x && y == .G`, `dwarf x && giant y || …`) rather than as list comprehensions over `entities`, which in Lean would say the same thing at more length. `Unspec` is the default of the `FInterp`, which makes the function total in the one way that is linguistically meaningful — an unnamed constant denotes an unspecified entity. And the interpretation agrees with the translation on names and argument order: `MCWPL.hs` emits `Atom "love" [subj, obj]` while `int0` keys on `"Love"` and reverses the arguments, so the two halves of the source never actually meet.

**6.4 is absorbed rather than ported.** Everything it builds — the interpretation function, variable assignments, `change`, `eval` — is already in `FOL.lean` as `Interp`, `Assign`, `Assign.update` and `Formula.eval`. What is left for this chapter is the model itself and the two-step procedure, `checkSentence`, which is CSwFP/6.7.

**CSwFP/5.6 is present only as an exercise.** Its content is a translation key from lexical items to predicate letters, which 6.2 supersedes by computing the translation. Its Exercise 5.27 — four sentences of the fragment to translate — survives as `fragment-translations`.

### 9. CSwFP/6 — where it lands

Sections 6.1–6.4 are in `English.lean`, as the section above describes. Section
6.5's structured-term evaluation and its `[0..]` discussion are in `FOL.lean`:
they are about the evaluator rather than about the fragment, and the chapter
that defines `Term` is where they belong. Section 6.6 (Further Reading) is
omitted.

**There is no `ModelChecking.lean`.** The plan once called for one, and older
notes in this file use that name for CSwFP/6's content; they should be read as
naming the content, not a file. The reason it belongs with the English
fragment is that it is built on that fragment, so the two are one development
rather than two.

What this means for `FOL.lean` is recorded in the `Logic.lean` section above:
the fairy-tale model of 6.3 is *not* pulled forward into it. It arrives with
the grammar it interprets, and `FOL.lean` evaluates against Enderton's
four-vertex graph instead.

This is also why `Sets.lean` reads best just before `English.lean`, though it
is not required: `Model.hs` builds the model with `OnePlacePred = Entity ->
Bool` and `list2OnePlacePred xs = \x -> elem x xs` — the characteristic
function of 2.3 and the set-as-predicate of 2.1, applied. The choice between
`Set Entity` and `Entity → Bool` is exactly the one `Sets.lean` makes.

## Omitted throughout

All "Further Reading" sections (1.8, 2.7, 3.15, 4.8, 5.8, 6.6), 1.7 (Overview of the Book), and 3.12 (Identifiers in Haskell).

## Beyond CSwFP/6

Everything above is settled and covers CSwFP/1 to CSwFP/6. The rest of the book is deferred, and the placements below are provisional, not decisions.

CSwFP/7 (The Composition of Meaning in Natural Language) goes after `English.lean`. It continues that chapter's fragment and, in CSwFP, builds on the same syntax module, so the constraint that puts the fragment before CSwFP/6 keeps 7 downstream of both. How much of `English.lean` it absorbs — CSwFP/7 is where a consolidated semantics of a natural-language fragment actually appears — is the question to settle when that chapter is taken up.

A proof system as data — CSLib's `Cslib.Logic.PL.Theory.Derivation` — is deferred rather than rejected, for the reasons in the `Logic.lean` section. It becomes attractive exactly where `CSwL` would have something to give back: CSLib has the derivations but no propositional semantics, and this book builds the valuation. Soundness — every derivable sequent is true under every valuation satisfying its context — needs both halves, and neither project has both today. `Cslib/Logics/README.md` invites exactly this ("we are interested in expanding them or creating new ones that can cover your use cases"). Its natural place is after `Sets.lean`, once relations and quantifiers are available. It stays out of the plan until CSwFP/1–6 are in place.

Mathlib's `ContextFreeGrammar` for the grammar of `SeaBattle.lean` is deferred on the same footing, and for reasons that are ours rather than the library's — see "Reusing Mathlib and CSLib". It is the one deferred item that would change a chapter already written, so it belongs after the pending work already tracked, not before it.

The related question — whether `PL.lean`'s valuation is written in CSLib's shape from the start — is settled above, and settled against it.

Chapters 8 onwards are not planned yet.
