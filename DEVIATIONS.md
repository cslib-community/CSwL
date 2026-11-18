# How CSwL departs from CSwFP

`CSwL` reorders CSwFP so that the presentation is natural in Lean.
`CSwFP.yaml` says where each CSwFP section and exercise went. This
file records the decisions behind that, as they stand now; how they
were reached is in the git history and the pull requests. The rules
the decisions serve are in `STYLE-CODE.md` and `STYLE-WRITING.md`.

## Chapter order

CSwFP runs sets, lambda calculus and types (2) before Haskell (3). That works
because its chapter 2 is prose. In Lean the same material is code, so the
language has to come first, and chapter 2 is split: 2.3 and 2.4 into
`IntroL`, 2.1 and 2.2 into `Sets`; 2.5 is dropped.

| Chapter      | Requires  | Why                                                                         |
|--------------|-----------|-----------------------------------------------------------------------------|
| `IntroCS`    | —         |                                                                             |
| `IntroL`     | `IntroCS` |                                                                             |
| `Logic`      | `IntroL`  |                                                                             |
| `Sets`       | `Logic`   | its exercises are proofs, and 2.3 needs classical reasoning                 |
| `SeaBattle`  | `Logic`   | its exercises prove theorems by induction on `WellFormed`                   |
| `Morphology` | `IntroL`  | placed here so that its exercises may use tactics                           |
| `InfEngine`  | `Sets`    | the language of 4.3 is about sets, and the syllogisms are proved over `Set` |
| `ModelChecking` | `Logic` | it translates into `FOL`'s `Formula` and evaluates with its `eval`; best after `Sets`, whose characteristic functions build the model |

CSwFP/6 is in `ModelChecking`: it is built on the fragment of 4.2, whose
categories it translates one by one. 

## Reusing Mathlib and CSLib

The default is to reuse. What is reused today: `Set`, `Rel`, `Setoid`,
`Finset` and `Fintype` from Mathlib in `Sets`, `List.Chain` in `SeaBattle`,
and the tactic library. No chapter imports CSLib yet.

- **CSLib's propositional logic is not used.** It would put a third object,
  `Γ ⊢ A`, next to `Formula` and `Prop` in the reader's first logic chapter;
  it takes `imp` as primitive where `Formula` takes `neg`; and it presents
  minimal logic, with classical strength as axioms of a theory. CSLib has no
  semantics for propositional logic and no first-order logic, so 5.2, 5.3 and
  5.5 have nothing to reuse.
- **`PL` defines a plain `eval` and states the bridge to `Prop` as ordinary
  theorems**, not in CSLib's `Satisfies`/`HasInferenceSystem` shape. Adopting
  the shape later is one structure, one instance and one notation on top of
  `eval`, and belongs in a separate module.
- **Mathlib's `ContextFreeGrammar` is deferred.** `SeaBattle` models its BNF as
  ordinary types, and nothing checks that the types match the grammar. The
  library would supply that link, derivations, and unique readability for
  `PL`. It would also mean giving each grammar twice and proving membership by
  building `ReflTransGen` chains. The natural place is a closing section of
  `SeaBattle`. Exercises 4.11, 4.15, 4.16 and 4.21 wait on it.
- **A proof system as data** (CSLib's `Derivation`) is deferred, not rejected.
  Soundness needs CSLib's derivations and this book's valuations together.
  Its natural place is after `Sets`, once CSwFP/1–6 are in place.

## Inconsistencies found in CSwFP

Porting CSwFP turned up inconsistencies in it. Some were found by
reading, when two passages disagree; others were forced into view,
because Lean checks things that Haskell lets pass, such as total
functions and exhaustive pattern matches. They are recorded here,
with what was done about them.

- **The empty parse tree `Ep` (CSwFP/9).** `ParseTree` has three
  constructors, `Ep | Leaf a | Branch b [ParseTree a b]`, but `Ep` is
  built in one place only: `epsilonT = succeed Ep`, used only by the
  palindrome parser of 9.3, for the rule `A → ε`. The palindrome
  parser of 9.2, for the same grammar, gives the empty word the leaf
  `Leaf "[]"` instead, so the two parsers return different trees for
  the same word. Both also give `A → a` a bare leaf, while every other
  rule gets an `A` node. After 9.3, `Ep` never occurs: the gaps of 9.7
  are leaves with a special category, and `t2c` and `assignT` (9.6) and
  the interpretation functions of chapter 12 (`dintTXT`, `dintNP`, …)
  match only `Leaf` and `Branch`. Haskell accepts these partial
  functions; Lean does not, so keeping `Ep` would cost every function
  on trees a case for a tree that never occurs. CSwL drops `Ep` and
  `epsilonT`, gives every rule used an `A` node in both parsers
  (`A → ε` gives a node with no children), and makes `subtree`, which
  was CSwFP's other partial function on trees, return an `Option`.
  Discussed in issue #51.
- **Two definitions of c-command (CSwFP/4.5 and 9.1).** Section 4.5
  defines binding through c-command: a node `a` c-commands `b` if the
  first branching node above `a` dominates `b`, with dominance
  reflexive (`a = b` "in the limit case"). Section 9.1 defines
  c-command as sisterhood composed with dominance, again reflexive:
  `p` c-commands `q` if a sister of `p` dominates `q`. The two
  disagree in two ways. By 4.5, a node c-commands itself, its
  descendants and its mother, since the first branching node above it
  dominates all three; by 9.1 it c-commands none of them, which is
  what parts (1) and (2) of exercise 9.2 say. And a node with no
  sister c-commands nothing by 9.1, but by 4.5 it c-commands what the
  first branching node above it dominates: in the tree of 9.1, the
  leaf `Snow White`, only daughter of the subject `NP`, c-commands
  every node by 4.5 and none by 9.1. Three further problems: (a) 4.5
  says that `∀x` binds an occurrence of `x` when it c-commands `x`,
  but in the syntax tree drawn there `x` is not a node, only part of
  the atoms `Px`, `Qx` and `Rxy` that are leaves; (b) part (3) of
  exercise 9.2, "the lowest branching position that dominates `p`
  also dominates `q`", is false with reflexive dominance: in the tree
  of 9.1, the `VP` c-commands the subject, but the `VP` branches, so
  the lowest branching position that dominates it is the `VP` itself,
  which does not dominate the subject; the official solution has the
  same gap; (c) neither definition is the standard one of the
  syntax literature (Haegeman 1994, as in the Wikipedia article on
  c-command): `a` c-commands `b` if neither dominates the other and
  the lowest branching node that properly dominates `a` dominates
  `b`. That definition agrees with 9.1 except on nodes with no
  sister, and with it exercise 9.3 fails: in the tree of 9.1, the
  leaf `Snow White` and the `VP` c-command each other without being
  sisters. The Wikipedia article is itself split: its opening sentence
  and its worked example follow the sister definition of 9.1. CSwL
  adopts the sister definition throughout. In `Logic/FOL`, a `details`
  block replaces the binding passage of 4.5: it draws the syntax tree,
  says that `∀x` binds the occurrences of `x` in the atomic formulas
  below its sister, names that relation c-command, and points to
  `Parsing`. `Parsing/ParseTrees` ports 9.1 as `cCommand`, and
  exercise 9.2 becomes three theorems: parts (1) and (2), and part (3)
  with proper dominance, as "the mother of `p` dominates `q`". The
  new exercise `c-command-variants` asks for the definition of 4.5 and
  the standard one of the Wikipedia article, and checks on a tree with
  a node with one daughter (the tree of the article) where the three
  disagree. The prose describes the 4.5 definition without naming its
  source, as `STYLE-WRITING.md` requires.

## By chapter

Where a CSwFP section went, and why, is in `CSwFP.yaml`. What follows are the
decisions inside the chapters.

### `IntroL`

- `instance` is presented here: later chapters declare instances, and no
  chapter declares a `class`.
- `Prop` is not: `Logic` presents it, and every chapter that shows `Prop`
  comes after `Logic`. `IntroL` uses `example` and `rfl` only as the shape of
  an exercise's tests.

### `Logic`

- **`PL` and `FOL` have the same three parts**: syntax as an `inductive`, a
  computable semantics, and the bridge that interprets the syntax into `Prop`
  and proves the two readings agree. The bridge has no source.
- `Formula` is binary in both files, with `conjs`/`disjs` for the n-ary
  notation. A constructor holding a `List Formula` would make the type nested,
  costing `induction` and `deriving`. `mutual` is introduced in `FOL`, for
  `Term`.
- Structural induction is the recursor `inductive` generates. Unique
  readability is not stated: a term of `Formula` is already a tree, so there is
  no string to disambiguate.
- The domain of the model in `FOL` is an `inductive` plus a `List`, joined by
  `mem_vertices`, which discharges the hypothesis of the bridge theorem.
  `Fintype` does not replace the `List`: its quantifier instance is the same
  walk hidden in an instance, `deriving Fintype` fails on this toolchain, and
  no computable route leads back to a `List`.
- One `eval` serves `Formula Variable` and `Formula Term`, taking the term
  valuation as a parameter, where CSwFP has two evaluators.
- Validity comes in two families, `Valid`/`Satisfiable`/`Implies` for
  `Formula Variable` and `ValidT`/`ImpliesL` for `Formula Term`: a structure
  without function symbols is `(D, I)`, with them `(D, I, F)`.
- A model in `FOL` interprets predicates as functions (`D → Prop`), not with
  `Set` or `Rel`, which arrive in `Sets`.
- `no_list_lists_Nat` proves that no list covers `Nat`, so the bridge
  hypothesis cannot hold over `Nat`.

### `InfEngine`

- The least fixed point is computed with a fuel bound, the square of the
  domain size, since iterating to a fixed point has no structural termination
  argument.
- Relations are `List (α × α)`, named `Relation` so that Mathlib's `Rel` keeps
  its name.
- The closing section, which proves syllogisms valid over `Set`, has no source.

### `ModelChecking`

- The sections are 6.1, 4.2, 6.2, and 6.3 with 6.4. 6.2 translates the 4.2
  grammar category by category, so the grammar comes first; 6.1 motivates the
  translation, so it opens the chapter.
- A Lean function is total, so the gaps `MCWPL.hs` leaves are decisions:
  - `most` is not in `DET`: it has no first-order translation, as 6.2 says,
    and the prose states the limitation. `a` is in `DET`, since 6.2 treats it.
  - `AV`, `To`, `INF` and `TINF` are not in the grammar: they illustrate
    intensionality, and 6.2 gives them no translation.
  - `ADJ` is translated intersectively. That is right for *happy* and *evil*,
    not for *fake*, and the prose says so.
  - `caught` gets an atom like every transitive verb. The model does not
    interpret it, so every sentence using it is false.
- The grammar is extended by wrapping, not by redeclaring: a new category
  containing the old one (`| base (np : NP)`) plus the new rules. The chapter
  shows it on sentence coordination, and the exercises of 4.7 and 4.8 use it.
  The extension is not recursive, and the new constructors never overlap with
  the old ones.
- Constructors are named for what they are (`npDet`, `rcnSubj`, `rcnObj`,
  `vpTrans`), not numbered (`NP1`, `RCN2`).
- The fairy-tale model of 6.3 is here, next to the grammar it interprets.
  Predicates are `Entity → Bool`; `admire` and `defeat` are written as
  conditions rather than list comprehensions; `Unspec` is the default of the
  `FInterp`; and names and argument order agree with the translation, which
  in the Haskell source they do not.

### `Composition`

CSwFP/7 continues the fragment of `ModelChecking` and builds on the same
syntax and model, so it comes after `ModelChecking`. Being written.

- The chapter summary is translated as the chapter's opening, with Lean in
  place of Haskell as the lambda-calculus engine of `ModelChecking`.
- In the opening of 7.2, the paragraph observing that the translation of
  *Every prince sang a ballad* has no sub-expression for its noun phrases, and
  the one on quantified noun phrases as "systematically misleading
  expressions", are cut to a one-sentence reminder: `ModelChecking`'s
  `english-form` already makes both points, at more length.
- Example (7.4), *Every mermaid hummed a song*, becomes *Every dwarf defeated
  a giant*: mermaids, songs and humming are not in `ModelChecking`'s fragment
  or model, and the new sentence can be evaluated there with `#eval`.
- The tree of numbers is not an infinite list, since Lean is not lazy: `tree
  k` is the list of rows `0` to `k`, and `treeOfNumbers k` (exercise 7.1) and
  `genTree q k` (exercise 7.3) take the same bound. Both are written over
  `tree`, so exercise 7.3 does not depend on the solution of 7.1.
- Figures 7.5 and 7.6 are computed: `numberTree` and `patternTree` label the
  same `tree k`, one with the pairs and one with `+` and `-`.
- Subsections "Numerical Trees" and "Logical Representations for
  Quantifiers" keep one cast of examples, the quantifiers of exercise 7.2 and
  Figure 7.6, announced at the start. So CSwFP's `atleast2butnotall` becomes
  `atLeast3ButNotAll`, *at least three but not all*.
- In "Relational Properties", CSwFP calls *some* reflexive. With its own
  definition, `∀X Q XX`, it is not: `Q ∅ ∅` is false, the top of the tree
  pattern. The book keeps the definition and makes the empty set the point,
  in exercise `some-not-refl` and in the quiz on irreflexivity.
- Each relational property is defined twice, over sets (`GQ.Refl`,
  `GQ.MonUp`, …) and over the tree (`ReflNum`, `MonUpNum`, …). That the two
  versions agree is stated, not proved: the proof goes from sets to
  cardinalities through EXT, CONS and ISOM.
- Exercises 7.5 and 7.6 become quizzes, because their answers, the tree
  forms of MON↑ and MON↓, are the definitions `MonUpNum` and `MonDownNum`
  that exercises 7.7–7.10 use. Exercises 7.8 and 7.9 are split by
  operation, `mon-and` and `mon-or`, each with both directions.
- CSwFP's `Quant` is `ListQuant`, in parallel with `NumQuant`, and takes the
  universe before the property, `List Nat → (Nat → Bool) → Bool`, so that
  `List.all` and `List.any` have the type as they are. `toNum` turns a
  `ListQuant` into a `NumQuant` at the start of "Logical Representations for
  Quantifiers", which CSwFP leaves implicit, so that the patterns of
  `List.all` and `allNum` can be compared.
- Of "Quantifiers, Automata, and Definability" only the words are
  implemented: `wordOf`, `langOf q` as a Mathlib `Language Bool`, the
  theorem that it is closed under permutation, and the operations
  `notNum`, `andNum` and `orNum` as complement, intersection and union
  (with *all* as `{[true]}∗`, CSwFP's `1∗`). The automata are deferred,
  not dropped (issue 41): until then, they, van Benthem's
  characterization and the definability of *most* are in the cues only,
  and exercises 7.11 and 7.12 wait for them.
- 7.3 and 7.4, the language of typed logic and the reduction of its
  expressions, are dropped, with their exercises 7.13–7.22. Lean is the
  typed logic: its types, lambda terms and evaluation are what `IntroL`
  presents with the lambda calculus of 2.4, and Lean reduces and substitutes
  for the reader. No later section handles terms as data. CSLib's lambda
  calculi were considered for 7.4 and do not fit: the named one is untyped,
  and the typed one is locally nameless, without constants.
- CSwFP changes the argument order of transitive verbs between 7.5 and
  7.6: the rule for VP → TV NP in 7.5 applies the verb to the object first,
  `λx ↦ ⟦NP⟧ (λy ↦ ((⟦TV⟧ y) x))`, and the code of 7.6 to the subject
  first, `intTV tv subj obj`, without comment. Both sections here follow
  7.6 and the model, whose relations take the subject first.
- The semantic rules of 7.5 are Lean functions in namespace `Rule`, named
  after the grammar constructors they interpret (`Rule.vpTrans` for
  `VP.vpTrans`). The chain of β-reductions for *Alice admired Dorothy* is
  the theorem `alice_admired_dorothy`, proved by `rfl` for any relation in
  place of *admire*, and exercise 7.24 asks for the same.
- In 7.6, `intSent`, `intNP`, `intVP` and `intRCN` apply the semantic
  rules of 7.5, one line per constructor. *Most* and the *at least* /
  *at most* of exercise 7.25 are meanings only, used through `Rule`:
  CSwFP adds them to `DET`, which here would mean wrapping `NP`, `VP`,
  `RCN` and `Sent` too (issue 42). The adjectives and *caught* are false
  of everything, as in `ModelChecking`'s model. An `#eval` checks that
  the direct interpretation agrees with the translation into a formula
  on the sentences of exercise `help-defeat`.
- 7.7, handling ambiguity, is deferred with its exercises 7.26–7.28
  (issue 43): its benefit is unclear for now, and the implementation
  within reach looked of little use. The scope reading of *Every dwarf
  defeated a giant* with the object in wide scope is not presented.
- 7.2 calls the second argument of a determiner its *body*, where CSwFP/6
  called it its *scope*. Both translate as "escopo".

### `Parsing`

CSwFP/8 is skipped for now, and the chapter follows `Composition`.

- 9.1: the tree relations are lists of pairs, as in CSwFP, because the
  section shows them with `#eval`; Mathlib's `Rel` of `Sets` is a `Prop`
  and cannot be printed. Dominance uses Lean's `<+:` (`List.IsPrefix`) in
  place of a helper `prefix`. `pos` is written with a local helper
  `posFrom` (`let rec`), so that Lean sees the recursion over the list
  of subtrees as structural. `ParseTree` has no empty tree: CSwFP's
  `Ep` is not ported (see "Inconsistencies found in CSwFP" below).
  `subtree` returns an `Option`, `none` at a position the tree does
  not have, where CSwFP's is undefined; `subtrees` drops the `none`s
  with `filterMap`. `toText` separates the
  daughters of a node by spaces, as in the bracket notation of LaTeX's
  `qtree` (`[.NP Snow White]`); CSwFP's `show` prints them as a list,
  with a further pair of brackets and commas. Nothing reads the text
  back: later chapters walk the trees, not their text.
- Exercise 9.2 becomes three theorems about positions: the relation of
  c-command is a sister followed by dominance, and no part depends on the
  tree. Part (3), on the lowest branching position, is stated with proper
  dominance, as "the mother of `p` dominates `q`": with reflexive
  dominance it is false (see "Inconsistencies found in CSwFP" above). Exercises 9.1, 9.3, 9.4 and 9.5 ask for a definition checked
  on the example tree; 9.6 asks for the splitting functions without empty
  parts.
- 9.2: `splitN` is defined for every number of pieces, where CSwFP's
  stops with an error below two: one piece is the input itself, and the
  empty input has the split into zero pieces. This makes `splitN` serve
  unary rules too, and lets `mem_splitN_flatten`, the converse of
  `flatten_of_mem_splitN`, hold for every list of pieces. `splitN'` in
  exercise 9.6 follows suit.
- 9.2: `recognize` and `parse` are total. They recurse over
  `(splitN 3 xs).attach`, which pairs each split with a proof of
  membership, and `decreasing_by` uses the lemma `flatten_of_mem_splitN`
  (the pieces of a split concatenate to the input) to show that the
  middle piece is shorter. The cue on termination says why left
  recursion is no trouble here, which is exercise 9.7. Generation stops
  at a given length, since Lean lists are finite. A theorem, in a
  `:::details` block, proves that `recognize` agrees with Mathlib's
  `List.Palindrome` on every word over `{a, b, c}`. `parse` gives every
  rule used an `A` node, so as to follow the grammar: `A → ε` gives a
  node with no children, and `A → a` a node over the leaf, where CSwFP
  gives a leaf `"[]"` and a bare leaf. A `:::details` block says why
  the shorter trees are not used.
- 9.3: `Parser α β` is `StateT (List α) List β`, which unfolds by
  definition to CSwFP's `[a] -> [(b,[a])]` (an `example … := rfl` says
  so). Mathlib's `Monad` and `Alternative` instances for `List` then give
  `pure`, `failure`, `<|>` and `<$>` with CSwFP's meaning, so `succeed`
  and `failp` are not defined: they are `pure` and `failure`. CSwFP's
  sequencing `<*>` and `<:>` become `do` blocks (Lean's `<*>` is the
  applicative one, with another type), and `collect` is written with
  `do`. The synonym `PARSER a b` is not ported: as an `abbrev` over
  `Parser α (ParseTree α β)` it hides the type constructor that `<$>`
  and `<|>` need to find their instances. Lean's `Std.Internal.Parsec`
  was considered and rejected: it returns one result, and its `<|>`
  commits to the first alternative that succeeds.
- 9.3: `palindrome`, `many` and the left-recursive example are
  `partial def`. The input they recurse on is the remainder left inside
  the `StateT`, and proving it shorter would need parsers that carry a
  proof that their remainder is a suffix of the input. Later sections
  only run parsers. A cue cites Danielsson's total parser combinators.
  The left-recursive example is defined but never run: it overflows the
  stack.
- 9.3: the Mastermind parser is dropped with Mastermind (see 5.4).
  `many` stays (9.6 uses it), moved to right after `parseAs`, and is
  built from a new one-or-more `many1` (the names of Lean's
  `Std.Internal.Parsec`): `many p` is `many1 p <|> pure []`. To give
  them a use, the example grammar of Figure 9.1 is extended from the
  start of the section with a sequence of adjectives,
  `NP ::= … | D N | D ADJS N` and `ADJS ::= ADJ … ADJ` (one or more,
  so that a bare `D N` has a single parse); `adjs` is
  `.branch "ADJS" <$> many1 adj`. `parseManyAs`, used later in CSwFP
  by nothing but the Mastermind parser, is not ported. The new
  exercise `adjs-recursive` writes ADJS with the recursive rule
  `ADJS ::= ADJ ADJS | ADJ`, compares its nested tree with the flat
  one, and shows by running it that the variant with `ε` gives
  *every wizard* two parses.
- 9.3: `<$>` comes before sequencing, so that every parser past the
  elementary ones builds a parse tree. The categories with only
  terminals on the right (`det`, `adj`, `n`, `vp`) are built with `<$>`;
  sequencing is shown on the rule NP → D N, combining two trees in a
  node; `collect` and `parseAs` generalize it. CSwFP's `pS`, …, `pN`,
  which return strings, are not ported.
- 9.3: the palindrome parser becomes the new exercise
  `palindrome-parser`, checked by running it on two inputs. It returns
  the same trees as `parse` in 9.2, one `A` node for every rule used:
  `A → ε` is `parseAs 'A' []`. CSwFP's `epsilonT`, which built the
  empty tree `Ep` for that rule, has no use left and is not ported.
- 9.4: `combine` returns an `Option Agreement`, and `assign` an
  `Option Cat`, where CSwFP returns a list that is empty on failure and
  has one element otherwise. `combine` puts the features in a canonical
  order by filtering `allFeats`, the list of every feature, where CSwFP
  sorts and removes duplicates: Lean's `List.mergeSort` is defined by
  well-founded recursion, so `decide` cannot evaluate it. The lists of
  the values of each kind of feature (`genderFeats`, …) are named, and
  `allFeats` joins them. `Cat` is a structure, whose fields replace
  CSwFP's functions `phon`, `catLabel`, `fs` and `subcatList`.
  Constructors of `Feat` are lowercase (`sg`, `mascOrFem`), as Lean
  style asks, and `Feat.toString` prints them as in CSwFP (`Sg`). A
  category is printed as an attribute-value matrix, as in HPSG and the
  ERG (`[CAT NP, ORTH she, GEN fem, NUM sg, …]`, with `SUBCAT ⟨…⟩`),
  where CSwFP prints `she NP[Pers,Thrd,Sg,Nom,Fem]`; the attributes are
  the kinds of features, and the display, a `Repr` instance built with
  `Std.Format`, sits in a `:::details` block. The terse cues present
  `combine` as unification of these matrices.
  The new exercise `combine-comm` proves that `combine` does not
  depend on the order of the categories.
- 9.5: the lexicon is not one function by cases on the word. Its
  entries are lists of `Cat`, one per word class (`pronouns`,
  `commonNouns`, `verbs`, …), and `lexicon w` keeps the entries whose
  form is `w`. The regular classes are built by helpers: `noun` gives
  the singular and plural of a common noun, `verb` the past (`tense`)
  and infinitive (`infl`) of a verb with a given subcategorization
  list. The entries are the same as CSwFP's, in the same order for
  each word. `collectCats` returns `Except String (List (List Cat))`,
  with an error naming the unknown words, where CSwFP calls `error`. `scan`
  works on the list of characters, `scanChars`, and `lexer` splits on
  spaces with `splitOn`, as Lean has no `words`. The new exercise
  `init-cats-length` proves that the number of lists returned by
  `initCats` is the product of the number of categories of each word.
- 9.6: the parsers are written bottom-up, from the lexical parsers to
  `sRule`, because Lean needs a definition before its use; CSwFP
  starts with `sRule`. The rules are in `do`-notation on the `Parser`
  of 9.3, and `fromOption`, which is not in CSwFP, turns the `none` of
  `combine`, `assign` and `assignT` into `failure`. `match` is renamed
  `matchSubcat`, as `match` is a Lean keyword. `prs` returns
  `Except String (List (ParseTree Cat Cat))`, following `collectCats`,
  with two errors: an unknown word, and a sentence with no parse,
  where CSwFP returns the empty list. So `.ok` always carries at least
  one tree. A parse tree is printed as one AVM, the daughters of a node
  under `ARGS` as in the ERG, through a `Repr` instance built with
  `Std.Format` in a `:::details` block. Exercise 9.10 waits in issue
  53.
- 9.9: further reading is kept, unlike in the other chapters, as the
  last section of the chapter, and extended with references on general
  parsing algorithms (CKY, Earley) that a `:::details` block after
  `leftRec` points to. The sentences on 9.7 (gaps, extraction grammars)
  wait in a `:::dev` note until 9.7 is written.

## Beyond CSwFP/9

Not planned yet. CSwFP/8 is skipped for now.
