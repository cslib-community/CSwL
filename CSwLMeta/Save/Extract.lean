-- Adapted from sf-in-lean/SFLMeta/Save/Extract.lean
-- (namespace SFLMeta -> CSwLMeta), with the cuts that go along with the
-- modules CSwL did not port (see `CSwLMeta.lean`):
--
-- * the `walkBlock` cases for Details/Terse+Full/SlideBreak are left out --
--   the corresponding modules don't exist here;
--   (DevComment was ported -- see the `Block.devcomment` case below; Bnf and
--   DisplayMath were also ported, but with no case of their own here --
--   they fall through to the generic branch below, which already suffices:
--   `Block.bnf`/`Block.display` wrap the original text as a `Block.code`
--   child, and the generic branch recurses into the children, so the text
--   comes out as a `--` comment, without trying to elaborate it as real
--   Lean -- the right behavior for BNF and for informal derivations like
--   `turn ⇒ attack reaction ⇒ ...`);
-- * the support module (`SFLCompat.lean`) is left out, which serves to
--   carry the `sf_experiment`/`sf_expect_failure` macros to the extracted
--   project: CSwL's chapters only use plain ` ```lean ` blocks
--   (extractionMode = .code);
-- * `hasSuppressHeaderMarker` (which depended on Terse.lean) is fixed to
--   `false`.
--
-- Everything else -- SaveBuffers, the text formatter, the
-- walkBlocks/walkBlock/walkSection/walkOuter control flow, and the
-- leanSaved/exercise/quiz/quizSolution/gradeTheorem/devcomment cases -- is a
-- literal copy, as far as the cuts allow. When porting one of the missing
-- modules, its corresponding `walkBlock` case must come back along with it,
-- or the block falls through to the generic branch and turns into prose.

import VersoManual

import CSwLMeta.Comment
import CSwLMeta.Exercise
import CSwLMeta.Quiz
import CSwLMeta.Grade

import CSwLMeta.Save.SourceRewrite
import CSwLMeta.Save.Lean
import CSwLMeta.Save.CodeBlock

import Std.Data.HashMap

open Lean
open Std (HashMap)
open Verso Doc Genre Manual

namespace CSwLMeta.Save


/-- Per-file buffers accumulated by the saver -/
abbrev SaveBuffers := HashMap String (Variants String)

namespace SaveBuffers

def appendAll (buf : SaveBuffers) (file : String) (s : String) : SaveBuffers :=
  let vs := buf.getD file default
  buf.insert file <| vs.map (· ++ s)

def appendOnly (buf : SaveBuffers) (file : String) (variant : Variant) (s : String) : SaveBuffers :=
  let vs := buf.getD file default |>.mapV fun v x => if v == variant then x ++ s else x
  buf.insert file vs

def append
    (buf : SaveBuffers) (file : String) (vs' : Variants String) : SaveBuffers :=
  let vs := buf.getD file default
  buf.insert file <| vs ++ vs'

end SaveBuffers

namespace Text

/-- Join author (or other) name fragments the way `{citep}`/`{citet}` do in the
HTML/TeX output: `"A"`, `"A and B"`, `"A, B, and C"`. -/
def andListText : Array String → String
  | xs =>
    match xs.size with
    | 0 => ""
    | 1 => xs[0]!
    | 2 => xs[0]! ++ " and " ++ xs[1]!
    | _ =>
      let allButLast := xs.extract 0 (xs.size - 1)
      String.intercalate ", " allButLast.toList ++ ", and " ++ xs.back!

mutual

/--
Render a piece of Verso inline content to a plain-text fragment suitable for
inclusion in a `/-! … -/` Lean module-doc comment. Markdown-like delimiters
(`*…*` for emphasis, `**…**` for bold, backticks for code, `[text](url)` for
links) are preserved so the resulting comment still reads naturally.
`{citep}`/`{citet}`/`{citehere}` are recognised specially (via `citeToText`)
since their visible text is computed from `data`, not from child inlines —
the generic `.other` fallback below would otherwise render them as empty. -/
partial def inlineToText : Verso.Doc.Inline Manual → String
  | .text s => s
  | .linebreak _ => "\n"
  | .emph content => "*" ++ String.join (content.toList.map inlineToText) ++ "*"
  | .bold content => "**" ++ String.join (content.toList.map inlineToText) ++ "**"
  | .code s => "`" ++ s ++ "`"
  | .math _ s => "$" ++ s ++ "$"
  | .link content url =>
    "[" ++ String.join (content.toList.map inlineToText) ++ "](" ++ url ++ ")"
  | .footnote name _ => s!"[^{name}]"
  | .image alt url => s!"![{alt}]({url})"
  | .concat content => String.join (content.toList.map inlineToText)
  | .other which content =>
    if which.name == ``Verso.Genre.Manual.Bibliography.Inline.cite then
      citeToText which.data
    else String.join (content.toList.map inlineToText)

/-- Short in-text form of a single citation's author list: last name(s) only,
matching the local `authorHtml` helper inside `Citable.inlineHtml`
(`VersoManual/Bibliography.lean`) — one author's last name, "A and B" for two
or three, and "A et al." beyond that. -/
partial def citeAuthorText (c : Verso.Genre.Manual.Bibliography.Citable) : String :=
  open Verso.Genre.Manual.Bibliography in
  let names := c.authors
  if h : names.size = 0 then ""
  else if h : names.size = 1 then inlineToText (Bibliography.lastName names[0])
  else if h : names.size > 3 then inlineToText (Bibliography.lastName names[0]) ++ " et al."
  else andListText (names.map (fun n => inlineToText (Bibliography.lastName n)))

/-- Render an in-text citation (`{citep}`/`{citet}`/`{citehere}`) to plain text:
the short "author (year)" / "(author, year)" form that `Citable.inlineHtml`
puts in the running text, without the marginalia popup (the full bibliography
entry shown on hover in HTML), which has no plain-text analogue. Decodes
`data` the same way `Inline.cite`'s own `toHtml`/`toTeX` do. -/
partial def citeToText (data : Json) : String :=
  open Verso.Genre.Manual.Bibliography in
  match FromJson.fromJson? data with
  | .error _ => ""
  | .ok ((citationsJson, style) : Json × Style) =>
    match FromJson.fromJson? citationsJson with
    | .error _ => ""
    | .ok (cs : List Citable) =>
      let one (c : Citable) : String :=
        let a := citeAuthorText c
        match style with
        | .parenthetical => s!"({a}, {c.year})"
        | .textual | .here => s!"{a} ({c.year})"
      String.intercalate "; " (cs.map one)

end

/-- Pretty-print an array of inlines to plain text. -/
def inlinesToText (inls : Array (Verso.Doc.Inline Manual)) : String :=
  String.join (inls.toList.map inlineToText)

/-- Right margin used when filling prose paragraphs in the terse build's
generated `.lean` files. -/
def terseFillWidth : Nat := 60

/-- Right margin used when filling prose paragraphs in the student and
solutions builds' generated `.lean` files. -/
def proseFillWidth : Nat := 75

/-- The prose fill width for a build variant. -/
def fillWidthFor : Variant → Nat
  | .terse => terseFillWidth
  | .student | .solutions | .grading => proseFillWidth
/--
Split `s` into whitespace-separated words, keeping each `` `code span` `` intact
as a single token even when it contains spaces (so wrapping never splits one
across a line break). -/
private def tokenizeKeepingCodeSpans (s : String) : Array String := Id.run do
  let mut words : Array String := #[]
  let mut cur : String := ""
  let mut inCode := false
  for c in s.toList do
    if inCode then
      cur := cur.push c
      if c == '`' then inCode := false
    else if c == '`' then
      cur := cur.push c
      inCode := true
    else if c == ' ' || c == '\n' || c == '\t' then
      if !cur.isEmpty then
        words := words.push cur
        cur := ""
    else
      cur := cur.push c
  if !cur.isEmpty then words := words.push cur
  return words

/--
Fill (word-wrap) `text` to at most `width` columns. The source's soft-wrap
newlines and continuation-line indentation are discarded and the words are
reflowed; a `` `code span` `` is never split across lines, and a single word
longer than `width` is left to overflow rather than being broken. -/
def fillText (width : Nat) (text : String) : String := Id.run do
  let mut lines : Array String := #[]
  let mut cur : String := ""
  for w in tokenizeKeepingCodeSpans text do
    if cur.isEmpty then
      cur := w
    else if cur.length + 1 + w.length ≤ width then
      cur := cur ++ " " ++ w
    else
      lines := lines.push cur
      cur := w
  if !cur.isEmpty then lines := lines.push cur
  return String.intercalate "\n" lines.toList

/-- Pretty-print a paragraph's inlines, reflowing them to `width` columns. -/
def paraToText (width : Nat) (inls : Array (Verso.Doc.Inline Manual)) : String :=
  fillText width (inlinesToText inls)

/-- Drop leading and trailing all-whitespace lines from `s`, preserving each
remaining line's own leading whitespace. -/
defmethod String.stripBlankEdgeLines (s : String) : String :=
  let blank : String → Bool := fun l => l.all (·.isWhitespace)
  let ls := s.splitOn "\n"
  let ls := (((ls.dropWhile blank).reverse).dropWhile blank).reverse
  String.intercalate "\n" ls

/--
Render a Verso block to a Markdown-like string for inclusion in a `/-! … -/`
comment, filling prose to `width` columns.  List items are prefixed with `- ` /
`N. `; continuation lines are indented to align under the item text. -/
partial def blockToText (width : Nat) : Verso.Doc.Block Manual → String
  | .para inlines => paraToText width inlines
  | .code s => "`" ++ s.trimAscii.toString ++ "`"
  | .concat bs | .blockquote bs =>
    String.intercalate "\n\n" (bs.toList.map (blockToText width))
  | .ul lis =>
    let items := lis.toList.map fun li =>
      let body := String.intercalate "\n\n" (li.contents.toList.map (blockToText width))
      "- " ++ body.replace "\n" "\n  "
    let sep := if items.any (·.contains '\n') then "\n\n" else "\n"
    String.intercalate sep items
  | .ol start lis =>
    let items := lis.toList.mapIdx fun i li =>
      let pfx := s!"{start + i}. "
      let indent := String.ofList (List.replicate pfx.length ' ')
      let body := String.intercalate "\n\n" (li.contents.toList.map (blockToText width))
      pfx ++ body.replace "\n" s!"\n{indent}"
    let sep := if items.any (·.contains '\n') then "\n\n" else "\n"
    String.intercalate sep items
  | .dl dis =>
    String.intercalate "\n" (dis.toList.map fun di =>
      inlinesToText di.term ++ "\n:   " ++
      String.intercalate "\n    " (di.desc.toList.map (blockToText width)))
  | .other _ bs => String.intercalate "\n\n" (bs.toList.map (blockToText width))

end Text


/-! ## ExtraStep walker -/

/-- Render a string as a block of `--` line comments, one per line (blank lines
stay completely blank), normalising trailing whitespace. -/
private def asModuleDoc (s : String) : String :=
  let t := s.trimAscii.toString
  let commented := String.intercalate "\n"
    ((t.splitOn "\n").map fun line =>
      if line.all (·.isWhitespace) then "" else "-- " ++ line)
  commented ++ "\n\n"

/-- Render a shown `:::dev` note as one contiguous `--` comment block, visually
set off from surrounding prose: the label line first, body lines indented 4
spaces under it, and interior blank lines kept as bare `--` (not truly blank)
so the note reads as a single unit. -/
private def devNoteComment (label body : String) : String :=
  let indented := String.intercalate "\n"
    ((body.trimAscii.toString.splitOn "\n").map fun l =>
      if l.all (·.isWhitespace) then "--" else "--     " ++ l)
  "-- " ++ label ++ ":\n" ++ indented ++ "\n\n"

section

/-- Decode a `Block.exercise` payload `(rating, name, level, manual)`, tolerating
the older 2-element `(rating, name)` form.  (See `CSwLMeta.decodeExerciseData`.) -/
def decodeExercise? (data : Json) : Option (Nat × String × Option String × Bool) :=
  match data with
  | .arr #[.num _, .str _, _, _] | .arr #[.num _, .str _] => some (decodeExerciseData data)
  | _ => none

/-- Whether a section's own blocks carry a full-only-heading suppression
marker. Always `false` here: the marker (`Block.
suppressPreviousHeaderWhenTerse`) is emitted only by `Terse.lean`, which the
CSwL has not ported. -/
def hasSuppressHeaderMarker (_blocks : Array (Verso.Doc.Block Manual)) : Bool :=
  false

/-- Find the ASCII alt text inside a `diagramWithAlt`: the first plain code block. -/
def findAlt? (contents : Array (Verso.Doc.Block Manual)) : Option String :=
  contents.findSome? fun
    | .code s => some s
    | _ => none

/-- For wrapping code in `sf_experiment` and `sf_expect_failure` -/
def wrapIndented (startText body : String) : String :=
  let body := body.trimAscii.toString.splitOn "\n" |>.map ("  " ++ ·) |> String.intercalate "\n"
  startText ++ "\n" ++ body ++ "\n\n"

end

section

/--
Determine the file-name base for a chapter Part. Uses the `file := …` HTML
metadata if the chapter author set it; otherwise falls back to the sluggified
title (matching what Verso uses for the HTML output filename). -/
def chapterFileBase (p : Part Manual) : String :=
  let .mk _ titleStr meta? _ _ := p
  (meta?.bind (·.file)).getD titleStr.sluggify.toString


/-- Generated Lean file path for a chapter Part. -/
def chapterPath (vol : String) (p : Part Manual) : String :=
  vol ++ "/" ++ chapterFileBase p ++ ".lean"

/-- Generated Lean module name for a chapter Part. Uses the raw `file :=`
identifier when it is a plain alphanumeric/underscore name; falls back to
French-quote brackets for slugs that contain hyphens or other punctuation. -/
def chapterModule (vol : String) (p : Part Manual) : String :=
  let base := chapterFileBase p
  if base.all (fun c => c.isAlphanum || c == '_') then vol ++ "." ++ base
  else vol ++ ".«" ++ base ++ "»"

end

mutual

open Text

/--
Walk a list of blocks, batching consecutive `.para`, `.ul`, and `.ol` blocks
into a single `/-! … -/` comment instead of emitting one per block, so a list
stays in the same comment as its lead-in paragraph. -/
partial def walkBlocks (width : Nat) (file : String) (bs : Array (Verso.Doc.Block Manual))
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  let mut buf := buf
  let mut pending : Array String := #[]
  for b in bs do
    match b with
    | .para inls => pending := pending.push (Text.paraToText width inls)
    | .ul _ | .ol _ _ => pending := pending.push (Text.blockToText width b)
    | _ =>
      if !pending.isEmpty then
        buf := buf.appendAll file (asModuleDoc (String.intercalate "\n\n" pending.toList))
        pending := #[]
      buf := walkBlock width file b buf
  if !pending.isEmpty then
    buf := buf.appendAll file (asModuleDoc (String.intercalate "\n\n" pending.toList))
  return buf

/--
Walk a single block, accumulating content for the student, solutions, and terse
variants in `buf` for `file`. Only the blocks the CSwL actually uses
(`leanSaved`, `importBlock`, `exercise`, `diagramWithAlt`, `quiz`,
`quizSolution`, `gradeTheorem`) are handled specially; anything else recurses
into its children as a best-effort, matching the original's fallback for
unknown extension blocks. -/
partial def walkBlock (width : Nat) (file : String) (b : Verso.Doc.Block Manual)
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  match b with
  | .other which contents =>
    let name := which.name
    if name == ``Verso.Genre.Manual.Block.diagram then
      return buf
    if name == ``CSwLMeta.Block.leanSaved then
      -- The wrapper carries pre-computed student, solutions, and terse source
      -- variants plus the extraction-relevant `lean` block flags. Verso still
      -- checks and renders the selected child normally; the generated project
      -- gets code, `sf_experiment`, or `sf_expect_failure` according to
      -- `LeanSaved.Data.extractionMode`.
      if let some saved := LeanSaved.decode? which.data then
        match saved.extractionMode with
        | .code =>
          return buf.append file <| saved.variants.map fun src =>
           src.trimAscii.toString ++ "\n\n"
        | .experiment =>
          return buf.append file <| saved.variants.map (wrapIndented "sf_experiment")
        | .expectFailure =>
          return buf.append file <| saved.variants.map (wrapIndented "sf_expect_failure")
      return buf
    if name == ``Block.importBlock then
      -- Cross-chapter `import` lines shown to the reader.  The extracted
      -- files get their import lines from the chapter source's header
      -- preamble (assembled by the caller), so nothing is emitted here.
      return buf
    if name == ``Block.exercise then
      -- Emit a `### Exercise (N⭐): name` heading; the contained `lean`
      -- blocks render normally via recursion below.
      if let some (rating, exName, level, manual) := decodeExercise? which.data then
        let stars := String.ofList (List.replicate rating '⭐')
        let desig := exerciseDesignation level manual
        let header := s!"### Exercise ({rating} star{if rating == 1 then "" else "s"}): {exName}{desig} {stars}"
        let mut buf := buf.appendAll file (asModuleDoc header)
        buf := walkBlocks width file contents buf
        return buf
      return buf
    if name == ``Block.diagramWithAlt then
      match findAlt? contents with
      | .some alt => return buf.appendAll file (asModuleDoc alt.trimAscii.toString)
      | .none => return buf
    if name == ``Block.quiz then
      -- A quiz is shown in every build product; label it so the reader of the
      -- generated `.lean` can tell the question apart from surrounding prose.
      let mut buf := buf.appendAll file (asModuleDoc "_Quiz:_")
      buf := walkBlocks width file contents buf
      return buf
    if name == ``Block.quizSolution then
      -- A quiz answer is elided from every generated `.lean` build product —
      -- it surfaces only in the HTML book, as a click-to-reveal button.
      return buf
    if name == ``Block.devcomment then
      -- A `:::dev` note (marking a deviation from the CSwFP presentation)
      -- passes through as a labelled comment when its urgency makes it shown
      -- (`devNoteShown`: `NOW`, `BeforeNextRelease`, or none); otherwise
      -- nothing is emitted.
      if let some (author, urgency, year) := decodeDevData? which.data then
        if devNoteShown urgency then
          let body := String.intercalate "\n\n"
            (contents.toList.map (blockToText (width - 4)))
          return buf.appendAll file
            (devNoteComment (devNoteLabel author urgency year) body)
      return buf
    if name == ``Block.gradeTheorem then
      let ⟨points, names⟩ := decodeGradeTheoremData which.data
      let names := " ".intercalate (names.map Name.toString).toList
      return buf.appendOnly file .grading s!"attribute [autogradedProof {points}] {names}\n\n"
    -- Unknown extension block: recurse into children as a best-effort.
    walkBlocks width file contents buf
  | .para inls => return buf.appendAll file (asModuleDoc (paraToText width inls))
  | .code s => return buf.appendAll file (asModuleDoc s.trimAscii.toString)
  | .concat bs | .blockquote bs => walkBlocks width file bs buf
  | .ul _ | .ol _ _ =>
    return buf.appendAll file (asModuleDoc (blockToText width b))
  | .dl dis =>
    let mut buf := buf
    for di in dis do
      buf := buf.appendAll file (asModuleDoc (inlinesToText di.term))
      buf := walkBlocks width file di.desc buf
    return buf


end

/--
Walk a section (a Part at depth ≥ 1, inside a chapter). The section's title is
emitted as a `#`-prefixed module-doc heading whose level equals `depth`; all
content goes into the chapter's `file`. -/
partial def walkSection (width : Nat) (depth : Nat) (file : String) (part : Part Manual)
    (buf : SaveBuffers) : SaveBuffers := Id.run do
  let .mk titleInlines _ _ intro subParts := part
  let mut buf := buf
  let hashes := String.ofList (List.replicate depth '#')
  let titleText := Text.inlinesToText titleInlines
  if !hasSuppressHeaderMarker intro then
    buf := buf.appendAll file (asModuleDoc s!"{hashes} {titleText}")
  buf := walkBlocks width file intro buf
  for p in subParts do
    buf := walkSection width (depth + 1) file p buf
  return buf

/--
The root of the walker. Each top-level sub-Part of the root document is
treated as a chapter and written to its own file (using the `file :=` metadata
key each chapter sets in its `%%%` block). The root file (`{vol}.lean`) gets one
`import` line per chapter. -/
def walkOuter (width : Nat) (vol : String) (text : Part Manual) (buf : SaveBuffers) :
    SaveBuffers := Id.run do
  let rootFile := vol ++ ".lean"
  let .mk _ _ _ _ subParts := text
  let mut buf := buf
  for p in subParts do
    buf := buf.appendAll rootFile s!"import {chapterModule vol p}\n"
  for p in subParts do
    let chapterFile := chapterPath vol p
    buf := buf.appendOnly chapterFile .grading s!"import AutograderLib\n\n"
    buf := walkSection width 1 chapterFile p buf
  return buf

end CSwLMeta.Save
