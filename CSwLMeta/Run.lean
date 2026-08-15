-- Adapted from /Users/ar/r/sf-in-lean/SFLMeta/Run.lean, simplified: o `CSwL` é
-- um livro só (o `sf-in-lean` tem três "volumes"), então não há a
-- parametrização por `vol`/`crossVol` — o prefixo é sempre `CSwL`.
import VersoManual
-- Import the full `CSwLMeta` aggregate (not just `Save`): `manualMain`'s
-- default `extension_impls%` collects the registered block/inline extensions
-- from *this* module's environment, so every `block_extension` (`:::exercise`,
-- `:::solution`, `::::quiz`, `:::quizSolution`, `:::gradeTheorem`, …) must be
-- in scope here or HTML rendering panics with "No block traversal
-- implementation found".  (This module is deliberately *not* part of the
-- `CSwLMeta` aggregate, so importing it back is not a cycle.)
import CSwLMeta

open Verso Genre Manual

namespace CSwLMeta

/-- Module prefix (and directory) of the book's chapters: `CSwL/ChapterNN.lean`
⇒ `CSwL.ChapterNN`.  It is both the buffer key used by the extractor and the
name of the `lean_lib` in the standalone project written under
`_out/<variante>/lean/`. -/
def bookPrefix : String := "CSwL"

/-- Render configuration for a single variant build. -/
def mkConfig (mode : String) : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  destination := s!"_out/{mode}"

/-- Build the book in one variant.  `args` is the command line of the
`cswl-book` executable: the first argument is the variant, the rest is passed
through to `manualMain`. -/
def runBook (doc : Verso.Doc.Part Manual) (args : List String) : IO UInt32 := do
  match args with
  | mode :: rest => do
    let some variant := Variant.fromString? mode
      | IO.eprintln s!"variante inválida: {mode}"
        IO.eprintln "a variante tem de ser student, solutions, terse ou grading"
        return 1
    setCurrVariant variant
    let extraStep := match variant with
      | .student => Save.emitSavedStudent bookPrefix
      | .solutions => Save.emitSavedSolutions bookPrefix
      | .terse => Save.emitSavedTerse bookPrefix
      | .grading => Save.emitSavedGrading bookPrefix
    let config := mkConfig mode
    manualMain doc (options := rest) (config := config) (extraSteps := [extraStep])
  | _ =>
    IO.eprintln "uso: lake exe cswl-book <variante>"
    IO.eprintln "  (variante: student | solutions | terse | grading)"
    return 1

end CSwLMeta
