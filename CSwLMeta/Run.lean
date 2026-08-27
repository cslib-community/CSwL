-- Adapted from sf-in-lean/SFLMeta/Run.lean, simplified: `CSwL` is a single
-- book (`sf-in-lean` has three "volumes"), so there is no `vol`/`crossVol`
-- parametrization -- the prefix is always `CSwL`.
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

/-- Verso always writes the multi-page HTML output to `html-multi/`. `CSwL`
only ever emits that form, so the qualifier buys nothing, and the directory
is renamed to plain `html/` at the end of the build (see
`sf-in-lean/SFLMeta/Run.lean`, `renameHtmlDir`). -/
def renameHtmlDir (dest : System.FilePath) : IO Unit := do
  let multi := dest.join "html-multi"
  let html := dest.join "html"
  if ← multi.pathExists then
    if ← html.pathExists then
      IO.FS.removeDirAll html
    IO.FS.rename multi html

/-- Build the book in one variant.  `args` is the command line of the
`cswl-book` executable: the first argument is the variant, the rest is passed
through to `manualMain`. -/
def runBook (doc : Verso.Doc.Part Manual) (args : List String) : IO UInt32 := do
  match args with
  | mode :: rest => do
    let some variant := Variant.fromString? mode
      | IO.eprintln s!"invalid variant: {mode}"
        IO.eprintln "variant must be student, solutions, terse, or grading"
        return 1
    setCurrVariant variant
    let extraStep := match variant with
      | .student => Save.emitSavedStudent bookPrefix
      | .solutions => Save.emitSavedSolutions bookPrefix
      | .terse => Save.emitSavedTerse bookPrefix
      | .grading => Save.emitSavedGrading bookPrefix
    let config := mkConfig mode
    let rc ← manualMain doc (options := rest) (config := config) (extraSteps := [extraStep])
    if rc == 0 then
      renameHtmlDir config.destination
    return rc
  | _ =>
    IO.eprintln "usage: lake exe cswl-book <variant>"
    IO.eprintln "  (variant: student | solutions | terse | grading)"
    return 1

end CSwLMeta
