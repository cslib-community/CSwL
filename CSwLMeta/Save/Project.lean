-- Adapted from sf-in-lean/SFLMeta/Save/Project.lean.
--
-- For each variant, writes a standalone Lake project to
-- `_out/<variant>/lean/`: the `.lean` files extracted from the book, plus a
-- `lakefile.toml`, a `lean-toolchain`, and a `README.md`. This generated
-- project — and only it — depends on `lean4-autograder-main`, in the
-- `grading` variant; the autograder does not enter `CSwL`'s own
-- `lakefile.toml` (it collides with the Mathlib that `cslib` brings; see the
-- comment on `[[lean_exe]] cswl-book`).
--
-- Three deliberate cuts relative to the `sf-in-lean` original, all because
-- they have no equivalent in `CSwL` (a fourth cut, about the `SFLCompat`
-- support module, was REVERTED -- see the note below):
--
-- 1. No `crossVol`: `sf-in-lean` has three volumes, and chapters in one
--    import chapters from another. `CSwL` is a single book.
-- 2. No generic `bundleLoop`: the original copies, verbatim, the source of
--    ANY prerequisite module that is not a chapter or an external package
--    (in `sf-in-lean`, things like `LF/CustomTactics.lean`, plus
--    `SFLCompat` itself). `CSwL` has no prerequisite module at all outside
--    the book itself: a chapter imports Mathlib, sections living in their
--    own file under the same chapter (`CSwL.Morphology.…`, silently
--    dropped by `isIntraBookSection` -- their content has already been
--    merged into the chapter's buffer, there is no separate module to
--    import in the extracted project), the `CSwLCompat` support module (see
--    below), and nothing else. Any other `import` becomes a book build
--    error -- a loud failure, instead of a generated project with an
--    `import` that does not resolve. That's why what exists here is only
--    `bundleCompatSeed`, a fixed copy of a single file, not a recursive
--    dependency search like `sf-in-lean`'s `bundleLoop` -- we didn't
--    generalize to arbitrary prerequisite modules because `CSwL` has no
--    other candidate today.
-- 3. No `mergeAdjacentModuleDocs`: the original merges adjacent `/-! … -/`
--    blocks, and our extractor writes prose as `--` lines.
--
-- REVERTED CUT -- support module (`CSwLCompat.lean`, adapted from
-- `sf-in-lean`'s `SFLCompat.lean`/`SFLCompat/Experiment.lean`): it defined
-- the `sf_experiment`/`sf_expect_failure` macros, which the extractor
-- already emits (see `Save/Extract.lean`, `walkBlock`) for ` ```lean -keep `
-- and ` ```lean +error ` blocks, but which previously had no definition at
-- all in the generated project -- a chapter with one of those fences would
-- generate an unknown macro. Ported because a real chapter came to need
-- both fences (code that must fail Lean's check, or exploratory code that
-- must not contaminate the environment of the following blocks).
-- `CSwLCompat` is a top-level module name -- not `CSwL.Compat` or
-- `CSwLMeta.Compat` -- on purpose: `CSwL.Compat` would fall into
-- `isIntraBookSection` (dropped as if it were a section of the chapter
-- itself) and `CSwLMeta.Compat` would fall into `frameworkPrefixes`
-- (dropped as book infrastructure) -- in both cases the `import` would
-- silently disappear from the extracted header, and the generated project
-- would have a macro with no definition. A module of its own at the top
-- level avoids both exclusion lists without having to touch them.

import VersoManual

import CSwLMeta.Variant

import CSwLMeta.Save.Extract

open Verso Doc Genre Manual

namespace CSwLMeta.Save

/-- Revision of `lean4-autograder-main` used by the generated project for the
`grading` variant. The same one the validation spike tested. -/
def autograderRev : String := "comparator-4.33.0"

def autograderUrl : String := "https://github.com/plclub/lean4-autograder-main"

structure ExtractConfig where
  /-- Chapters' module prefix (and directory): `CSwL`. -/
  modPrefix : String
  variant : Variant
  /-- Run `lake build` inside the generated project, to check that it
  compiles on its own. Stays `false` for two reasons, both measured and not
  hypothetical: (a) chapters import Mathlib, so the generated project would
  compile Mathlib from scratch on every `make`; (b) in the `grading` variant
  the autograder requires the `v4.33.0` toolchain and ours is
  `v4.33.0-rc2` -- the same mismatch that kept the autograder out of
  `CSwL`'s own `lakefile.toml`, and which remains open for the real
  chapters (`Placeholder` does not import Mathlib, so for it the generated
  `grading` project is pure autograder). -/
  verify : Bool := false

/-! ## Generated Lake project template -/

/-- Content of the generated project's `lakefile.toml`. `pkgRequires` lists
the external packages `(name, git url, rev)` some extracted chapter needs
(e.g. Mathlib from `import Mathlib.Tactic`), each pinned to the same
revision the book is compiled with -- read from `CSwL`'s own
`lake-manifest.json`. `extraLibs` lists additional library names to declare
besides `vol` -- today, at most, `"CSwLCompat"` when some extracted chapter
imports the support module (see `bundleCompatSeed`). It does not go into
`defaultTargets`: as in `sf-in-lean`, it is pulled in transitively by the
`import` of the chapter that uses it. -/
private def lakefileTemplate (vol : String) (v : Variant)
    (pkgRequires : Array (String × String × String))
    (extraLibs : Array String) : String :=
  let pkgRequires := if v.isGrading
    then pkgRequires.push ("autograder", autograderUrl, autograderRev)
    else pkgRequires
  let reqs := pkgRequires.foldl (init := "") fun acc (name, url, rev) =>
    acc ++ "\n[[require]]\nname = \"" ++ name ++ "\"\ngit = \"" ++ url ++
      "\"\nrev = \"" ++ rev ++ "\"\n"
  let libs := extraLibs.foldl (init := "") fun acc lib =>
    acc ++ "\n[[lean_lib]]\n" ++ "name = \"" ++ lib ++ "\"\n"
  "name = \"" ++ vol.toLower ++ "-extracted\"\n" ++
  "version = \"0.1.0\"\n" ++
  "defaultTargets = [\"" ++ vol ++ "\"]\n" ++
  reqs ++
  "\n[[lean_lib]]\n" ++
  "name = \"" ++ vol ++ "\"\n" ++
  libs

private def readmeTemplate (vol : String) (v : Variant) : String :=
  s!"# {vol} — variante `{v}`\n\n" ++
  "Gerado a partir do livro (Verso, gênero `Manual`) por " ++
  s!"`lake exe cswl-book {v}` — **não edite aqui**: a fonte é o `CSwL`.\n\n" ++
  (if v.isGrading then
    "Esta variante traz as provas completas e os atributos " ++
    "`[autogradedProof …]`. Para corrigir uma entrega:\n\n" ++
    "    lake exe autograder --local <entrega> <arquivo deste projeto>\n\n" ++
    "Ela nunca sai do repositório privado.\n"
   else "")

/-- Writes the generated project to `dest`: the extracted files, plus
`lakefile.toml`, `lean-toolchain`, and `README.md`. `extraLibs` are
libraries besides `vol` (today, at most, `"CSwLCompat"`) whose source root
also needs to be cleared before rewriting, for the same reason as `vol`
below. -/
private def writeProject (dest : System.FilePath) (toolchain : String)
    (vol : String) (v : Variant) (files : Array (String × String))
    (pkgRequires : Array (String × String × String))
    (extraLibs : Array String) : IO Unit := do
  IO.FS.createDirAll dest
  -- Clears the source tree so a renamed or removed chapter doesn't linger
  -- as an orphan from a previous generation. The rest (`.lake`,
  -- `lakefile.toml`, `lean-toolchain`, `README.md`) stays where it is.
  for lib in #[vol] ++ extraLibs do
    let libRoot := dest / lib
    if ← libRoot.pathExists then
      IO.FS.removeDirAll libRoot
    -- `CSwLCompat` today is a single top-level file (`CSwLCompat.lean`),
    -- not a directory -- `libRoot` above does not reach it; remove the
    -- file separately.
    let libFile := dest / (lib ++ ".lean")
    if ← libFile.pathExists then
      IO.FS.removeFile libFile
  -- And deletes the manifest from a previous generation: with no manifest
  -- `lake build` resolves dependencies on its own, but with a manifest that
  -- doesn't know about a now-required package it refuses ("missing
  -- manifest").
  let manifest := dest / "lake-manifest.json"
  if ← manifest.pathExists then
    IO.FS.removeFile manifest
  IO.FS.writeFile (dest / "lakefile.toml") (lakefileTemplate vol v pkgRequires extraLibs)
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md") (readmeTemplate vol v)
  for (relPath, body) in files do
    let target := dest / relPath
    target.parent.forM IO.FS.createDirAll
    IO.FS.writeFile target body

/-- Runs `lake build` inside `dest` and reports failure via `reportError`.
The `student` and `terse` variants have `sorry` on purpose, which is a
warning and not an error. -/
private def buildProject (dest : System.FilePath) (v : Variant) :
    BuildLogT IO Unit := do
  IO.println s!"Building generated project {v} at {dest}…"
  let res ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := dest
  }
  if res.exitCode != 0 then
    reportError <|
      s!"generated project {v} at {dest} failed to build " ++
      s!"(exit {res.exitCode}):\n--- stdout ---\n{res.stdout}\n" ++
      s!"--- stderr ---\n{res.stderr}"
  else
    IO.println s!"Generated project {v} built."

/-! ## Generated project's `import`s

The extracted project is a standalone Lake package, so each chapter's header
has to be rebuilt from the source chapter's header: infrastructure `import`s
are dropped (they build the book, not the student's code) and the rest is
kept. An external-package `import` (Mathlib) is kept, and the generated
`lakefile.toml` gets the matching `[[require]]`, pinned to `CSwL`'s own
`lake-manifest.json` revision. -/

/-- Authoring-infrastructure modules: their `import`s build the book and
must never appear in an extracted `.lean`. -/
private def frameworkPrefixes : List String :=
  ["VersoManual", "Verso", "Illuminate", "SubVerso", "CSwLMeta", "Bib", "Book"]

/-- Toolchain modules: they exist in any Lake project, so they stay as an
`import` line and never need a `[[require]]`. -/
private def corePrefixes : List String :=
  ["Lean", "Std", "Init"]

/-- Prefixes served by an external package: the `import` stays, and the
generated `lakefile.toml` has to `require` the package (pinned by
`manifestPin`). The package's Lake name is the lowercased prefix -- if a
chapter comes to import `Cslib.…`, this is where `"Cslib"` goes. -/
private def pkgPrefixes : List String :=
  ["Mathlib"]

/-- Support ("seed") modules copied verbatim into the extracted project --
today only `CSwLCompat` (the `sf_experiment`/`sf_expect_failure` macros used
by the ` ```lean -keep `/` ```lean +error ` fences; see
`bundleCompatSeed`). The `import` survives (it is not authoring
infrastructure, so `keepImport` already keeps it) but it is neither a
chapter nor an external package, so it needs its own category here --
without it, it would fall into the generic `reportError` below. -/
private def seedPrefixes : List String :=
  ["CSwLCompat"]

/-- Top-level namespace of a module name (`CSwL.Morphology.Phonemes` ⇒
`CSwL`). -/
private def modTop (m : String) : String := (m.splitOn ".").headD m

/-- Looks up package `name` in `CSwL`'s own `lake-manifest.json` and returns
`(git url, pinned rev)`, so the extracted project uses exactly the revision
the book is compiled with. -/
private def manifestPin (name : String) : IO (Option (String × String)) := do
  let .ok raw ← (IO.FS.readFile "lake-manifest.json").toBaseIO | return none
  let .ok json := Lean.Json.parse raw | return none
  let .ok pkgs := json.getObjVal? "packages" | return none
  let .ok arr := pkgs.getArr? | return none
  for p in arr do
    if (p.getObjValAs? String "name").toOption == some name then
      let .ok url := p.getObjValAs? String "url" | return none
      let .ok rev := p.getObjValAs? String "rev" | return none
      return some (url, rev)
  return none

/-- Should module `m` appear as an `import` in an extracted file? -/
private def keepImport (m : String) : Bool := ! frameworkPrefixes.contains (modTop m)

/-- The `import`s in a Lean source's header, reading only up to `#doc`. -/
private def headerImports (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for raw in src.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "#doc" then break
    if line.startsWith "import " then
      out := out.push ((line.drop 7).trimAscii.toString)
  return out

/-- Copies, verbatim, the support module(s) ("seeds") named in `usedSeeds`
into the extracted project. A minimal analogue of `sf-in-lean`'s
`bundleLoop` -- but not recursive, because `CSwL` only has one seed
(`CSwLCompat`), and it does not itself import anything besides the
toolchain (`Lean.Elab.BuiltinCommand`), so there is no second-order
dependency to follow. Returns the `(path, content)` pairs to add to the
chapter files, at the root of the generated project (`CSwLCompat.lean`, not
a directory -- the module itself, as in the source repository). -/
private def bundleCompatSeed (usedSeeds : List String) :
    IO (Array (String × String)) := do
  let mut out : Array (String × String) := #[]
  for seed in usedSeeds do
    let path := seed ++ ".lean"
    let content ← IO.FS.readFile path
    out := out.push (path, content)
  return out

/--
Shared implementation. Writes the extracted Lean project to
`_out/<variant>/lean/`, alongside the `html/` that `manualMain` generates as
`html-multi/` and `CSwLMeta.renameHtmlDir` renames (from
`cfg.destination := "_out/<variant>"`, see `CSwLMeta/Run.lean`). -/
private def emitSavedImpl (config : ExtractConfig) :
    Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  fun _mode _cfg _state text => do
    let width := Text.fillWidthFor <| config.variant
    let buf : SaveBuffers := walkOuter width config.modPrefix text {}
    let toolchain ← (IO.FS.readFile "lean-toolchain").toBaseIO >>= fun
      | .ok s => pure s
      | .error _ => pure "leanprover/lean4:v4.33.0-rc2\n"
    let rootFile := config.modPrefix ++ ".lean"
    -- Snapshot the buffer as a list, to be able to read the sources (IO)
    -- entry by entry.
    let entries := buf.fold (init := []) fun acc k v => (k, v) :: acc
    -- Emitted chapters: the buffer keys that have a path separator (the
    -- root, `CSwL.lean`, does not). `CSwL/Morphology.lean` ⇒
    -- `CSwL.Morphology` (the chapter's `chapterFileBase`/`file :=` --
    -- never the path of a section file it includes, like
    -- `CSwL/Morphology/Phonemes.lean`).
    let chapterModules := entries.map (·.1) |>.filter (·.any (· == '/'))
      |>.map fun k => ((k.dropEnd 5).toString).replace "/" "."
    -- Picks each file's variant and prefixes the chapter's `import` header,
    -- already stripped of the infrastructure ones.
    let mut files : Array (String × String) := #[]
    let mut usedPkgs : Array String := #[]
    let mut usedSeeds : Array String := #[]
    for (file, vs) in entries do
      let chosen := vs.get config.variant
      if file == rootFile then
        files := files.push (file, chosen)
      else
        -- The buffer key is the source chapter's path in the repository,
        -- so its header can be reread and the surviving `import`s
        -- re-emitted.
        let src ← (IO.FS.readFile file).toBaseIO >>= fun
          | .ok s => pure s
          | .error _ => pure ""
        -- An `import CSwL.Morphology.FinnishVowelHarmony` in the header
        -- of a "glue" chapter (one that only gathers sections living in
        -- their own file via `{include 1 ...}`) is neither infrastructure
        -- nor another chapter: it is a section whose content has already
        -- been merged into this same chapter's buffer by `walkSection`.
        -- There is no separate module for it in the extracted project
        -- (flattened, one file per chapter) -- the line has to fall here,
        -- before the classification below, or the generated project would
        -- have an `import` that does not resolve.
        let isIntraBookSection (i : String) : Bool :=
          modTop i == config.modPrefix && ! chapterModules.contains i
        let imps := (headerImports src).toList.filter keepImport
          |>.filter (! isIntraBookSection ·)
        for i in imps do
          let top := modTop i
          if pkgPrefixes.contains top then
            if ! usedPkgs.contains top then usedPkgs := usedPkgs.push top
          else if seedPrefixes.contains top then
            if ! usedSeeds.contains top then usedSeeds := usedSeeds.push top
          else if ! corePrefixes.contains top && ! chapterModules.contains i then
            -- Neither infrastructure, nor toolchain, nor a known external
            -- package, nor a support seed, nor another chapter: the
            -- generated project would have an `import` that does not
            -- resolve. Fail here, loudly (see cut 2 at the top).
            reportError <|
              s!"`import {i}` in {file} is not infrastructure, toolchain, " ++
              s!"a known external package, a support module, or a book " ++
              s!"chapter -- the extracted project under _out/ would not " ++
              s!"be able to resolve it. Add '{top}' to `pkgPrefixes` (with " ++
              s!"the package in lake-manifest.json) or to `seedPrefixes` " ++
              s!"(with the module in `bundleCompatSeed`), or remove the " ++
              s!"import from the chapter."
        -- A chapter with a ` ```lean -keep ` or ` ```lean +error ` block
        -- has, in the chosen variant, a call to
        -- `sf_experiment`/`sf_expect_failure` (emitted by `walkBlock` in
        -- `Save/Extract.lean`) -- but nothing here forces the source
        -- chapter's header to have `import CSwLCompat`. Without this
        -- check, the extractor would silently generate a project with the
        -- macro called and no `import` defining it: the error would only
        -- show up inside the extracted project's build ("unknown
        -- command"), not in the book's build. Fail here, loudly (same
        -- spirit as the unknown-`import` `reportError` above).
        let usesCompatMacro :=
          (chosen.splitOn "sf_experiment").length > 1 ||
          (chosen.splitOn "sf_expect_failure").length > 1
        if usesCompatMacro then
          if ! imps.any (seedPrefixes.contains ∘ modTop) then
            reportError <|
              s!"{file} uses ` ```lean -keep ` or ` ```lean +error ` " ++
              s!"(emits `sf_experiment`/`sf_expect_failure`) but the " ++
              s!"source chapter's header has no `import CSwLCompat` -- " ++
              s!"the extracted project would call a macro with no " ++
              s!"definition. Add `import CSwLCompat` to the chapter."
        let preamble := imps.foldl (init := "") fun acc i => acc ++ "import " ++ i ++ "\n"
        let preamble := if preamble.isEmpty then "" else preamble ++ "\n"
        files := files.push (file, preamble ++ chosen)
    -- A chapter that imports an external package (Mathlib) requires the
    -- matching `[[require]]` in the generated lakefile, at the book's own
    -- revision.
    let mut pkgRequires : Array (String × String × String) := #[]
    for pre in usedPkgs do
      let name := pre.toLower
      match ← manifestPin name with
      | .some (url, rev) => pkgRequires := pkgRequires.push (name, url, rev)
      | .none => reportError <|
          s!"package '{name}' (needed for `import {pre}.…` in an " ++
          s!"extracted chapter) is not in lake-manifest.json, so the " ++
          s!"extracted project has no way to pin it"
    -- Copies verbatim, into the extracted project, each seed named by some
    -- chapter (today, at most, `CSwLCompat`); each also becomes an extra
    -- `[[lean_lib]]` in the generated `lakefile.toml`.
    let seedFiles ← bundleCompatSeed usedSeeds.toList
    files := files ++ seedFiles
    let dest := System.FilePath.mk "_out" / config.variant.toString / "lean"
    writeProject dest toolchain config.modPrefix config.variant files pkgRequires usedSeeds
    if config.verify then buildProject dest config.variant

/-- `ExtraStep` for the `student` variant: answer keys elided (become
`sorry`). -/
def emitSavedStudent (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .student }

/-- `ExtraStep` for the `solutions` variant: answer keys shown. -/
def emitSavedSolutions (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .solutions }

/-- `ExtraStep` for the `terse` (lecture) variant: answer keys elided and
proofs marked with `workinclass!` become `sorry`, to be done live. -/
def emitSavedTerse (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .terse }

/-- `ExtraStep` for the `grading` variant: full proofs plus the
`[autogradedProof …]` attributes and the `import AutograderLib`. -/
def emitSavedGrading (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .grading }

end CSwLMeta.Save
