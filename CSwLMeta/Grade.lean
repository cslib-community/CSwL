-- Adapted from sf-in-lean/SFLMeta/Grade.lean
-- (namespace SFLMeta -> CSwLMeta; without the `:::grade`/`Block.grade`
-- directive, which is a noop and depends on `SFLMeta.Comment` -- only
-- `:::gradeTheorem` is included here).
import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace CSwLMeta

/-! ## `:::gradeTheorem` directive

`:::gradeTheorem <pts> <name>` records the point value and theorem name as
directive arguments, so the grading build's extractor can emit
`attribute [autogradedProof <pts>] <name>` for it. Like the rest of `Block.*`
grading machinery it is a noop for HTML/TeX (renders nothing); the arguments
survive in the Verso source and are consumed only by the extractor
(`Save/Extract.lean`). -/

/-- Author-facing configuration for `:::gradeTheorem`: a point value and the
name of the theorem to grade, both positional (`:::gradeTheorem 1 myThm`).
Points are kept as a *string* so fractional values (`0.5`, `0.25`) survive
exactly; write an integer bare (`1`) and a fraction quoted (`"0.5"`). -/
structure GradeTheoremConfig where
  /-- Points awarded for the theorem, as written (`1`, `"0.5"`). -/
  points : String
  /-- The names of the graded theorems. -/
  names : List Name
deriving Repr

section
variable [Monad m] [MonadError m] [MonadLiftT TermElabM m]

/-- A point value written either bare as a natural-number literal (`1`) or, for
a fractional value, as a quoted string (`"0.5"`); yields the value's text. -/
def ValDesc.pointsText : ValDesc m String where
  description := doc!"a point value (a number, or a quoted decimal)"
  signature := CanMatch.Num ∪ CanMatch.String
  get
    | .num n => Pure.pure (toString n.getNat)
    | .str s => Pure.pure s.getString
    | other => throwError "Expected a point value, got {toMessageData other}"

/-- Resolve a name using `InlineLean`'s scope (stored in an environment extension). -/
defmethod ValDesc.inlineLeanResolvedName : ValDesc m Name where
  description := doc!"a name resolved in the current inline Lean scope"
  signature := .Ident
  get
    | .name x => InlineLean.Scopes.runWithOpenDecls <| realizeGlobalConstNoOverloadWithInfo x
    | other => throwError "Expected identifier, got {other}"

/-- Argument parser for `GradeTheoremConfig` -/
def GradeTheoremConfig.parse : ArgParse m GradeTheoremConfig :=
  GradeTheoremConfig.mk
    <$> .positional `points ValDesc.pointsText <*> many1 (.positional `name .inlineLeanResolvedName)
where
  many1 p := (· :: ·) <$> p <*> .many p

instance : FromArgs GradeTheoremConfig m := ⟨GradeTheoremConfig.parse⟩

end

/-! `Block.gradeTheorem` records a `:::gradeTheorem <pts> <name>` grading
directive as structured `(points, name)` data. A noop for HTML/TeX (rendered
empty, dropped at elaboration for those); the spec survives verbatim for the
extractor. -/
block_extension Block.gradeTheorem (points : String) (names : List Name) where
  data := Json.arr #[.str points, .arr <| (names.map (Json.str ∘ Name.toString)).toArray]
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure .empty
  toTeX := none

@[directive]
def gradeTheorem : DirectiveExpanderOf GradeTheoremConfig
  | cfg, _contents => do
    ``(Verso.Doc.Block.other
        (CSwLMeta.Block.gradeTheorem $(quote cfg.points) $(quote cfg.names)) #[])

def decodeGradeTheoremData (data : Json) : String × Array Name :=
  match data with
  | .arr #[Json.str points, Json.arr names] => (
      points,
      names.map fun
        | .str s => s.toName
        | _ => unreachable!
    )
  | _ => unreachable!

end CSwLMeta
