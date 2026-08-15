-- Adapted from /Users/ar/r/sf-in-lean/SFLMeta/Solution.lean
-- (namespace SFLMeta -> CSwLMeta). O original importa `SFLMeta.Save` só para
-- alcançar `SFLMeta.Variant` de carona (por causa do `getCurrVariant`); aqui o
-- import é direto, para não criar uma dependência de um módulo folha no
-- agregado Save/Extract/Project.
import VersoManual
import CSwLMeta.Variant

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output.Html

namespace CSwLMeta

/-!
`Block.solution` wraps a worked solution (prose or non-compiling illustrative
code) that should appear only in the *solutions* build. -/
block_extension Block.solution where
  data := Json.null
  traverse _ _ _ := do
    let variant ← getCurrVariant
    if variant.isSolution ∨ variant.isGrading then
      -- keep solution blocks in solution variant
      return none
    else
      return some (.concat #[])
  toHtml :=
    some fun _ goB _ _ contents =>
      Verso.Output.Html.seq <$> contents.mapM goB
  toTeX := none

@[directive]
def solution : DirectiveExpanderOf Unit
  | (), contents => do
    let blocks ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other CSwLMeta.Block.solution #[$blocks,*])

end CSwLMeta
