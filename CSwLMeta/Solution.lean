-- Adapted from sf-in-lean/SFLMeta/Solution.lean
-- (namespace SFLMeta -> CSwLMeta). The original imports `SFLMeta.Save` only
-- to reach `SFLMeta.Variant` along the way (because of `getCurrVariant`);
-- here the import is direct, to avoid creating a dependency on a leaf
-- module from the Save/Extract/Project aggregate.
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
