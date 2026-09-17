-- Adapted from sf-in-lean/SFLMeta/Diagrams.lean.
--
-- Vector diagrams used by the book chapters.
--
-- These live under `CSwLMeta` rather than beside the chapter that uses them
-- because they are authoring-framework code: the extracted `.lean` projects
-- drop `CSwLMeta` imports (a diagram is replaced there by its ASCII alt text),
-- whereas a module under a chapter prefix would be bundled into them verbatim,
-- carrying an `Illuminate` dependency the extracted project does not have.

import Illuminate

open Illuminate

namespace CSwLMeta.Diagrams

/--
A self-loop drawn above the node at `p`: a cubic that leaves the node's
upper left, arcs over it, and re-enters at the upper right.

This is built by hand because `commDiag`'s own arrows cannot draw one. For a
morphism whose source and target coincide, `buildArrow` computes a zero
direction vector, so both the bend offset (`bend * dir.length * 0.3`) and the
arrowhead direction collapse to zero: the emitted path is `M30 0 C30 0 30 0 30
0`, a curve from a point to itself, and nothing is visible.
-/
private def selfLoop (p : Vec2) : Diagram SVG :=
  let r : Float := 11        -- where the loop meets the node
  let h : Float := 18        -- how far above the node it arcs
  let start : Vec2 := ⟨p.x - r, p.y - r⟩
  let stop  : Vec2 := ⟨p.x + r, p.y - r⟩
  let c1    : Vec2 := ⟨p.x - h, p.y - h - r⟩
  let c2    : Vec2 := ⟨p.x + h, p.y - h - r⟩
  let shaft := Diagram.fromStroke
    (PathData.empty |>.moveTo start |>.curveTo c1 c2 stop)
    Stroke.defaultArrow
  let (head, _) := ArrowDraw.drawArrowhead ({} : Arrowhead) stop
                     (Vec2.sub stop c2) Stroke.defaultArrow
  Diagram.atop head shaft

/--
The directed graph of the model in `Logic/FOL`'s semantics section: four
vertices `a`, `b`, `c`, `d` and the edge relation
`{⟨a,b⟩, ⟨b,a⟩, ⟨b,c⟩, ⟨c,c⟩}`.

`a` and `b` point at each other, so their two arrows are bent apart to keep
both visible. `c` carries a loop, and `d` is isolated — it is the witness for
`∃x ∀y ¬E y x`, which is what the section's first example formula asserts.
-/
def edgeGraph : Diagram SVG :=
  let base : Diagram SVG := commDiag do
    let a ← CommDiagM.node "a"
    let b ← CommDiagM.node "b"
    let c ← CommDiagM.node "c"
    let d ← CommDiagM.node "d"
    CommDiagM.grid #[#[some a, some b, some c, some d]]
    CommDiagM.arrowWith a b { bend := 0.35 }
    CommDiagM.arrowWith b a { bend := 0.35 }
    CommDiagM.arrow b c
  -- `CommDiagM.node` names nodes `node_0`, `node_1`, … in creation order, so
  -- `c` is `node_2`; its position is only known once the grid is laid out.
  let cPos := (base.find (Lean.Name.mkSimple "node_2")).origin.toVec2
  Diagram.atop (selfLoop cPos) base

end CSwLMeta.Diagrams
