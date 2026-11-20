import VersoManual
import CSwLMeta.Exercise

/-!
# Cross-references to sections and exercises

`{cref "tag"}[text]` links to the section whose `tag` is `"tag"` or to the
exercise whose `name` is `"tag"`. With empty brackets, `{cref "tag"}[]`, the
link text is generated: the section's title, or the exercise's name in code.
The text therefore follows the title when the title changes. Nothing else is
added: the prose names the kind of target, as in "no exercício {cref …}[]".

The text is generated during traversal, by replacing the node with one that
carries the text as its content. The HTML and the extracted Lean projects
(`CSwLMeta/Save`), which render an inline's content, both see it.

A tag that names neither a section nor an exercise, or that names both, is
reported as an error.
-/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output Verso.Output.Html

namespace CSwLMeta

/-- The target of a cross-reference: where it links and the text to show
when the reference brings none. -/
structure CrefTarget where
  /-- The URL of the target. -/
  href : String
  text : Array (Verso.Doc.Inline Manual)

/-- Resolve `name` among the section tags and the exercise names. -/
def resolveCref (st : TraverseState) (name : String) :
    Except String CrefTarget := do
  let sec? := st.getDomainObject? sectionDomain name
  let ex? := st.getDomainObject? exerciseDomain name
  match sec?, ex? with
  | some _, some _ =>
    throw s!"'{name}' is both a section tag and an exercise name"
  | some obj, none =>
    let title := (obj.data.getObjValAs? String "title").toOption.getD name
    match st.resolveDomainObject sectionDomain name with
    | .error e => throw e
    | .ok dest => return { href := dest.link, text := #[.text title] }
  | none, some _ =>
    match st.resolveDomainObject exerciseDomain name with
    | .error e => throw e
    | .ok dest =>
      return { href := dest.link, text := #[.code name] }
  | none, none =>
    throw s!"No section tag or exercise name '{name}'"

-- A cross-reference to the section or exercise `name`.
inline_extension Inline.cref (name : String) where
  data := toJson name
  -- With empty content, fill in the generated text once the target is known.
  -- An unknown target is left alone here: a later pass may register it, and
  -- `toHtml` reports it if none does.
  traverse _ data content := do
    let .ok (name : String) := fromJson? data | pure none
    unless content.isEmpty do return none
    match resolveCref (← get) name with
    | .ok tgt => return some (.other (Inline.cref name) tgt.text)
    | .error _ => return none
  toHtml :=
    some fun go _ data content => do
      let .ok (name : String) := fromJson? data
        | reportError s!"Bad cref data {data}"; content.mapM go
      match resolveCref (← Doc.Html.HtmlT.state) name with
      | .ok tgt =>
        let body ← (if content.isEmpty then tgt.text else content).mapM go
        return {{<a href={{tgt.href}}>{{body}}</a>}}
      | .error e =>
        reportError e
        content.mapM go
  toTeX :=
    some fun go _ _ content => content.mapM go

structure CrefArgs where
  name : String

instance [Monad m] [MonadError m] : FromArgs CrefArgs m where
  fromArgs := CrefArgs.mk <$> .positional `name .string

/-- `{cref "tag"}[text]` links to a section or exercise; `{cref "tag"}[]`
generates the text. -/
@[role]
def cref : RoleExpanderOf CrefArgs
  | {name}, content => do
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (CSwLMeta.Inline.cref $(quote name))
        #[$content,*])

end CSwLMeta
