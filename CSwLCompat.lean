-- Adapted from /Users/ar/r/sf-in-lean/SFLCompat.lean e
-- /Users/ar/r/sf-in-lean/SFLCompat/Experiment.lean, fundidos num arquivo só
-- (namespace SFLCompat.Experiment -> CSwLCompat). O CSwL não tem o mecanismo
-- `recall` do sf-in-lean (`SFLCompat/Recall/*.lean`), então nada de lá foi
-- portado -- só as macros `sf_experiment`/`sf_expect_failure`/
-- `sf_expect_failure?` que sustentam os fences ` ```lean -keep ` e
-- ` ```lean +error ` (veja `CSwLMeta/Save/Extract.lean`, `walkBlock`, e
-- `CSwLMeta/Save/Lean.lean`, `LeanSaved.Data.extractionMode`).
--
-- Duas diferenças deliberadas em relação ao original:
-- 1. Sem o `import Batteries.CodeAction` que o `SFLCompat.lean` raiz tinha: ele
--    existe para propagar code actions do Lean para o projeto gerado, mas o
--    `CSwL` não depende de `batteries` (só de `cslib`/Mathlib) -- puxar
--    `batteries` só para isso infla o projeto extraído sem necessidade.
-- 2. Sem o `namespace Tests` do fim do `SFLCompat/Experiment.lean` original:
--    são `#guard_msgs` que conferem o texto exato de diagnósticos do Lean
--    ("Unknown identifier `x`", posições literais por `(positions := true)`,
--    etc.). O `CSwL` está no mesmo `v4.33.0` do `sf-in-lean` hoje, mas fixar
--    esse texto aqui arrisca quebrar tanto o build do livro quanto o de todo
--    projeto extraído (o arquivo é copiado verbatim) a cada drift de
--    mensagem entre versões do Lean -- sem ganho para o curso, que não usa
--    `recall` nem testa essas macros diretamente.
--
-- Este arquivo é o "seed" copiado verbatim para `_out/<variante>/lean/` por
-- `CSwLMeta/Save/Project.lean` (função `bundleCompatSeed`) sempre que algum
-- capítulo extraído tiver `import CSwLCompat` no cabeçalho.

module

public meta import Lean.Elab.BuiltinCommand

namespace CSwLCompat

open Lean Elab Command

meta section

-- Copiado de `SubVerso.Compat` para não fazer os projetos gerados dependerem
-- do Verso. Precisamos que o estado de info e as mensagens estejam
-- disponíveis logo após a elaboração, então desligamos `Elab.async`, que
-- deixaria diagnósticos passarem de forma assíncrona via snapshot tasks.
private def commandWithoutAsync (act : CommandElabM Unit) : CommandElabM Unit := do
  match (← get).scopes with
  | [] => act
  | h :: t =>
    let mut orig : Option Bool := none
    try
      orig := h.opts.get? `Elab.async
      modify fun s => { s with scopes := { h with opts := h.opts.setBool `Elab.async false } :: t }
      act
    finally
      if let h :: t := (← get).scopes then
        let opts := orig.map (h.opts.setBool `Elab.async) |>.getD (h.opts.erase `Elab.async)
        modify fun s => { s with scopes := { h with opts := opts } :: t }

private def withRestoringState (keepMsgs : Bool) (m : CommandElabM Unit) : CommandElabM Unit := do
  let savedState ← get
  try
    m
  finally
    let state ← get
    set { savedState with
      -- Preserva a árvore de informação.
      infoState := state.infoState
      messages := if keepMsgs then state.messages else savedState.messages }

namespace IndentedCommands

/-! ## Parser de bloco de comandos indentado
  Faz o parse de um bloco de comandos indentado, separados por linhas.
  Como queremos capturar erros de parse em `sf_expect_failure`, não podemos
  usar o parser de comandos do Lean diretamente na sintaxe do nosso comando,
  porque um erro de parse ali derrubaria o próprio `sf_expect_failure`. A
  solução é fazer o parse do corpo indentado inteiro como sintaxe bruta
  primeiro, e só depois rodar o parser e o elaborador de comandos do Lean. -/

open Parser

private def rawLineEndFn : ParserFn :=
  eoiFn <|> satisfyFn (· == '\n') "line break"

/-- Consome tudo até a próxima quebra de linha e então a própria quebra. -/
private def rawLineFn : ParserFn :=
  takeUntilFn (· == '\n') >> rawLineEndFn

/- Para cada linha depois da primeira linha do corpo, consome os espaços à
  esquerda. Se a linha for em branco, consome só a quebra de linha; senão,
  consome a linha exigindo a indentação. -/
private def rawIndentedLineFn : ParserFn := atomicFn <|
  takeWhileFn (· == ' ') >>
  (satisfyFn (· == '\n') "line break" <|>
    (checkColGeFn "indented command sequence" >> rawLineFn))

private def rawCommandBlockFn : ParserFn :=
  rawFn (rawLineFn >> manyFn rawIndentedLineFn) (trailingWs := true)

private def rawCommandBlock : Parser := { fn := rawCommandBlockFn }

@[combinator_parenthesizer rawCommandBlock]
private def rawCommandBlock.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter rawCommandBlock]
private def rawCommandBlock.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

private partial def runRawCmdsAux
    (ictx : InputContext) (pstate : ModuleParserState) : CommandElabM Unit := do
  let state ← get
  let scope := state.scopes.head!
  let pctx :=  {
      env := state.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls : ParserModuleContext
    }
  let (cmd, pstate, messages) := parseCommand ictx pctx pstate state.messages
  modify fun state => { state with messages }
  unless cmd.isOfKind ``Command.eoi do
    elabCommand cmd
    runLinters cmd
    unless isTerminalCommand cmd do
      runRawCmdsAux ictx pstate

/- Recupera a origem e elabora os comandos. -/
private def runRawCmds (body : Syntax) : CommandElabM Unit := do
  let some source := body.getSubstring? (withLeading := false) (withTrailing := false)
    | throwErrorAt body "command sequence has no source range"
  let fileName ← getFileName
  let fileMap ← getFileMap
  -- `rawIndentedLineFn` pode consumir espaços depois da quebra de linha;
  -- aqui recuamos o fim até o último caractere não-espaço para produzir
  -- diagnósticos com a posição correta.
  let stopPos := source.trimRight.stopPos
  if h : stopPos ≤ fileMap.source.rawEndPos then
    let ictx := InputContext.mk fileMap.source fileName
      (fileMap := fileMap) (endPos := stopPos) (endPos_valid := h)
    runRawCmdsAux ictx { pos := source.startPos, recovering := false, hasLeading := false }
  else
    throwErrorAt body "invalid command-sequence source range"

end IndentedCommands

end

public meta section

open Parser IndentedCommands

/--
Elabora os comandos internos e reporta seus diagnósticos, mas descarta os
efeitos depois.

Exemplo:
```lean
sf_experiment
  def hidden : Nat := 1
  #check hidden
-- `hidden` não está disponível aqui.
```
-/
def experimentTk := leading_parser
  "sf_experiment"

@[command_parser] def experimentCmd := leading_parser
  experimentTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

/--
Só é bem-sucedido se os comandos internos falharem.
Os diagnósticos da falha esperada são suprimidos.

Exemplo:
```lean
sf_expect_failure
  example : 1 = 2 := rfl
```
-/
def expectFailureTk := leading_parser
  "sf_expect_failure"

/-
  Como `sf_expect_failure`, mas reporta os diagnósticos.
-/
def expectFailureInfoTk := leading_parser
  "sf_expect_failure?"

@[command_parser] def expectFailureCmd := leading_parser
  expectFailureTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_parser] def expectFailureInfoCmd := leading_parser
  expectFailureInfoTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_elab experimentCmd]
def elabExperimentCmd : CommandElab := fun stx => do
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState true do
    runRawCmds body

@[command_elab expectFailureCmd, command_elab expectFailureInfoCmd]
def elabExpectFailureCmd : CommandElab := fun stx => do
  let keepMsgs := stx.isOfKind ``expectFailureInfoCmd
  unless keepMsgs || stx.isOfKind ``expectFailureCmd do
    throwUnsupportedSyntax
  let tk := stx[0]
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState keepMsgs do
    withRef tk <| failIfSucceeds <| runRawCmds body

end

end CSwLCompat
