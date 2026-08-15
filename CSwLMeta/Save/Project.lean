-- Adapted from /Users/ar/r/sf-in-lean/SFLMeta/Save/Project.lean.
--
-- Escreve, para cada variante, um projeto Lake autônomo em
-- `_out/<variante>/lean/`: os `.lean` extraídos do livro, mais um
-- `lakefile.toml`, um `lean-toolchain` e um `README.md`. É esse projeto gerado
-- — e só ele — que depende do `lean4-autograder-main`, na variante `grading`;
-- no `lakefile.toml` do `CSwL` o autograder não entra (colide com o Mathlib que
-- o `cslib` traz; veja o comentário do `[[lean_exe]] cswl-book`).
--
-- Quatro cortes deliberados em relação ao original do `sf-in-lean`, todos por
-- não ter equivalente no `CSwL`:
--
-- 1. Sem módulo de apoio (`SFLCompat.lean`): ele existe para levar as macros
--    `sf_experiment`/`sf_expect_failure` ao projeto gerado, e o `CSwL` não usa
--    nenhuma das duas. ATENÇÃO ao converter um capítulo: o extrator ainda tem
--    os ramos que envolvem o código nessas macros, para blocos escritos como
--    ` ```lean -keep ` ou ` ```lean +error ` (veja `Save/Extract.lean`). Um
--    bloco assim geraria, no projeto extraído, uma macro sem definição. Ou não
--    se usam esses dois modificadores, ou é preciso portar o `SFLCompat.lean`
--    do `sf-in-lean` junto.
-- 2. Sem `crossVol`: o `sf-in-lean` tem três volumes, e capítulos de um
--    importam capítulos de outro. O `CSwL` é um livro só.
-- 3. Sem `bundleLoop`: o original copia, verbatim, o fonte de um módulo
--    pré-requisito que não seja capítulo nem pacote externo (no `sf-in-lean`,
--    coisas como `LF/CustomTactics.lean`). O `CSwL` não tem nenhum módulo
--    assim: um capítulo importa Mathlib e mais nada. Em vez de portar o
--    empacotamento, um `import` desses vira erro de build do livro — falha
--    ruidosa, em vez de um projeto gerado com `import` que não resolve.
-- 4. Sem `mergeAdjacentModuleDocs`: o original junta blocos `/-! … -/`
--    adjacentes, e o nosso extrator escreve a prosa como linhas `--`.

import VersoManual

import CSwLMeta.Variant

import CSwLMeta.Save.Extract

open Verso Doc Genre Manual

namespace CSwLMeta.Save

/-- Revisão do `lean4-autograder-main` usada pelo projeto gerado da variante
`grading`. É a mesma que o spike de validação testou. -/
def autograderRev : String := "comparator-4.33.0"

def autograderUrl : String := "https://github.com/plclub/lean4-autograder-main"

structure ExtractConfig where
  /-- Prefixo de módulo (e diretório) dos capítulos: `CSwL`. -/
  modPrefix : String
  variant : Variant
  /-- Rodar `lake build` dentro do projeto gerado, para conferir que ele
  compila sozinho. Fica `false` por dois motivos, os dois medidos e não
  hipotéticos: (a) os capítulos importam Mathlib, então o projeto gerado
  compilaria Mathlib do zero a cada `make`; (b) na variante `grading` o
  autograder exige o toolchain `v4.33.0` e o nosso é `v4.33.0-rc2` — o mesmo
  descasamento que tirou o autograder do `lakefile.toml` do `CSwL`, e que
  continua em aberto para os capítulos reais (o `Placeholder` não importa
  Mathlib, então nele o projeto `grading` gerado é autograder puro). -/
  verify : Bool := false

/-! ## Molde do projeto Lake gerado -/

/-- Conteúdo do `lakefile.toml` do projeto gerado. `pkgRequires` lista os
pacotes externos `(nome, url git, rev)` de que algum capítulo extraído precisa
(por ex. o Mathlib de `import Mathlib.Tactic`), cada um fixado na mesma revisão
com que o livro é compilado — lida do `lake-manifest.json` do `CSwL`. -/
private def lakefileTemplate (vol : String) (v : Variant)
    (pkgRequires : Array (String × String × String)) : String :=
  let pkgRequires := if v.isGrading
    then pkgRequires.push ("autograder", autograderUrl, autograderRev)
    else pkgRequires
  let reqs := pkgRequires.foldl (init := "") fun acc (name, url, rev) =>
    acc ++ "\n[[require]]\nname = \"" ++ name ++ "\"\ngit = \"" ++ url ++
      "\"\nrev = \"" ++ rev ++ "\"\n"
  "name = \"" ++ vol.toLower ++ "-extracted\"\n" ++
  "version = \"0.1.0\"\n" ++
  "defaultTargets = [\"" ++ vol ++ "\"]\n" ++
  reqs ++
  "\n[[lean_lib]]\n" ++
  "name = \"" ++ vol ++ "\"\n"

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

/-- Escreve o projeto gerado em `dest`: os arquivos extraídos, mais
`lakefile.toml`, `lean-toolchain` e `README.md`. -/
private def writeProject (dest : System.FilePath) (toolchain : String)
    (vol : String) (v : Variant) (files : Array (String × String))
    (pkgRequires : Array (String × String × String)) : IO Unit := do
  IO.FS.createDirAll dest
  -- Limpa a árvore de fontes para que um capítulo renomeado ou removido não
  -- fique como órfão de uma geração anterior. O resto (`.lake`,
  -- `lakefile.toml`, `lean-toolchain`, `README.md`) fica onde está.
  let libRoot := dest / vol
  if ← libRoot.pathExists then
    IO.FS.removeDirAll libRoot
  -- E apaga o manifesto de uma geração anterior: sem manifesto o `lake build`
  -- resolve as dependências sozinho, mas com um manifesto que não conhece um
  -- pacote agora exigido ele recusa ("missing manifest").
  let manifest := dest / "lake-manifest.json"
  if ← manifest.pathExists then
    IO.FS.removeFile manifest
  IO.FS.writeFile (dest / "lakefile.toml") (lakefileTemplate vol v pkgRequires)
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md") (readmeTemplate vol v)
  for (relPath, body) in files do
    let target := dest / relPath
    target.parent.forM IO.FS.createDirAll
    IO.FS.writeFile target body

/-- Roda `lake build` dentro de `dest` e reporta a falha via `reportError`.
As variantes `student` e `terse` têm `sorry` de propósito, que é aviso e não
erro. -/
private def buildProject (dest : System.FilePath) (v : Variant) :
    BuildLogT IO Unit := do
  IO.println s!"Compilando o projeto {v} gerado em {dest}…"
  let res ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := dest
  }
  if res.exitCode != 0 then
    reportError <|
      s!"o projeto {v} gerado em {dest} não compilou " ++
      s!"(saída {res.exitCode}):\n--- stdout ---\n{res.stdout}\n" ++
      s!"--- stderr ---\n{res.stderr}"
  else
    IO.println s!"Projeto {v} gerado compilou."

/-! ## `import`s do projeto gerado

O projeto extraído é um pacote Lake autônomo, então o cabeçalho de cada
capítulo tem de ser reconstruído a partir do cabeçalho do capítulo-fonte:
descartam-se os `import`s da infraestrutura (eles constroem o livro, não o
código do aluno) e mantém-se o resto. Um `import` de pacote externo (Mathlib) é
mantido, e o `lakefile.toml` gerado ganha o `[[require]]` correspondente,
fixado na revisão do `lake-manifest.json` do `CSwL`. -/

/-- Módulos da infraestrutura de autoria: seus `import`s constroem o livro e
nunca podem aparecer num `.lean` extraído. -/
private def frameworkPrefixes : List String :=
  ["VersoManual", "Verso", "Illuminate", "SubVerso", "CSwLMeta", "Bib", "Book"]

/-- Módulos do toolchain: existem em qualquer projeto Lake, então continuam
como linha de `import` e nunca precisam de `[[require]]`. -/
private def corePrefixes : List String :=
  ["Lean", "Std", "Init"]

/-- Prefixos servidos por um pacote externo: o `import` fica, e o
`lakefile.toml` gerado tem de `require` o pacote (fixado por `manifestPin`).
O nome Lake do pacote é o prefixo em minúsculas — se um capítulo passar a
importar `Cslib.…`, é aqui que `"Cslib"` entra. -/
private def pkgPrefixes : List String :=
  ["Mathlib"]

/-- Namespace de topo de um nome de módulo (`CSwL.Chapter02` ⇒ `CSwL`). -/
private def modTop (m : String) : String := (m.splitOn ".").headD m

/-- Procura o pacote `name` no `lake-manifest.json` do próprio `CSwL` e devolve
`(url git, rev fixada)`, para que o projeto extraído use exatamente a revisão
com que o livro é compilado. -/
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

/-- O módulo `m` deve aparecer como `import` num arquivo extraído? -/
private def keepImport (m : String) : Bool := ! frameworkPrefixes.contains (modTop m)

/-- Os `import`s do cabeçalho de um fonte Lean, lendo só até o `#doc`. -/
private def headerImports (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for raw in src.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "#doc" then break
    if line.startsWith "import " then
      out := out.push ((line.drop 7).trimAscii.toString)
  return out

/--
Implementação comum. Escreve o projeto Lean extraído em
`_out/<variante>/lean/`, ao lado do `html-multi/` que o `manualMain` gera (a
partir de `cfg.destination := "_out/<variante>"`, veja `CSwLMeta/Run.lean`). -/
private def emitSavedImpl (config : ExtractConfig) :
    Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  fun _mode _cfg _state text => do
    let width := Text.fillWidthFor <| config.variant
    let buf : SaveBuffers := walkOuter width config.modPrefix text {}
    let toolchain ← (IO.FS.readFile "lean-toolchain").toBaseIO >>= fun
      | .ok s => pure s
      | .error _ => pure "leanprover/lean4:v4.33.0-rc2\n"
    let rootFile := config.modPrefix ++ ".lean"
    -- Instantâneo do buffer como lista, para poder ler os fontes (IO) entrada
    -- a entrada.
    let entries := buf.fold (init := []) fun acc k v => (k, v) :: acc
    -- Capítulos emitidos: as chaves de buffer que têm separador de caminho (a
    -- raiz, `CSwL.lean`, não tem). `CSwL/Chapter02.lean` ⇒ `CSwL.Chapter02`.
    let chapterModules := entries.map (·.1) |>.filter (·.any (· == '/'))
      |>.map fun k => ((k.dropEnd 5).toString).replace "/" "."
    -- Escolhe a variante de cada arquivo e prefixa o cabeçalho de `import`s do
    -- capítulo, já sem os da infraestrutura.
    let mut files : Array (String × String) := #[]
    let mut usedPkgs : Array String := #[]
    for (file, vs) in entries do
      let chosen := vs.get config.variant
      if file == rootFile then
        files := files.push (file, chosen)
      else
        -- A chave do buffer é o caminho do capítulo-fonte no repositório, então
        -- dá para reler o cabeçalho dele e reemitir os `import`s que ficam.
        let src ← (IO.FS.readFile file).toBaseIO >>= fun
          | .ok s => pure s
          | .error _ => pure ""
        let imps := (headerImports src).toList.filter keepImport
        for i in imps do
          let top := modTop i
          if pkgPrefixes.contains top then
            if ! usedPkgs.contains top then usedPkgs := usedPkgs.push top
          else if ! corePrefixes.contains top && ! chapterModules.contains i then
            -- Nem infraestrutura, nem toolchain, nem pacote externo conhecido,
            -- nem outro capítulo: o projeto gerado teria um `import` que não
            -- resolve. Falha aqui, ruidosamente (veja o corte 3 no topo).
            reportError <|
              s!"`import {i}` em {file} não é infraestrutura, toolchain, " ++
              s!"pacote externo conhecido nem capítulo do livro — o projeto " ++
              s!"extraído em _out/ não conseguiria resolvê-lo. Acrescente " ++
              s!"'{top}' a `pkgPrefixes` (com o pacote no lake-manifest.json) " ++
              s!"ou tire o import do capítulo."
        let preamble := imps.foldl (init := "") fun acc i => acc ++ "import " ++ i ++ "\n"
        let preamble := if preamble.isEmpty then "" else preamble ++ "\n"
        files := files.push (file, preamble ++ chosen)
    -- Um capítulo que importa pacote externo (Mathlib) exige o `[[require]]`
    -- correspondente no lakefile gerado, na revisão do próprio livro.
    let mut pkgRequires : Array (String × String × String) := #[]
    for pre in usedPkgs do
      let name := pre.toLower
      match ← manifestPin name with
      | .some (url, rev) => pkgRequires := pkgRequires.push (name, url, rev)
      | .none => reportError <|
          s!"o pacote '{name}' (preciso para `import {pre}.…` num capítulo " ++
          s!"extraído) não está no lake-manifest.json, então o projeto " ++
          s!"extraído não tem como fixá-lo"
    let dest := System.FilePath.mk "_out" / config.variant.toString / "lean"
    writeProject dest toolchain config.modPrefix config.variant files pkgRequires
    if config.verify then buildProject dest config.variant

/-- `ExtraStep` da variante `student`: gabaritos elididos (viram `sorry`). -/
def emitSavedStudent (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .student }

/-- `ExtraStep` da variante `solutions`: gabaritos à mostra. -/
def emitSavedSolutions (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .solutions }

/-- `ExtraStep` da variante `terse` (aula): gabaritos elididos e provas
marcadas com `workinclass!` viram `sorry`, para serem feitas ao vivo. -/
def emitSavedTerse (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .terse }

/-- `ExtraStep` da variante `grading`: provas completas mais os atributos
`[autogradedProof …]` e o `import AutograderLib`. -/
def emitSavedGrading (vol : String) :=
  emitSavedImpl { modPrefix := vol, variant := .grading }

end CSwLMeta.Save
