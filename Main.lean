import CSwL.IntroL

/-- Executável do projeto. Por ora só confirma que a biblioteca carrega; a
partir do capítulo 5 ele hospeda o motor de inferência, que é interativo.
Importa {lit}`CSwL.IntroL` diretamente (não mais `import CSwL`): desde a
migração para o gênero {lit}`Manual`, `CSwL.lean` (a raiz da lib
{lit}`Literate`) não importa mais nenhum capítulo. -/
def main : IO Unit := do
  IO.println "CSwL — Computational Semantics with Lean"
  IO.println (IntroL.genS 3)
