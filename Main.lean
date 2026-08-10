import CSwL

/-- Executável do projeto. Por ora só confirma que a biblioteca carrega; a
partir do capítulo 5 ele hospeda o motor de inferência, que é interativo. -/
def main : IO Unit := do
  IO.println "CSwL — Computational Semantics with Lean"
  IO.println (Chapter02.genS 3)
