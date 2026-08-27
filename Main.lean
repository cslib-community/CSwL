import CSwL.IntroL

/-- Project executable. For now it only confirms that the library loads; from
chapter 5 on it will host the inference engine, which is interactive.
Imports {lit}`CSwL.IntroL` directly (no longer `import CSwL`): since the
migration to the {lit}`Manual` genre, `CSwL.lean` (the root of the
{lit}`Literate` lib) no longer imports any chapter. -/
def main : IO Unit := do
  IO.println "CSwL — Computational Semantics with Lean"
  IO.println (IntroL.genS 3)
