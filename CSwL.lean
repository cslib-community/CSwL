/-!
# Computational Semantics with Lean

Root module of the `CSwL` library. The book itself is assembled in
`Book.lean`, in Verso's `Manual` genre, and every chapter lives under
`CSwL/`; nothing is imported here.

The file stays because `[[lean_lib]] name = "CSwL"` in `lakefile.toml`
requires a root module, and the `Book`/doc-gen4 target still uses that
library.
-/
