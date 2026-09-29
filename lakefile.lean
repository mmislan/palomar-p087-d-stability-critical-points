import Lake
open Lake DSL
package palomarP087 where
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"
lean_lib ResearchProofs where
  roots := #[`proofs]
  globs := #[.submodules `proofs]
  leanOptions := #[⟨`warningAsError, true⟩]
lean_lib RegistryStatements where
  roots := #[`Registry]
  globs := #[.submodules `Registry]
