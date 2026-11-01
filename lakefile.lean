import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

package tltt where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]

@[default_target]
lean_lib Tltt where

lean_lib Misc where

lean_lib Finite where

@[test_driver]
lean_lib TlttTests where
