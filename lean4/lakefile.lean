import Lake
open Lake DSL

package CohesionPowerIndices where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib CohesionIndices where
  srcDir := "CohesionIndices"

lean_lib Aristotle where
  srcDir := "Aristotle"
