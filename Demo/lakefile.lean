import Lake
open Lake DSL

package «demo» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"

lean_lib «TestProject» where
  roots := #[`Basic]
