import Lake
open Lake DSL

package «demo» where

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

lean_lib «TestProject» where
  roots := #[`Basic, `Monadic, `Sorting]
