module

public import Lean.Util.Path

@[expose] public section

/-!
# Environment Discovery

Self-contained environment discovery for lean-dag standalone mode.
Instead of relying on the caller to set up LEAN_PATH and LEAN_SYSROOT via
`lake env`, lean-dag discovers these at startup by running `lake env printenv`.
-/

namespace LeanDag.Environment

/-- Run `lake env printenv VAR` to get an environment variable as Lake would set it. -/
def lakeEnvVar (varName : String) : IO (Option String) := do
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["env", "printenv", varName]
  }
  if output.exitCode == 0 then
    let value := output.stdout.trimAscii.toString
    return if value.isEmpty then none else some value
  else
    return none

/-- Discover LEAN_SYSROOT via `lake env printenv`, falling back to Lean.findSysroot. -/
def discoverSysroot : IO System.FilePath := do
  match ← lakeEnvVar "LEAN_SYSROOT" with
  | some sysroot => pure ⟨sysroot⟩
  | none => Lean.findSysroot

/-- Initialize environment: discover paths via `lake env printenv` if not already set. -/
def initEnvironment : IO Unit := do
  IO.eprintln "[LeanDag.Environment] Initializing environment..."

  let existingSysroot ← IO.getEnv "LEAN_SYSROOT"
  let existingLeanPath ← IO.getEnv "LEAN_PATH"

  let (sysroot, leanPath) ← match existingSysroot with
    | some _ =>
      IO.eprintln "[LeanDag.Environment] Using existing environment"
      pure (existingSysroot, existingLeanPath)
    | none =>
      IO.eprintln "[LeanDag.Environment] Discovering environment via `lake env printenv`..."
      let discoveredSysroot ← discoverSysroot
      let discoveredPath ← lakeEnvVar "LEAN_PATH"
      IO.eprintln s!"[LeanDag.Environment] Discovered LEAN_SYSROOT: {discoveredSysroot}"
      IO.eprintln s!"[LeanDag.Environment] Discovered LEAN_PATH: {discoveredPath}"
      pure (some discoveredSysroot.toString, discoveredPath)

  let sp := leanPath.map System.SearchPath.parse |>.getD []
  let libDir : System.FilePath := match sysroot with
    | some sr => ⟨sr⟩ / "lib" / "lean"
    | none => ⟨""⟩
  let fullPath := sp ++ [libDir]

  Lean.searchPathRef.set fullPath
  IO.eprintln s!"[LeanDag.Environment] Search path set: {fullPath}"

end LeanDag.Environment
