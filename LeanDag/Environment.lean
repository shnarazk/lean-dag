module

public import Lean.Util.Path
public import LeanDag.Logging

@[expose] public section

/-!
# Environment Discovery

Self-contained environment discovery for lean-dag standalone mode.
Instead of relying on the caller to set up LEAN_PATH and LEAN_SYSROOT via
`lake env`, lean-dag discovers these at startup by running `lake env printenv`.
-/

namespace LeanDag.Environment

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

def discoverSysroot : IO System.FilePath := do
  match ← lakeEnvVar "LEAN_SYSROOT" with
  | some sysroot => pure ⟨sysroot⟩
  | none => Lean.findSysroot

def initEnvironment : IO Unit := do
  log! "[LeanDag.Environment] Initializing environment..."

  let existingSysroot ← IO.getEnv "LEAN_SYSROOT"
  let existingLeanPath ← IO.getEnv "LEAN_PATH"

  let (sysroot, leanPath) ← match existingSysroot with
    | some _ =>
      log! "[LeanDag.Environment] Using existing environment"
      pure (existingSysroot, existingLeanPath)
    | none =>
      log! "[LeanDag.Environment] Discovering environment via `lake env printenv`..."
      let discoveredSysroot ← discoverSysroot
      let discoveredPath ← lakeEnvVar "LEAN_PATH"
      log! s!"[LeanDag.Environment] Discovered LEAN_SYSROOT: {discoveredSysroot}"
      log! s!"[LeanDag.Environment] Discovered LEAN_PATH: {discoveredPath}"
      pure (some discoveredSysroot.toString, discoveredPath)

  let sp := leanPath.map System.SearchPath.parse |>.getD []
  let libDir : System.FilePath := match sysroot with
    | some sr => ⟨sr⟩ / "lib" / "lean"
    | none => ⟨""⟩
  let fullPath := sp ++ [libDir]

  Lean.searchPathRef.set fullPath
  log! s!"[LeanDag.Environment] Search path set: {fullPath}"

end LeanDag.Environment
