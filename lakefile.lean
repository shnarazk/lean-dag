import Lake
open Lake DSL

package «lean-dag» where
  testDriver := "«lean-dag-unit-tests»"
  -- moreLeanArgs := #["-Dlinter.all=true"] -- only if you want strict linting

@[default_target]
lean_lib «LeanDag» where
  precompileModules := true
  extraDepTargets := #[`«protocol-schema»]


/--  ## Dependencies -/

require «json-schema-to-lean» from git "https://codeberg.org/wvhulle/json-schema-to-lean" @ "main"

/-- Target that ensures lean-dag binary is built -/
target «lean-dag-bin» pkg : System.FilePath := do
  if let some exe := pkg.findLeanExe? `«lean-dag» then
    exe.exe.fetch
  else
    error "Could not find lean-dag executable"

/-- Track protocol-schema.json as a dependency for code generation -/
target «protocol-schema» pkg : System.FilePath := do
  let path := pkg.dir / "protocol-schema.json"
  inputTextFile path

/-! ## Test Libraries -/

/-- Unit tests - no external dependencies -/
lean_lib «Tests.Unit» where
  globs := #[.submodules `Tests.Unit]

/-- Run unit tests only (fast, no external dependencies) -/
lean_exe «lean-dag-unit-tests» where
  root := `Tests.Unit.Main
  supportInterpreter := true

/-- Integration tests - require lean-dag binary -/
lean_lib «Tests.Integration» where
  globs := #[.submodules `Tests.Integration]

/-- Run integration tests only (requires lean-dag binary) -/
lean_exe «lean-dag-integration-tests» where
  root := `Tests.Integration.Main
  supportInterpreter := true
  extraDepTargets := #[`«lean-dag-bin»]

/-- All tests -/
lean_lib «Tests» where
  globs := #[.one `Tests.Harness, .one `Tests.LspClient, .submodules `Tests.Unit, .submodules `Tests.Integration]

/-- Run all tests -/
lean_exe «lean-dag-tests» where
  root := `Tests.Main
  supportInterpreter := true
  extraDepTargets := #[`«lean-dag-bin»]


/-! ## Executables -/

lean_exe «lean-dag» where
  root := `Main
  supportInterpreter := true

/-- Debug tool for outputting GenericDag JSON from a file and position -/
lean_exe «print-json» where
  root := `PrintJsonMain
  supportInterpreter := true
