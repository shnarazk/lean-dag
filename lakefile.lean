import Lake
open Lake DSL

package «lean-dag» where

lean_lib «LeanDag» where

lean_lib «Tests» where
  globs := #[.submodules `Tests]

@[default_target]
lean_exe «lean-dag» where
  root := `Main
  supportInterpreter := true

lean_exe «lean-dag-tests» where
  root := `Tests.Main
  supportInterpreter := true

/-- Run tests after building the lean-dag binary (required for RPC integration tests) -/
@[test_driver]
script test do
  -- Build the lean-dag binary first (required by RPC integration tests at runtime)
  let buildResult ← IO.Process.run { cmd := "lake", args := #["build", "lean-dag"] }
  if !buildResult.isEmpty then IO.println buildResult
  -- Then run the test executable
  let exitCode ← IO.Process.spawn { cmd := ".lake/build/bin/lean-dag-tests" } >>= (·.wait)
  return exitCode
