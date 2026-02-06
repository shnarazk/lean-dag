import Lean
import LeanDag
import Tests.Harness
import Tests.Unit.FunctionalDagTestHarness

namespace Tests.Unit.FunctionalDagUI

open Lean LeanDag Tests.Harness Tests.Unit.FunctionalDagTestHarness

/-! ## FunctionalDag Builder Tests (Real Elaboration)

These tests elaborate real Lean code and verify that the functional DAG
builder correctly processes do-blocks (the main user-facing feature).
-/

/-!
### Test 1: Do-Block Monadic Binds - ARE captured as letE

Monadic `let a ← expr` binds elaborate to letE expressions with bind calls.
The test verifies these are captured.
-/
def testDoBlockMonadicBinds : IO Unit := do
  printSubsection "Do-Block Monadic Binds"

  let code := "import Init
def monadicComputation (x : Nat) : Option Nat := do
  let a ← some x
  let b ← some (a + 1)
  pure b
"
  let result ← assertElaborates code
  -- Monadic binds elaborate to letE expressions wrapping bind calls
  -- Each `let a ← expr` produces a letE, plus lambdas for continuations
  assertAtLeastSignificantTerms result 2  -- Should capture 2 letE for the monadic binds

/-!
### Test 2: Do-Block full pipeline - Debug why UI shows empty DAG

This test inspects the full pipeline to find where the bug is:
1. isTermModeTree - does it pass?
2. isSignificantTerm - are terms captured?
3. Both must work for DAG to be non-empty
-/
def testDoBlockFullPipeline : IO Unit := do
  printSubsection "Do-Block Full Pipeline Debug"

  let code := "import Init
def computation (a b : Nat) : Option Nat := do
  let x ← some a
  let y ← some (x + b)
  pure y
"
  let result ← assertElaborates code

  -- Debug dump all InfoTrees
  IO.println s!"  Total InfoTrees: {result.infoTrees.size}"
  for h : idx in [:result.infoTrees.size] do
    debugInfoTree result.infoTrees[idx] idx

  -- Check isTermModeTree
  assertIsTermModeTree result

  -- Check significant terms are captured
  let sigCount := countSignificantTerms result
  IO.println s!"  Significant terms captured: {sigCount}"
  if sigCount == 0 then
    IO.println s!"  BUG: No significant terms captured from do-block!"
    IO.println s!"    significant kinds: {getSignificantExprKinds result}"
    throw <| IO.userError "Do-block should have significant terms (letE from monadic binds)"

  assertAtLeastSignificantTerms result 2  -- Should have at least 2 letE from `let x ←` and `let y ←`

/-! ## Test Runner -/

def runTests : IO Unit := do
  printSection "FunctionalDag Builder Tests (Real Elaboration)"

  testDoBlockMonadicBinds
  testDoBlockFullPipeline

  IO.println "\n  ✓ FunctionalDag builder tests completed"

end Tests.Unit.FunctionalDagUI
