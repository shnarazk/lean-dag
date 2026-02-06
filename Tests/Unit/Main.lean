import Tests.Unit.ProofDag
import Tests.Unit.ProofState
import Tests.Unit.FunctionalDagTestHarness
import Tests.Unit.FunctionalDagUI
import Tests.Unit.EffectFlowPosition

def main : IO Unit := do
  IO.println "LeanDag Unit Tests"
  IO.println "=================="

  -- Unit tests (no external dependencies)
  Tests.Unit.ProofDag.runTests
  Tests.Unit.ProofState.runTests
  Tests.Unit.FunctionalDagUI.runTests
  Tests.Unit.EffectFlowPosition.runTests

  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "  All unit tests passed"
  IO.println "══════════════════════════════════════════════════════════════"
