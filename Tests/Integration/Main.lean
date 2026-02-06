import Tests.Integration.Basic
import Tests.Integration.ProofDag
import Tests.Integration.Boundary
import Tests.Integration.Tactics
import Tests.Integration.Unicode

unsafe def main : IO Unit := do
  IO.println "LeanDag Integration Tests"
  IO.println "========================="

  -- RPC integration tests (require lean-dag binary)
  Tests.Integration.Basic.runTests
  Tests.Integration.ProofDag.runTests
  Tests.Integration.Boundary.runTests
  Tests.Integration.Tactics.runTests
  Tests.Integration.Unicode.runTests

  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "  All integration tests passed"
  IO.println "══════════════════════════════════════════════════════════════"
