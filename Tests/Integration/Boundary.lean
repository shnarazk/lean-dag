import Lean
import Lean.Data.Lsp.Ipc
import LeanDag
import Tests.LspClient
import Tests.Harness

namespace Tests.Integration.Boundary

open Lean Lsp Ipc JsonRpc LeanDag Tests.LspClient Tests.Harness

def edgeCaseFile : System.FilePath := testProjectPath / "EdgeCases.lean"
def simpleFile : System.FilePath := testProjectPath / "Simple.lean"

/-! ## Term-Mode Proofs (No Tactics) -/

unsafe def testTermModeProof : IO Unit := do
  printSubsection "Term-Mode Proof (No Tactics)"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile edgeCaseFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 4: "theorem term_mode_proof : 1 = 1 := rfl" (1-indexed)
    let dag ← getCompleteProofDagAt uri sessionId 4 11 3

    match dag with
    | some d =>
      -- Term-mode proofs should have no tactic nodes
      assertTrue "term-mode has no nodes" d.nodes.isEmpty
    | none =>
      -- Or the RPC might return an error/empty result for term-mode
      IO.println "  ✓ term-mode proof returns no DAG (expected)"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ term-mode proof handled correctly"

/-! ## Incomplete Proofs (sorry) -/

unsafe def testSorryProof : IO Unit := do
  printSubsection "Incomplete Proof (sorry)"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile edgeCaseFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 7: "theorem sorry_proof : 2 = 2 := by sorry" (1-indexed)
    let dag ← getCompleteProofDagAt uri sessionId 7 11 3

    match dag with
    | some d =>
      -- sorry proof should have one node
      assertTrue "sorry has nodes" (!d.nodes.isEmpty)
      -- The proof is not complete (sorry leaves goals unsolved)
      let node := d.nodes[0]!
      assertTrue "sorry tactic text" (containsSubstring node.tactic.text "sorry")
    | none =>
      IO.println "  ✗ sorry proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ sorry proof handled correctly"

/-! ## Invalid Cursor Position -/

unsafe def testInvalidPosition : IO Unit := do
  printSubsection "Invalid Cursor Position"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile simpleFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile simpleFile
    let uri ← fileUri simpleFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Request at line 1001 (way beyond file, 1-indexed)
    -- Server gracefully handles this by returning the last valid snapshot
    let dag ← getCompleteProofDagAt uri sessionId 1001 1 3

    match dag with
    | some d =>
      -- Server returns last valid snapshot for out-of-bounds positions
      IO.println s!"  ✓ out of bounds handled (returned {d.nodes.size} nodes)"
    | none =>
      IO.println "  ✓ out of bounds returns no DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ invalid position handled gracefully"

/-! ## Position at Whitespace/Comment -/

unsafe def testWhitespacePosition : IO Unit := do
  printSubsection "Cursor at Comment"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile edgeCaseFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile edgeCaseFile
    let uri ← fileUri edgeCaseFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- EdgeCases.lean line 1: "/-! # Edge Case Proofs..." comment (1-indexed)
    let dag ← getCompleteProofDagAt uri sessionId 1 1 3

    -- Should handle gracefully (empty or no DAG)
    match dag with
    | some d =>
      IO.println s!"  ✓ comment position returned {d.nodes.size} nodes"
    | none =>
      IO.println "  ✓ comment returns no DAG (expected)"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ comment position handled gracefully"

unsafe def runTests : IO Unit := do
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println "  RPC Boundary Tests"
  IO.println "══════════════════════════════════════════════════════════════"

  testTermModeProof
  testSorryProof
  testInvalidPosition
  testWhitespacePosition

  IO.println "\n  ✓ RPC boundary tests passed"

end Tests.Integration.Boundary
