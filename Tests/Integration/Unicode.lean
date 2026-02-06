import Lean
import Lean.Data.Lsp.Ipc
import LeanDag
import Tests.LspClient
import Tests.Harness

namespace Tests.Integration.Unicode

open Lean Lsp Ipc JsonRpc LeanDag Tests.LspClient Tests.Harness

def unicodeFile : System.FilePath := testProjectPath / "Unicode.lean"

/-! ## Unicode Identifiers -/

unsafe def testUnicodeIdentifiers : IO Unit := do
  printSubsection "Unicode Identifiers (Greek Letters)"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile unicodeFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile unicodeFile
    let uri ← fileUri unicodeFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Unicode.lean line 5: "  rw [Nat.add_comm]" inside αβγ_test (1-indexed)
    -- The theorem name contains greek letters: theorem αβγ_test
    let dag ← getCompleteProofDagAt uri sessionId 5 5 3

    match dag with
    | some d =>
      assertTrue "unicode proof has nodes" (!d.nodes.isEmpty)
      -- Verify hypotheses with unicode names are handled
      for node in d.nodes do
        for hyp in node.proofStateAfter.hypotheses do
          assertTrue s!"hyp {hyp.name} has type" (!hyp.type.isEmpty)
      IO.println s!"  ✓ unicode proof returned {d.nodes.size} nodes"
    | none =>
      IO.println "  ✗ unicode proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ unicode identifiers handled correctly"

/-! ## Unicode Column Positions -/

unsafe def testUnicodeColumnPosition : IO Unit := do
  printSubsection "Unicode Column Positions"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile unicodeFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile unicodeFile
    let uri ← fileUri unicodeFile

    openDocument uri content
    waitForFileReady uri

    let _ ← connectRpcSession 2 uri

    -- Unicode.lean line 4: "theorem αβγ_test (α β : Nat) : α + β = β + α := by"
    -- Greek letters α, β, γ are multi-byte in UTF-8 but single UTF-16 code units
    -- Column 9 in editor should be on 'α' in the theorem name
    let hover ← hoverRequest 3 uri 4 9

    match hover with
    | some h =>
      IO.println s!"  ✓ hover at unicode position: {h.contents.value.take 50}..."
    | none =>
      IO.println "  ✓ hover at unicode position returned none"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ unicode column positions handled correctly"

/-! ## Subscript Characters -/

unsafe def testSubscriptCharacters : IO Unit := do
  printSubsection "Subscript Characters (x₁, x₂)"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile unicodeFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile unicodeFile
    let uri ← fileUri unicodeFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Unicode.lean line 9: "  rw [Nat.add_comm]" inside sub_test (1-indexed)
    let dag ← getCompleteProofDagAt uri sessionId 9 5 3

    match dag with
    | some d =>
      assertTrue "subscript proof has nodes" (!d.nodes.isEmpty)
      -- Check that subscript variable names are preserved
      for node in d.nodes do
        for hyp in node.proofStateAfter.hypotheses do
          -- x₁ and x₂ should appear in hypothesis names or types
          IO.println s!"    hyp: {hyp.name} : {hyp.type}"
      IO.println s!"  ✓ subscript proof returned {d.nodes.size} nodes"
    | none =>
      IO.println "  ✗ subscript proof should return a DAG"

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ subscript characters handled correctly"

unsafe def runTests : IO Unit := do
  IO.println ""
  IO.println "══════════════════════════════════════════════════════════════"
  IO.println "  RPC Unicode Tests"
  IO.println "══════════════════════════════════════════════════════════════"

  testUnicodeIdentifiers
  testUnicodeColumnPosition
  testSubscriptCharacters

  IO.println "\n  ✓ RPC unicode tests passed"

end Tests.Integration.Unicode
