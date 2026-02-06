import Lean
import Lean.Data.Lsp.Ipc
import LeanDag
import Tests.LspClient
import Tests.Harness

namespace Tests.Integration.ProofDag

open Lean Lsp Ipc JsonRpc LeanDag Tests.LspClient Tests.Harness

def logicFile : System.FilePath := testProjectPath / "Logic.lean"
def inductionFile : System.FilePath := testProjectPath / "Induction.lean"

def parseProofDag (json : Json) : Except String CompleteProofDag :=
  match json.getObjVal? "proofDag" with
  | .ok dagJson => FromJson.fromJson? dagJson
  | .error e => .error s!"Missing proofDag field: {e}"

/-- Get proof DAG at position. Line/col are 1-indexed (editor style). -/
def getProofDagAt (uri : String) (sessionId : UInt64) (line col : Nat) (requestId : Nat) : IpcM CompleteProofDag := do
  let result ← callRpc requestId sessionId uri line col "LeanDag.getCompleteProofDag" (Json.mkObj [("mode", "tree")])
  match parseProofDag result with
  | .ok dag => return dag
  | .error e => throw <| IO.userError s!"Failed to parse CompleteProofDag: {e}"

unsafe def testLinearProofStructure : IO Unit := do
  printSubsection "Linear Proof - contrapositive"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    -- Verify basic structure
    assertTrue "has nodes" (!dag.nodes.isEmpty)
    assertSome "has root" dag.rootNodeId
    assertSome "has currentNodeId" dag.currentNodeId

    -- Verify initial state has the theorem goal
    assertTrue "initialProofState has goal" (!dag.initialProofState.goals.isEmpty)
    let initialGoal := dag.initialProofState.goals[0]!
    assertTrue "initial goal has type" (!initialGoal.type.isEmpty)
    assertTrue "initial goal has id" (!initialGoal.id.isEmpty)

    -- Verify nodes have required fields for TUI
    for node in dag.nodes do
      assertTrue s!"node {node.id} has tactic text" (!node.tactic.text.isEmpty)
      assertTrue s!"node {node.id} has position" (node.position.line ≥ 0)

      -- proofStateBefore and proofStateAfter must exist
      -- Goals in states must have required fields
      for goal in node.proofStateBefore.goals do
        assertTrue s!"node {node.id} proofStateBefore goal has type" (!goal.type.isEmpty)
        assertTrue s!"node {node.id} proofStateBefore goal has id" (!goal.id.isEmpty)

      for goal in node.proofStateAfter.goals do
        assertTrue s!"node {node.id} proofStateAfter goal has type" (!goal.type.isEmpty)
        assertTrue s!"node {node.id} proofStateAfter goal has id" (!goal.id.isEmpty)

      -- Hypotheses must have required fields
      for hyp in node.proofStateBefore.hypotheses do
        assertTrue s!"node {node.id} hyp has name" (!hyp.name.isEmpty)
        assertTrue s!"node {node.id} hyp has type" (!hyp.type.isEmpty)
        assertTrue s!"node {node.id} hyp has id" (!hyp.id.isEmpty)

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ linear proof structure validated"

unsafe def testBranchingProofStructure : IO Unit := do
  printSubsection "Branching Proof - or_assoc_logic"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 23: "    cases h with" inside or_assoc_logic (1-indexed)
    let dag ← getProofDagAt uri sessionId 23 7 3

    assertTrue "has nodes" (!dag.nodes.isEmpty)
    assertSome "has root" dag.rootNodeId

    -- Verify all nodes have valid structure
    for node in dag.nodes do
      -- Parent references should be valid (if present)
      if let some parentId := node.parent then
        assertTrue s!"node {node.id} parent {parentId} exists" (dag.nodes.any (·.id == parentId))

      -- Children references should be valid
      for childId in node.children do
        assertTrue s!"node {node.id} child {childId} exists" (dag.nodes.any (·.id == childId))

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ branching proof structure validated"

unsafe def testInductionProofStructure : IO Unit := do
  printSubsection "Induction Proof - nat_add_zero"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile inductionFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile inductionFile
    let uri ← fileUri inductionFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Induction.lean line 5: "  | zero => rfl" (1-indexed)
    let dag ← getProofDagAt uri sessionId 5 5 3

    assertTrue "has nodes" (!dag.nodes.isEmpty)

    -- Verify goal types are non-empty strings (not hygienic names)
    for node in dag.nodes do
      for goal in node.proofStateAfter.goals do
        -- username should be None or a visible name (filtered)
        if let some name := goal.username then
          assertTrue s!"goal username is visible" (!name.isEmpty && !containsSubstring name "._hyg.")

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ induction proof structure validated"

unsafe def testNavigationLocationsField : IO Unit := do
  printSubsection "NavigationLocations Field Present"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    -- Verify navigationLocations field exists in goals (even if empty)
    for goal in dag.initialProofState.goals do
      -- The field should exist (default value is empty)
      -- We just verify the structure is valid by accessing it
      let _ := goal.navigationLocations
      IO.println s!"  ✓ initialProofState goal has navigationLocations field"

    for node in dag.nodes do
      for goal in node.proofStateAfter.goals do
        let _ := goal.navigationLocations
      for hyp in node.proofStateAfter.hypotheses do
        let _ := hyp.navigationLocations

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ navigationLocations fields present"

unsafe def testUsernameFiltering : IO Unit := do
  printSubsection "Username Filtering"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath

  let simpleFile := testProjectPath / "Simple.lean"
  requireFile simpleFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile simpleFile
    let uri ← fileUri simpleFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Simple.lean line 1: "theorem simple_rfl : 1 = 1 := by rfl" (1-indexed)
    let dag ← getProofDagAt uri sessionId 1 11 3

    -- Verify anonymous usernames are filtered to None
    for goal in dag.initialProofState.goals do
      if let some name := goal.username then
        assertTrue "username not [anonymous]" (name != "[anonymous]")
        assertTrue "username not hygienic" (!containsSubstring name "._hyg." && !containsSubstring name "._@.")

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ username filtering correct"

unsafe def testNewHypothesesIndices : IO Unit := do
  printSubsection "New Hypotheses Indices"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    for node in dag.nodes do
      -- newHypothesisIndices indices must be valid
      for idx in node.newHypothesisIndices do
        assertTrue s!"node {node.id} newHyp idx {idx} valid"
          (idx < node.proofStateAfter.hypotheses.size)

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ newHypothesisIndices indices valid"

unsafe def testTacticInfoFields : IO Unit := do
  printSubsection "Tactic Info Fields"

  let analyzerPath ← LeanDagPath
  requireBinary analyzerPath
  requireFile logicFile

  runWithLeanDag do
    let _ ← initializeServer 0

    let content ← IO.FS.readFile logicFile
    let uri ← fileUri logicFile

    openDocument uri content
    waitForFileReady uri

    let sessionId ← connectRpcSession 2 uri

    -- Logic.lean line 4: "  intro hnq hp" (1-indexed)
    let dag ← getProofDagAt uri sessionId 4 5 3

    for node in dag.nodes do
      -- tactic.text must be non-empty
      assertTrue s!"node {node.id} tactic text non-empty" (!node.tactic.text.isEmpty)

      -- hypothesisDependencies should be a list (can be empty)
      let _ := node.tactic.hypothesisDependencies

      -- referencedTheorems should be a list (can be empty)
      let _ := node.tactic.referencedTheorems

    shutdown 4
    let _ ← waitForExit
    IO.println "  ✓ tactic info fields valid"

unsafe def runTests : IO Unit := do
  printSection "RPC ProofDag Validation Tests"

  testLinearProofStructure
  testBranchingProofStructure
  testInductionProofStructure
  testNavigationLocationsField
  testUsernameFiltering
  testNewHypothesesIndices
  testTacticInfoFields

  IO.println "\n  ✓ RPC ProofDag tests passed"

end Tests.Integration.ProofDag
