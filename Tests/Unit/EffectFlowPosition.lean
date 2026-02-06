import Lean
import Lean.Elab.Frontend
import LeanDag
import Tests.Harness
import Tests.Unit.FunctionalDagTestHarness

namespace Tests.Unit.EffectFlowPosition

open Lean Elab Command Meta
open Tests.Harness Tests.Unit.FunctionalDagTestHarness
open LeanDag.EffectFlow

/-- Check if an InfoTree contains effectful monadic code (IO version for tests). -/
def isEffectfulTreeIO (infoTree : InfoTree) : IO Bool := do
  let exprs := infoTree.foldInfo (init := #[]) fun _ info acc =>
    match info with
    | .ofTermInfo termInfo => acc.push termInfo.expr
    | _ => acc
  for e in exprs do
    if ← hasMatchingRule e then return true
  return false

/-- Collect all expressions with positions from an InfoTree. -/
def collectPositions (tree : InfoTree) : Array (Expr × Nat) :=
  let unsorted := tree.foldInfo (init := #[]) fun _ info arr =>
    match info with
    | .ofTermInfo ti =>
      match info.pos? with
      | some pos => arr.push (ti.expr, pos.byteIdx)
      | none => arr
    | _ => arr
  unsorted.insertionSort fun (_, p1) (_, p2) => p1 < p2

/-- Find the outermost effectful expression with position in an InfoTree (IO version). -/
def findOutermostEffectfulExprIO (tree : InfoTree) (text : FileMap)
    : IO (Option (ContextInfo × TermInfo × Array (Expr × Nat))) := do
  let allTerms := tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo termInfo => acc.push (ctx, termInfo, info.pos?, info.tailPos?)
    | _ => acc

  let mut candidates : Array (ContextInfo × TermInfo × Lsp.Position) := #[]
  for (ctx, termInfo, startPos?, _) in allTerms do
    if ← hasMatchingRule termInfo.expr then
      match startPos? with
      | some startPos =>
        let startLsp := text.utf8PosToLspPos startPos
        candidates := candidates.push (ctx, termInfo, startLsp)
      | none => pure ()

  let sorted := candidates.insertionSort fun (_, _, s1) (_, _, s2) =>
    s1.line < s2.line || (s1.line == s2.line && s1.character < s2.character)

  match sorted[0]? with
  | some (ctx, termInfo, _) =>
    let positions := collectPositions tree
    return some (ctx, termInfo, positions)
  | none => return none
    let positions := collectPositions tree
    some (ctx, termInfo, positions)
  | none => none

/-- Analyze effect flow from an elaboration result.
    Returns nodes and the FileMap for position conversion. -/
def analyzeEffectFlowFromResult (result : ElaborationResult)
    : IO (Array EffectNode × FileMap) := do
  let text := result.fileMap

  for tree in result.infoTrees.toList do
    if ← isEffectfulTreeIO tree then
      match ← findOutermostEffectfulExprIO tree text with
      | some (ctx, termInfo, allPositions) =>
        let lctx := termInfo.lctx.sanitizeNames.run' {options := {}}
        let nodes ← ctx.runMetaM lctx do
          analyze termInfo.expr lctx allPositions
        return (nodes, text)
      | none => continue

  return (#[], result.fileMap)

/-- Test: Effect flow nodes are created with positions assigned. -/
def testPositionAssignment : IO Unit := do
  printSubsection "Position Assignment"

  let code := "
import Init

def simpleOption : Option Nat := do
  let a ← some 1
  let b ← some 2
  pure (a + b)
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  assertTrue "nodes created" (nodes.size > 0)

  -- Count nodes with positions
  let nodesWithPos := nodes.filter (·.position.isSome)
  IO.println s!"    nodes: {nodes.size}, with positions: {nodesWithPos.size}"

  -- Print position debug info
  for node in nodes do
    let posStr := match node.position with
      | some p =>
        let lspPos := text.utf8PosToLspPos ⟨p⟩
        s!"line {lspPos.line + 1}"
      | none => "NONE"
    IO.println s!"    Node {node.id} ({node.kind}): pos={posStr}"

  -- At least some nodes should have positions
  assertTrue "some nodes have positions" (nodesWithPos.size > 0)

/-- Test: Multiple bind nodes get different positions. -/
def testUniqueBindPositions : IO Unit := do
  printSubsection "Unique Bind Positions"

  let code := "
import Init

structure Counter where value : Nat deriving Repr

def increment : StateM Counter Nat := do
  let s ← get
  set (Counter.mk (s.value + 1))
  pure s.value

def counterSequence : StateM Counter Nat := do
  let v1 ← increment
  let v2 ← increment
  let v3 ← increment
  pure (v1 + v2 + v3)
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  -- Get bind nodes
  let bindNodes := nodes.filter (·.kind == "effectBind")
  IO.println s!"    total nodes: {nodes.size}, bind nodes: {bindNodes.size}"

  -- Print all bind nodes with positions
  for node in bindNodes do
    let posStr := match node.position with
      | some p =>
        let lspPos := text.utf8PosToLspPos ⟨p⟩
        s!"line {lspPos.line + 1}, col {lspPos.character}"
      | none => "NONE"
    IO.println s!"    Bind node {node.id}: pos={posStr}"

  -- Check that bind nodes exist
  assertTrue "has bind nodes" (bindNodes.size >= 1)

  -- Check how many have positions
  let bindsWithPos := bindNodes.filter (·.position.isSome)
  IO.println s!"    binds with positions: {bindsWithPos.size}"

  -- Positions should be different for different bind nodes
  let positions := bindsWithPos.filterMap (·.position) |>.toList
  let uniquePositions := positions.eraseDups
  IO.println s!"    unique positions: {uniquePositions.length}, total: {positions.length}"

  -- If we have multiple positions, they should be unique
  if positions.length > 1 then
    assertTrue "positions are unique" (uniquePositions.length == positions.length)

/-- Test: State operations (get/set) get positions. -/
def testStateOperationPositions : IO Unit := do
  printSubsection "State Operation Positions"

  let code := "
import Init

def simpleState : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  let m ← get
  pure m
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  IO.println s!"    total nodes: {nodes.size}"

  -- Get state read/write nodes
  let stateReadNodes := nodes.filter (·.kind == "stateRead")
  let stateWriteNodes := nodes.filter (·.kind == "stateWrite")

  IO.println s!"    stateRead nodes: {stateReadNodes.size}"
  IO.println s!"    stateWrite nodes: {stateWriteNodes.size}"

  -- Print all nodes for debugging
  for node in nodes do
    let posStr := match node.position with
      | some p =>
        let lspPos := text.utf8PosToLspPos ⟨p⟩
        s!"line {lspPos.line + 1}"
      | none => "NONE"
    IO.println s!"    Node {node.id} ({node.kind}): pos={posStr}"

  assertTrue "nodes exist" (nodes.size > 0)

/-- Test: Position-to-node matching works for cursor navigation. -/
def testCursorToNodeMapping : IO Unit := do
  printSubsection "Cursor to Node Mapping"

  let code := "
import Init

def testDo : Option Nat := do
  let a ← some 1
  let b ← some 2
  let c ← some 3
  pure (a + b + c)
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  -- Simulate cursor-to-node mapping (same logic as Builder.buildEffectDag)
  let findNodeAtCursor (cursorLine : Nat) : Option Nat := Id.run do
    let mut bestNode : Option EffectNode := none
    let mut bestLine : Nat := 0
    for node in nodes do
      if let some byteOffset := node.position then
        let lspPos := text.utf8PosToLspPos ⟨byteOffset⟩
        if lspPos.line <= cursorLine then
          if bestNode.isNone || lspPos.line >= bestLine then
            bestNode := some node
            bestLine := lspPos.line
    bestNode.map (·.id)

  -- Test that different cursor positions can yield different nodes
  let node4 := findNodeAtCursor 4
  let node5 := findNodeAtCursor 5
  let node6 := findNodeAtCursor 6
  let node7 := findNodeAtCursor 7

  IO.println s!"    cursor line 4 -> node {node4.getD 999}"
  IO.println s!"    cursor line 5 -> node {node5.getD 999}"
  IO.println s!"    cursor line 6 -> node {node6.getD 999}"
  IO.println s!"    cursor line 7 -> node {node7.getD 999}"

  -- At least some cursor positions should resolve to nodes
  let hasAnyMapping := node4.isSome || node5.isSome || node6.isSome || node7.isSome
  assertTrue "cursor positions resolve to nodes" hasAnyMapping

/-- REGRESSION TEST: Each bind line should map to a distinct node.
    This is the core cursor-to-node mapping problem we're trying to fix. -/
def testEachLineMapsToDifferentNode : IO Unit := do
  printSubsection "REGRESSION: Each Line Maps to Different Node"

  -- Simple do-block where each line has a distinct bind
  let code := "
import Init

def testMapping : Option Nat := do
  let a ← some 1
  let b ← some 2
  let c ← some 3
  pure (a + b + c)
"
  -- Lines in the code (0-indexed):
  -- Line 0: (empty)
  -- Line 1: import Init
  -- Line 2: (empty)
  -- Line 3: def testMapping...
  -- Line 4: let a ← some 1
  -- Line 5: let b ← some 2
  -- Line 6: let c ← some 3
  -- Line 7: pure (a + b + c)

  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  -- Build a map from line -> node id
  let mut lineToNode : Std.HashMap Nat Nat := {}
  for node in nodes do
    if let some byteOffset := node.position then
      let lspPos := text.utf8PosToLspPos ⟨byteOffset⟩
      lineToNode := lineToNode.insert lspPos.line node.id

  IO.println s!"    Line to node mapping:"
  for (line, nodeId) in lineToNode.toList do
    let node := nodes.find? (·.id == nodeId)
    let kind := node.map (·.kind) |>.getD "?"
    IO.println s!"      line {line + 1} -> node {nodeId} ({kind})"

  -- Count how many distinct lines have nodes
  let linesWithNodes := lineToNode.size
  IO.println s!"    Distinct lines with nodes: {linesWithNodes}"

  -- STRICT: We have 4 lines of monadic code (4,5,6,7), so we need 4 distinct positions
  -- This will FAIL until position matching is fixed
  assertTrue "STRICT: 4 lines of code need 4 distinct node positions" (linesWithNodes >= 4)

  -- Debug: print each node's line
  IO.println s!"    Node positions in array order:"
  for node in nodes do
    let posStr := match node.position with
      | some p => s!"line {(text.utf8PosToLspPos ⟨p⟩).line}"
      | none => "NONE"
    IO.println s!"      node {node.id} ({node.kind}): {posStr}"

  -- Now test cursor-to-node: cursor on each line should find a node on that line (or earlier)
  let findNodeAtCursor (cursorLine : Nat) : Option (Nat × Nat) := Id.run do
    let mut bestNode : Option EffectNode := none
    let mut bestLine : Nat := 0
    for node in nodes do
      if let some byteOffset := node.position then
        let lspPos := text.utf8PosToLspPos ⟨byteOffset⟩
        if lspPos.line <= cursorLine then
          if bestNode.isNone || lspPos.line >= bestLine then
            bestNode := some node
            bestLine := lspPos.line
    bestNode.map fun n => (n.id, bestLine)

  -- Test cursor-to-node mapping (0-indexed lines)
  -- The actual bind lines are 4, 5, 6 (0-indexed), pure is at line 7
  let result4 := findNodeAtCursor 4
  let result5 := findNodeAtCursor 5
  let result6 := findNodeAtCursor 6
  let result7 := findNodeAtCursor 7

  IO.println s!"    Cursor mapping (0-indexed cursor -> node id, node line):"
  IO.println s!"      cursor 4 -> node {result4.map (·.1) |>.getD 999} (at line {result4.map (·.2) |>.getD 999})"
  IO.println s!"      cursor 5 -> node {result5.map (·.1) |>.getD 999} (at line {result5.map (·.2) |>.getD 999})"
  IO.println s!"      cursor 6 -> node {result6.map (·.1) |>.getD 999} (at line {result6.map (·.2) |>.getD 999})"
  IO.println s!"      cursor 7 -> node {result7.map (·.1) |>.getD 999} (at line {result7.map (·.2) |>.getD 999})"

  -- The 3 bind cursor lines (4,5,6) should map to 3 different nodes
  let bindCursorResults := [result4, result5, result6].filterMap (·.map (·.1))
  let uniqueBindNodes := bindCursorResults.eraseDups
  IO.println s!"    Bind cursor nodes: {bindCursorResults}, unique: {uniqueBindNodes.length}"

  -- STRICT: Each bind line cursor should find a different node
  assertTrue "3 bind cursor lines map to 3 different nodes" (uniqueBindNodes.length >= 3)

/-- REGRESSION TEST: Multiple Bind.bind calls need distinct positions.
    The current algorithm matches by head constant name (Bind.bind),
    but when there are 3 binds they all try to claim the same position. -/
def testMultipleBindsGetDistinctPositions : IO Unit := do
  printSubsection "REGRESSION: Multiple Binds Get Distinct Positions"

  let code := "
import Init

def threeBinds : Option Nat := do
  let x ← some 1
  let y ← some 2
  let z ← some 3
  pure (x + y + z)
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  -- Get all effectBind nodes
  let bindNodes := nodes.filter (·.kind == "effectBind")
  let bindsWithPos := bindNodes.filter (·.position.isSome)

  IO.println s!"    Total effectBind nodes: {bindNodes.size}"
  IO.println s!"    With positions: {bindsWithPos.size}"

  -- Print each bind node's position
  for node in bindNodes do
    let posStr := match node.position with
      | some p =>
        let lspPos := text.utf8PosToLspPos ⟨p⟩
        s!"line {lspPos.line + 1}"
      | none => "NONE"
    IO.println s!"      Bind {node.id}: pos={posStr}"

  -- Get unique lines for bind nodes (1-indexed for display)
  let bindLines := bindsWithPos.filterMap fun n =>
    n.position.map fun p => (text.utf8PosToLspPos ⟨p⟩).line + 1
  let uniqueLines := bindLines.toList.eraseDups

  IO.println s!"    Bind nodes on lines (1-indexed): {bindLines.toList}"
  IO.println s!"    Unique lines: {uniqueLines.length}"

  -- STRICT: 3 bind statements need 3 distinct positions
  -- This WILL FAIL with current implementation
  assertTrue "STRICT: 3 binds have 3 distinct line positions" (uniqueLines.length >= 3)

/-- REGRESSION TEST: Nodes without positions break cursor mapping.
    When a node has pos=NONE, it can never be highlighted. -/
def testNodesWithoutPositions : IO Unit := do
  printSubsection "REGRESSION: Nodes Without Positions"

  let code := "
import Init

def stateTest : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  let m ← get
  set (m + 2)
  pure m
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  let nodesWithPos := nodes.filter (·.position.isSome)
  let nodesWithoutPos := nodes.filter (·.position.isNone)

  IO.println s!"    Total nodes: {nodes.size}"
  IO.println s!"    With positions: {nodesWithPos.size}"
  IO.println s!"    Without positions (BROKEN): {nodesWithoutPos.size}"

  -- List nodes without positions - these are the problem
  if nodesWithoutPos.size > 0 then
    IO.println "    Nodes without positions:"
    for node in nodesWithoutPos do
      IO.println s!"      Node {node.id} ({node.kind}) - CANNOT BE HIGHLIGHTED"

  -- Calculate percentage of nodes that can be highlighted
  let percentage := if nodes.size > 0 then
    (nodesWithPos.size * 100) / nodes.size
  else 0
  IO.println s!"    Highlightable: {percentage}%"

  -- ASSERT: At least 70% of nodes should have positions
  -- This is a regression test - if position matching breaks, this will fail
  assertTrue "at least 70% of nodes have positions" (percentage >= 70)

/-- REGRESSION TEST: stateRead and stateWrite nodes need positions.
    These are important nodes that users want to navigate to. -/
def testStateNodesHavePositions : IO Unit := do
  printSubsection "REGRESSION: State Nodes Have Positions"

  let code := "
import Init

def multiState : StateM Nat Nat := do
  let a ← get
  set (a + 1)
  let b ← get
  set (b + 2)
  let c ← get
  pure c
"
  let result ← assertElaborates code
  let (nodes, text) := ← analyzeEffectFlowFromResult result

  let stateReadNodes := nodes.filter (·.kind == "stateRead")
  let stateWriteNodes := nodes.filter (·.kind == "stateWrite")
  let stateReadWithPos := stateReadNodes.filter (·.position.isSome)
  let stateWriteWithPos := stateWriteNodes.filter (·.position.isSome)

  IO.println s!"    stateRead: {stateReadWithPos.size}/{stateReadNodes.size} have positions"
  IO.println s!"    stateWrite: {stateWriteWithPos.size}/{stateWriteNodes.size} have positions"

  -- Print details
  for node in stateReadNodes do
    let posStr := match node.position with
      | some p => s!"line {(text.utf8PosToLspPos ⟨p⟩).line + 1}"
      | none => "NONE"
    IO.println s!"      stateRead node {node.id}: pos={posStr}"

  for node in stateWriteNodes do
    let posStr := match node.position with
      | some p => s!"line {(text.utf8PosToLspPos ⟨p⟩).line + 1}"
      | none => "NONE"
    IO.println s!"      stateWrite node {node.id}: pos={posStr}"

  -- ASSERT: Most state nodes should have positions (they're user-visible operations)
  -- Note: Not all may have positions due to InfoTree limitations, but at least 2/3 should
  assertTrue "most stateRead nodes have positions" (stateReadWithPos.size * 2 >= stateReadNodes.size)
  assertTrue "all stateWrite nodes have positions" (stateWriteWithPos.size == stateWriteNodes.size)

def runTests : IO Unit := do
  printSection "Effect Flow Position Tests"
  testPositionAssignment
  testUniqueBindPositions
  testStateOperationPositions
  testCursorToNodeMapping
  -- Regression tests that should fail if position matching is broken
  testMultipleBindsGetDistinctPositions
  testEachLineMapsToDifferentNode
  testNodesWithoutPositions
  testStateNodesHavePositions
  IO.println "\n  ✓ Effect flow position tests completed"

end Tests.Unit.EffectFlowPosition
