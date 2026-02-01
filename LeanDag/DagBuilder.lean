module

public import Lean
public import LeanDag.Types
public import LeanDag.InfoTreeParser
public import LeanDag.Conversion
public import LeanDag.DiffComputation

@[expose] public section

open Lean Elab

namespace LeanDag

open LeanDag.InfoTreeParser

/-! ## Definition Name Extraction -/

/-- Extract the definition name from the InfoTree by finding the enclosing command.
    Uses the same pattern as Lean's DocumentSymbol handler. -/
def getDefinitionName (tree : InfoTree) : Option String :=
  let names := tree.collectNodesBottomUp fun _ctx i _cs acc =>
    match i with
    | .ofCommandInfo ci =>
      -- For declarations: stx[1][1] contains the declId
      -- Pattern: `(declId|$id$[.{$ls,*}]?)` extracts the identifier
      let declId := ci.stx.getArg 1 |>.getArg 1
      let id := declId.getArg 0 |>.getId  -- First child of declId is the identifier
      if id.isAnonymous then acc else id.toString :: acc
    | _ => acc
  names.head?

/-! ## DAG Building -/

def buildProofDag (steps : List ParsedStep) (cursorPos : Lsp.Position)
    (definitionName : Option String := none) : ProofDag :=
  if steps.isEmpty then {} else
  let stepsArray := steps.toArray
  -- Build goal ID to step index map: which step produces which goals
  -- goalsAfter are the goals that result from applying the tactic
  let goalToProducer : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for h : idx in [:stepsArray.size] do
      let step := stepsArray[idx]
      for goal in step.goalsAfter do
        m := m.insert goal.id.name.toString idx
    return m
  -- For each step, find parent (the step whose goalsAfter contains this step's goalBefore)
  let parentOf : Array (Option Nat) := stepsArray.map fun step =>
    goalToProducer.get? step.goalBefore.id.name.toString
  -- Compute children from parent relationships
  let childrenOf : Array (List Nat) := Id.run do
    let mut result : Array (List Nat) := stepsArray.map (fun _ => [])
    for h : childIdx in [:parentOf.size] do
      if let some parentIdx := parentOf[childIdx] then
        if parentIdx < result.size then
          result := result.modify parentIdx (childIdx :: ·)
    return result
  -- Compute depth: count steps to root
  let depths : Array Nat := Id.run do
    let mut result := stepsArray.map (fun _ => 0)
    for h : idx in [:stepsArray.size] do
      let mut depth := 0
      let mut current := idx
      let mut visited : Std.HashSet Nat := {}
      while true do
        if visited.contains current then break
        visited := visited.insert current
        match parentOf[current]? with
        | some (some p) =>
          depth := depth + 1
          current := p
        | _ => break
      result := result.set! idx depth
    return result
  -- Build nodes with computed relationships
  let nodes := stepsArray.mapIdx fun idx step =>
    let goalBefore := convertGoalInfo step.goalBefore
    let goalsAfter := step.goalsAfter.map convertGoalInfo
    let hypsBefore := step.goalBefore.hyps.map convertHypothesis |>.filter (·.name != "")
    -- Get hypotheses from first goal after tactic (if any), otherwise use before
    let hypsAfter := match step.goalsAfter.head? with
      | some g => g.hyps.map convertHypothesis |>.filter (·.name != "")
      | none => hypsBefore
    -- Compute new hypotheses: indices in hypsAfter for hyps not in hypsBefore
    let hypIdsBefore : Std.HashSet String := Std.HashSet.ofList (hypsBefore.map (·.id))
    let newHypotheses := Id.run do
      let mut result : List Nat := []
      for h : i in [:hypsAfter.length] do
        let hyp := hypsAfter[i]!
        if !hypIdsBefore.contains hyp.id then
          result := result ++ [i]
      return result
    -- Build raw states (without diff)
    let rawStateBefore : ProofState := { goals := [goalBefore], hypotheses := hypsBefore }
    let rawStateAfter : ProofState := { goals := goalsAfter, hypotheses := hypsAfter }
    -- Apply diff highlighting: stateBefore shows what will change, stateAfter shows what changed
    let stateBefore := diffStateBefore rawStateBefore rawStateAfter
    let stateAfter := diffStateAfter rawStateBefore rawStateAfter
    { id := idx
      tactic := { text := step.tacticString, dependsOn := step.tacticDependsOn, theoremsUsed := step.theorems.map (·.name) }
      position := step.position.start
      stateBefore
      stateAfter
      newHypotheses
      children := childrenOf[idx]?.getD []
      parent := parentOf[idx]?.join
      depth := depths[idx]?.getD 0 }
  -- Find all nodes with no parent (potential roots/orphans)
  let rootCandidates := nodes.toList.filterMap fun n =>
    if n.parent.isNone then some n.id else none
  -- First rootless node is the main root, rest are orphans (disconnected components)
  let (root, orphans) := match rootCandidates with
    | [] => (none, [])
    | r :: rest => (some r, rest)
  -- Find current node: the node whose position is closest to (but not after) cursor
  let currentNode : Option Nat := Id.run do
    let mut best : Option Nat := none
    let mut bestPos : Lsp.Position := ⟨0, 0⟩
    for h : i in [:nodes.size] do
      let node : ProofDagNode := nodes[i]
      let pos : Lsp.Position := node.position
      -- Node is at or before cursor position
      if pos.line < cursorPos.line || (pos.line == cursorPos.line && pos.character <= cursorPos.character) then
        -- And it's better than current best (closer to cursor)
        if best.isNone || pos.line > bestPos.line || (pos.line == bestPos.line && pos.character > bestPos.character) then
          best := some node.id
          bestPos := pos
    return best
  { nodes, root, orphans, currentNode, initialState := nodes[0]!.stateBefore, definitionName }

end LeanDag
