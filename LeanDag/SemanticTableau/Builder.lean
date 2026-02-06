import Lean
import LeanDag.Protocol
import LeanDag.SemanticTableau.InfoTreeParser
import LeanDag.SemanticTableau.DiffComputation

open Lean Elab

namespace LeanDag.SemanticTableau

open LeanDag.SemanticTableau.InfoTreeParser
open LeanDag.SemanticTableau (TacticProofState.diffBefore TacticProofState.diffAfter)
open LeanDag.ProofKind
open LeanDag (getDefinitionName)

/-! ## DAG Building -/

/-- Build a unified GenericDag from parsed proof steps. -/
def GenericDag.buildProof (steps : List ParsedStep) (cursorPos : Lsp.Position)
    (definitionName : Option String := none) : GenericDag :=
  if steps.isEmpty then { displayStyle := .proof, nodes := #[], metadata := Json.mkObj [] } else
  let stepsArray := steps.toArray
  -- Build goal ID to step index map: which step produces which goals
  let goalToProducer : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for h : idx in [:stepsArray.size] do
      let step := stepsArray[idx]
      for goal in step.goalsAfter do
        m := m.insert goal.mvarId.name.toString idx
    return m
  -- For each step, find parent (the step whose goalsAfter contains this step's goalBefore)
  let parentOf : Array (Option Nat) := stepsArray.map fun step =>
    goalToProducer.get? step.goalBefore.mvarId.name.toString
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
    let goalBefore := step.goalBefore.obligation
    let goalsAfter := (step.goalsAfter.map (·.obligation)).toArray
    let hypsBefore := (step.goalBefore.hypotheses.filter (·.name != "")).toArray
    -- Get hypotheses from first goal after tactic (if any), otherwise use before
    let hypsAfter := match step.goalsAfter.head? with
      | some g => (g.hypotheses.filter (·.name != "")).toArray
      | none => hypsBefore
    -- Compute new hypotheses: indices in hypsAfter for hyps not in hypsBefore
    let hypIdsBefore : Std.HashSet String := Std.HashSet.ofArray (hypsBefore.map (·.id))
    let newHypothesisIndices := Id.run do
      let mut result : Array Nat := #[]
      for h : i in [:hypsAfter.size] do
        let hyp := hypsAfter[i]!
        if !hypIdsBefore.contains hyp.id then
          result := result.push i
      return result
    -- Build raw states (without diff)
    let rawStateBefore : TacticProofState := { goals := #[goalBefore], hypotheses := hypsBefore }
    let rawStateAfter : TacticProofState := { goals := goalsAfter, hypotheses := hypsAfter }
    -- Apply diff highlighting
    let proofStateBefore := TacticProofState.diffBefore rawStateBefore rawStateAfter
    let proofStateAfter := TacticProofState.diffAfter rawStateBefore rawStateAfter
    -- Build edges from children
    let childIds := (childrenOf[idx]?.getD []).toArray
    let edges := childIds.map fun childId =>
      { target := childId, label := none, kind := none, attributes := Json.mkObj [] : GraphEdge }
    -- Build metadata with proof state info
    let metadata := Json.mkObj [
      ("proof_state_before", toJson proofStateBefore),
      ("proof_state_after", toJson proofStateAfter),
      ("new_hypothesis_indices", Json.arr (newHypothesisIndices.map fun i => toJson i)),
      ("hypothesis_dependencies", Json.arr (step.hypothesisDependencies.toArray.map fun s => Json.str s)),
      ("referenced_theorems", Json.arr ((step.theorems.map (·.name)).toArray.map fun s => Json.str s))
    ]
    { id := idx
      content := .plain step.tacticString
      kind := tactic
      position := step.position.start
      edges := edges
      parent := parentOf[idx]?.join
      depth := depths[idx]?.getD 0
      metadata := metadata : GraphNode }
  -- Find all nodes with no parent (potential roots/orphans)
  let rootCandidates := nodes.toList.filterMap fun n =>
    if n.parent.isNone then some n.id else none
  -- First rootless node is the main root, rest are orphans
  let (root, orphans) := match rootCandidates with
    | [] => (none, #[])
    | r :: rest => (some r, rest.toArray)
  -- Find current node: closest to cursor
  let currentNodeId : Option Nat := Id.run do
    let mut best : Option Nat := none
    let mut bestPos : Lsp.Position := ⟨0, 0⟩
    for h : i in [:nodes.size] do
      let node := nodes[i]
      let pos := node.position
      if pos.line < cursorPos.line || (pos.line == cursorPos.line && pos.character <= cursorPos.character) then
        if best.isNone || pos.line > bestPos.line || (pos.line == bestPos.line && pos.character > bestPos.character) then
          best := some node.id
          bestPos := pos
    return best
  -- Get initial context from first node's proof state
  let initialContext : Array LocalBinding := #[]  -- Proof mode uses metadata instead
  { displayStyle := .proof
    nodes := nodes
    rootNodeId := root
    orphans := orphans
    currentNodeId := currentNodeId
    initialContext := initialContext
    definitionName := definitionName
    definitionType := none
    metadata := Json.mkObj [] }

end LeanDag.SemanticTableau
