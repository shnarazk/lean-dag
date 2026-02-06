import Lean
import Lean.Meta.Basic
import LeanDag.Protocol
import LeanDag.Graph
import LeanDag.SearchExpression
import LeanDag.Logging
import LeanDag.DataFlow.Types
import LeanDag.DataFlow.RuleRegistry

/-!
# Functional DAG Computation

Main entry point for computing functional DAGs from term-mode Lean code.
Uses the rule-based decomposition system from `LeanDag.DataFlow.RuleRegistry`.
-/

open Lean Elab Server Meta
open LeanDag (getDefinitionName)
open LeanDag.SearchExpression (CollectedTerm DagContext collectTerms collectTermsAndBinders findOutermostTerm findCurrentNodeId buildBinderCache ppExprStr)
open LeanDag.DataFlow

namespace LeanDag.DataFlow

/-! # Type Pretty-Printing -/

/-- Pretty-print a type, extracting the return type for function types. -/
def ppGoalType (ctx : ContextInfo) (ty : Expr) : MetaM String :=
  forallBoundedTelescope ty (some 1) fun _ body => do
    ppExprStr (ctx.toPPContext (← getLCtx)) body

/-! # Expression Traversal -/

private def maxTraverseDepth : Nat := 20

/-- Recursively traverse an expression using rule-based decomposition.
    Returns a list of (ProtoNode, depth) pairs for all decomposed nodes. -/
partial def traverseExpr (lctx : LocalContext) (e : Expr) (depth : Nat)
    : MetaM (List (ProtoNode × Nat)) := do
  if depth >= maxTraverseDepth then return []

  match ← findRule e with
  | some rule =>
    match ← rule.decompose e lctx with
    | some result =>
      -- Collect nodes from this decomposition
      let nodesWithDepth := result.nodes.toList.map (·, depth)

      -- Recursively traverse children
      let childResults ← match result.children with
        | some children =>
          children.toList.foldlM (init := []) fun acc child => do
            let childNodes ← traverseExpr lctx child (depth + 1)
            return acc ++ childNodes
        | none => pure []

      return nodesWithDepth ++ childResults
    | none => return []
  | none => return []

/-! # Term Info Collection -/

/-- Collect term steps by traversing expressions using rule-based decomposition. Pure version. -/
def collectTermInfosPure (pctx : TermParserContext) (terms : Array CollectedTerm)
    : IO (List ParsedTermStep) := do
  let rules ← getRules

  log! s!"  [collectTermInfosPure] rules.size={rules.size}, terms.size={terms.size}"

  -- Debug: find terms that match rules
  let matchingTerms := terms.filter fun t => anyRuleApplies rules t.termInfo.expr
  log! s!"  [collectTermInfosPure] matchingTerms.size={matchingTerms.size}"
  for term in matchingTerms.take 3 do
    let exprKind := term.termInfo.expr.ctorName
    log! s!"  [collectTermInfosPure] MATCHING term kind={exprKind}"

  -- Find outermost matching expression using shared utility
  let some term := findOutermostTerm terms pctx.text pctx.position (anyRuleApplies rules ·)
    | do
      log! s!"  [collectTermInfosPure] No outermost term found matching rules"
      return []

  let lctx := term.termInfo.lctx.sanitizeNames.run' {options := {}}
  let ppCtx := term.ctx.toPPContext lctx
  let bindings ← formatBindings ppCtx lctx pctx.toNavigationContext
  let baseLspPos : Lsp.Position := match term.startPos with
    | some pos => pctx.text.utf8PosToLspPos pos
    | none => ⟨0, 0⟩

  -- Traverse the expression tree using rules
  let nodesWithDepth ← term.ctx.runMetaM lctx do
    traverseExpr lctx term.termInfo.expr 0

  -- Convert ProtoNodes to ParsedTermSteps
  let toStep := fun (node : ProtoNode) (depth : Nat) => do
    let lspPos : Lsp.Position := ⟨baseLspPos.line + depth, baseLspPos.character⟩
    let (exprStr, typeStr) ← term.ctx.runMetaM lctx do
      let exprStr ← ppExprStr ppCtx node.expr
      let typeStr ← match term.termInfo.expectedType? with
        | some ty => ppGoalType term.ctx ty
        | none => ppGoalType term.ctx (← Meta.inferType node.expr)
      return (exprStr, typeStr)
    return (ParsedTermStep.mk exprStr bindings (some typeStr) false lspPos depth node.kind (isCompleteExpr node.expr))

  let mut result : List ParsedTermStep := []
  for (node, depth) in nodesWithDepth do
    let step ← toStep node depth
    result := step :: result

  return result

/-! # DAG Construction -/

/-- Sort steps by position (line, then character). -/
def sortByPosition (steps : List ParsedTermStep) : Array ParsedTermStep :=
  steps.toArray.insertionSort fun a b =>
    a.position.line < b.position.line ||
    (a.position.line == b.position.line && a.position.character < b.position.character)

/-- Deduplicate steps by (position, expression). -/
def deduplicateSteps (steps : Array ParsedTermStep) : Array ParsedTermStep :=
  let (_, result) : Std.HashSet (Nat × Nat × String) × Array ParsedTermStep :=
    steps.foldl (init := ({}, #[])) fun (seen, result) step =>
      let key := (step.position.line, step.position.character, step.expression)
      if seen.contains key then (seen, result)
      else (seen.insert key, result.push step)
  result

/-- Build parent relationships for intermediate nodes. -/
def buildIntermediateNodes (steps : Array ParsedTermStep) : Array IntermediateNode := Id.run do
  let mut nodes : Array IntermediateNode := #[]
  let mut parentStack : List (Nat × List ParsedBinding) := []
  let mut lastConditionId : Option Nat := none
  let mut lastConditionPartId : Option Nat := none

  for h : idx in [:steps.size] do
    let step := steps[idx]
    let mut parentId : Option Nat := none
    let mut parentBindings : List ParsedBinding := []
    let mut depth := parentStack.length

    match step.nodeKind with
    | .conditionPart _ =>
      match lastConditionPartId with
      | some pid =>
        parentId := some pid
        depth := nodes[pid]?.map (·.depth + 1) |>.getD depth
        parentBindings := step.bindings
      | none =>
        for (pid, pb) in parentStack do
          if pb.length <= step.bindings.length then
            parentId := some pid; parentBindings := pb; break
      lastConditionPartId := some idx

    | .condition =>
      match lastConditionPartId with
      | some pid =>
        parentId := some pid
        depth := nodes[pid]?.map (·.depth + 1) |>.getD depth
        parentBindings := step.bindings
      | none =>
        for (pid, pb) in parentStack do
          if pb.length <= step.bindings.length then
            parentId := some pid; parentBindings := pb; break
      lastConditionId := some idx
      lastConditionPartId := none

    | .branch _ =>
      parentId := lastConditionId
      depth := lastConditionId.bind (fun i => nodes[i]?) |>.map (·.depth + 1) |>.getD depth
      parentBindings := step.bindings

    | .matchScrutinee =>
      for (pid, pb) in parentStack do
        if pb.length <= step.bindings.length then
          parentId := some pid; parentBindings := pb; break
      lastConditionId := some idx

    | _ =>
      for (pid, pb) in parentStack do
        if pb.length <= step.bindings.length then
          parentId := some pid; parentBindings := pb; break

    nodes := nodes.push {
      nodeKind := step.nodeKind, expression := step.expression
      bindings := step.bindings, parentBindings, expectedType := step.expectedType
      position := step.position, depth, parentId
      isComplete := step.isComplete
    }

    if step.nodeKind.affectsParentStack then
      parentStack := (idx, step.bindings) :: parentStack

  return nodes

/-- Build child map from intermediate nodes. -/
def buildChildrenMap (nodes : Array IntermediateNode) : Std.HashMap Nat (Array Nat) :=
  nodes.zipIdx.foldl (init := {}) fun map (node, idx) =>
    match node.parentId with
    | some pid => map.insert pid ((map.get? pid |>.getD #[]).push idx)
    | none => map

/-- Convert intermediate nodes to GraphNodes. -/
def buildGraphNodes (nodes : Array IntermediateNode) (childrenMap : Std.HashMap Nat (Array Nat))
    : Array GraphNode :=
  nodes.mapIdx fun idx node =>
    let children := childrenMap.get? idx |>.getD #[]
    let edges := children.map fun cid =>
      { target := cid, label := nodes[cid]?.map (·.nodeKind.branchLabel) |>.join
        kind := none, attributes := Json.mkObj [] : GraphEdge }
    { id := idx
      content := .plain node.expression
      kind := s!"{node.nodeKind}"
      position := node.position
      edges, parent := node.parentId, depth := node.depth
      metadata := Json.mkObj [
        ("bindings_before", bindingsToJson (node.parentBindings.map (·.binding)).toArray),
        ("bindings_after", bindingsToJson (node.bindings.map (·.binding)).toArray),
        ("new_binding_indices", Json.arr (newBindingIndices node.parentBindings node.bindings |>.map toJson)),
        ("expected_type", node.expectedType.getD ""),
        ("is_complete", node.isComplete),
        ("branch_label", node.nodeKind.branchLabel.getD "")
      ] }

/-- Extract initial context (function parameters) from first node. -/
def extractInitialContext (nodes : Array IntermediateNode) : Array LocalBinding :=
  nodes[0]?.map (·.bindings.map (·.binding) |>.toArray.filter fun b =>
    b.bindingKind == .funParam && !b.name.any (· == '✝') && b.name.isUserVisible
  ) |>.getD #[]

/-- Build GenericDag from parsed steps. -/
def buildDag (steps : List ParsedTermStep) (position : Lsp.Position) (definitionName : Option String)
    : GenericDag :=
  if steps.isEmpty then
    { displayStyle := .dataflow, nodes := #[], metadata := Json.mkObj [] }
  else Id.run do
    let dedupedSteps := deduplicateSteps (sortByPosition steps)
    let intermediateNodes := buildIntermediateNodes dedupedSteps
    let childrenMap := buildChildrenMap intermediateNodes
    let graphNodes := buildGraphNodes intermediateNodes childrenMap

    return {
      displayStyle := .dataflow
      nodes := graphNodes
      rootNodeId := if graphNodes.isEmpty then none else some 0
      currentNodeId := findCurrentNodeId graphNodes position
      initialContext := extractInitialContext intermediateNodes
      definitionName
      definitionType := dedupedSteps[0]?.bind (·.expectedType) |>.map .plain
      orphans := #[]
      metadata := Json.mkObj []
    }

/-! # Main Entry Point -/

/-- Parse term-mode InfoTree and build GenericDag with dataflow display style. Pure version. -/
def computeFunctionalDagPure (infoTree : InfoTree) (position : Lsp.Position)
    (ctx : DagContext) : IO (Option GenericDag) := do
  log! s!"computeFunctionalDagPure: position={position}"

  let isTermMode := isTermModeTree infoTree
  log! s!"  isTermModeTree={isTermMode}"
  unless isTermMode do return none

  let (terms, binderCache) := collectTermsAndBinders infoTree ctx.fileMap
  let pctx : TermParserContext := {
    binderCache
    fileUri := ctx.fileUri
    text := ctx.fileMap
    position
  }

  let steps ← collectTermInfosPure pctx terms
  log! s!"  collectTermInfos returned {steps.length} steps"
  if steps.isEmpty then
    log! s!"  returning none (no steps)"
    return none

  let definitionName := getDefinitionName infoTree
  let dag := buildDag steps position definitionName
  log! s!"  buildDag returned {dag.nodes.size} nodes, initialContext={dag.initialContext.size}"

  return some dag

end LeanDag.DataFlow
