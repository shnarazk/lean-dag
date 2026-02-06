import Lean
import Lean.Meta.Basic
import LeanDag.Protocol
import LeanDag.Logging
import LeanDag.SearchExpression
import LeanDag.NameUtils
import LeanDag.EffectFlow.Traverse

/-!
# Effect Flow DAG Computation

Main entry point for computing effect flow DAGs from monadic Lean code.
-/

open Lean Elab Server Meta
open LeanDag.SearchExpression (CollectedTerm collectTerms collectTermsAndPositions findOutermostTerm extractFunctionParams ppExprStr)
open LeanDag.EffectFlow

namespace LeanDag.EffectFlow

/-! ## Node Conversion -/

/-- Convert an EffectNode to a protocol GraphNode. -/
def effectNodeToGraphNode (node : EffectNode) (ppCtx : PPContext) (text : FileMap)
    : IO GraphNode := do
  -- Pretty-print the display expression using the node's local context
  let nodePpCtx := { ppCtx with lctx := node.lctx }
  let exprStr ← ppExprStr nodePpCtx node.displayExpr

  let fwdStr := if node.forwardOutput.isEmpty then node.forwardDesc else node.forwardOutput
  let bwdStr := if node.givenBack.isEmpty then node.backwardDesc else node.givenBack

  let baseMetadata : List (String × Json) := [
    ("forward", Json.str fwdStr),
    ("backward", Json.str bwdStr),
    ("stateEffect", Json.str node.stateEffect),
    ("forwardOutput", Json.str node.forwardOutput),
    ("givenBack", Json.str node.givenBack),
    ("forwardDesc", Json.str node.forwardDesc),
    ("backwardDesc", Json.str node.backwardDesc),
    ("fromUnfolding", Json.bool node.fromUnfolding)
  ]
  let extraMetadata := node.extraMetadata.map fun (k, v) => (k, Json.str v)
  let metadata := Json.mkObj (baseMetadata ++ extraMetadata)

  -- Convert children to edges
  let edges := node.children.map fun (childId, edgeKind, edgeLabel) =>
    { target := childId
      label := edgeLabel
      kind := some edgeKind
      attributes := Json.mkObj [] : GraphEdge }

  -- Convert position
  let position := node.position.map fun byteOffset =>
    text.utf8PosToLspPos ⟨byteOffset⟩

  return {
    id := node.id
    content := .plain exprStr
    kind := node.kind
    position := position.getD ⟨0, 0⟩
    edges := edges
    parent := node.parent
    depth := node.depth
    metadata := metadata
  }

/-! ## Main Entry Point -/

/-- Check if any rule applies to the expression. Pure version. -/
def anyRuleApplies (rules : Array EffectRule) (e : Expr) : Bool :=
  rules.any fun r => r.appliesTo e

/-- Check if expression is a truly effectful monadic operation.
    Only bind, state ops, throw, and catch indicate monadic code.
    if-then-else and pure can appear in non-monadic code. -/
def isMonadicExpr (e : Expr) : Bool :=
  isMonadBind e || isStateGet e || isStatePut e || isStateModify e || isThrow e || isCatch e

/-- Check if an InfoTree contains effectful monadic code.
    Returns true only if there are actual monadic operations (bind, state, throw/catch),
    not just if-then-else or pure which can appear in non-monadic code. -/
def isEffectfulTree (infoTree : InfoTree) : Bool :=
  let terms := collectTerms infoTree
  terms.any fun t => isMonadicExpr t.termInfo.expr

/-- Compute effect flow DAG from an InfoTree and position. Pure version.
    Returns None if not effectful code or analysis fails.

    Strategy: Find the outermost monadic expression that contains the cursor,
    analyze it fully, then mark which nodes are at/before cursor position. -/
def computeEffectFlowDagPure (infoTree : InfoTree) (position : Lsp.Position) (text : FileMap)
    : IO (Option GenericDag) := do
  let rules ← getRules

  -- Collect terms and expression positions in a single traversal
  let (terms, allPositions) := collectTermsAndPositions infoTree
  let some term := findOutermostTerm terms text position (anyRuleApplies rules ·)
    | return none

  -- Analyze the full expression and infer definition type in one MetaM block
  let lctx := term.termInfo.lctx.sanitizeNames.run' {options := {}}
  let ppCtx := term.ctx.toPPContext lctx
  let (nodes, definitionType) ← term.ctx.runMetaM lctx do
    let nodes ← analyze term.termInfo.expr lctx allPositions
    let ty ← Meta.inferType term.termInfo.expr
    let tyStr ← ppExprStr ppCtx ty
    return (nodes, some (AnnotatedTextTree.plain tyStr))

  -- DEBUG: Log position assignment results
  log! s!"[EffectFlow] ========================================="
  log! s!"[EffectFlow] === Position Debug ==="
  log! s!"[EffectFlow] InfoTree positions: {allPositions.size}, Nodes created: {nodes.size}"

  log! s!"[EffectFlow] --- InfoTree positions (sorted by line) ---"
  for (expr, byteOffset) in allPositions do
    let lspPos := text.utf8PosToLspPos ⟨byteOffset⟩
    let headName := match expr.getAppFn with
      | .const n _ => n.toString
      | .fvar id => s!"fvar:{id.name}"
      | other => s!"other:{other.ctorName}"
    log! s!"[EffectFlow]   byte {byteOffset} (line {lspPos.line + 1}): {headName}"

  log! s!"[EffectFlow] --- Node position results ---"
  let nodesWithPos := nodes.filter (·.position.isSome)
  let nodesWithoutPos := nodes.filter (·.position.isNone)
  for node in nodes do
    let posStr := match node.position with
      | some p =>
        let lspPos := text.utf8PosToLspPos ⟨p⟩
        s!"line {lspPos.line + 1} (byte {p})"
      | none => "NONE"
    log! s!"[EffectFlow]   Node {node.id} ({node.kind}): pos={posStr}"

  log! s!"[EffectFlow] --- Summary ---"
  log! s!"[EffectFlow]   Nodes with positions: {nodesWithPos.size}/{nodes.size}"
  if nodesWithoutPos.size > 0 then
    log! s!"[EffectFlow]   MISSING positions for: {nodesWithoutPos.map (fun n => s!"{n.id}({n.kind})") |> Array.toList |> String.intercalate ", "}"
  log! s!"[EffectFlow] Cursor: line {position.line + 1}"
  log! s!"[EffectFlow] ========================================="

  if nodes.isEmpty then
    return none

  let definitionName := getDefinitionName infoTree
  let initialContext ← extractFunctionParams ppCtx lctx
  let graphNodes ← nodes.mapM fun node => effectNodeToGraphNode node ppCtx text
  let rootNodeId := (nodes.find? fun n => n.parent.isNone).map (·.id)
  let currentNodeId :=
    let best : Option (Nat × Nat) := nodes.foldl (init := none) fun best node =>
      match node.position with
      | some byteOffset =>
        let lspPos := text.utf8PosToLspPos ⟨byteOffset⟩
        if lspPos.line <= position.line then
          match best with
          | some (_, bestLine) =>
            if lspPos.line >= bestLine then some (node.id, lspPos.line) else best
          | none => some (node.id, lspPos.line)
        else best
      | none => best
    best.map (·.1)

  log! s!"[EffectFlow] --- currentNodeId selection ---"
  log! s!"[EffectFlow]   Cursor at line {position.line + 1}"
  log! s!"[EffectFlow]   Selected currentNodeId: {currentNodeId.map toString |>.getD "none"}"
  if let some nodeId := currentNodeId then
    if let some node := nodes.find? (·.id == nodeId) then
      log! s!"[EffectFlow]   Selected node kind: {node.kind}"

  return some {
    displayStyle := .effectflow
    definitionName, definitionType, initialContext
    nodes := graphNodes, rootNodeId, currentNodeId
    orphans := #[]
    metadata := Json.mkObj []
  }

end LeanDag.EffectFlow
