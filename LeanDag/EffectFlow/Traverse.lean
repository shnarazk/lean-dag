module

public import Lean
public import Std.Data.HashMap
public import LeanDag.EffectFlow.RuleRegistry
public import LeanDag.EffectFlow.MonadPatterns
public import LeanDag.Logging

@[expose] public section

/-!
# Effect Flow Expression Traversal

Analyzes expressions for monadic effects using registered rules.
Produces `EffectNode`s with return/effect decompositions.
-/

open Lean Meta
open LeanDag.EffectFlow

namespace LeanDag.EffectFlow

/-! ## Types -/

structure EffectNode where
  id : Nat
  expr : Expr
  displayExpr : Expr
  lctx : LocalContext
  kind : String
  forwardOutput : String := ""
  givenBack : String := ""
  stateEffect : String := "none"
  forwardDesc : String := ""
  backwardDesc : String := ""
  position : Option Nat := none
  children : Array (Nat × String × Option String) := #[]
  parent : Option Nat := none
  depth : Nat := 0
  fromUnfolding : Bool := false
  extraMetadata : List (String × String) := []
  deriving Inhabited

structure TraverseState where
  nodes : Array EffectNode := #[]
  nextId : Nat := 0
  depth : Nat := 0
  maxDepth : Nat := 100
  allPositions : Array (Expr × Nat) := #[]
  inUnfolding : Bool := false
  deriving Inhabited

abbrev TraverseM := StateT TraverseState MetaM

/-! ## Helpers -/

def getHeadConstName (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

def ppOptExpr (lctx : LocalContext) (e? : Option Expr) : MetaM String := do
  match e? with
  | some expr => withLCtx lctx (← getLocalInstances) do pure (toString (← Meta.ppExpr expr))
  | none => pure ""

/-! ## Traversal -/

partial def analyzeExpr (e : Expr) (lctx : LocalContext) (parentId : Option Nat := none)
    : TraverseM (Option Nat) := do
  let state ← get
  if state.depth >= state.maxDepth then return none

  match ← findRule e with
  | some rule =>
    match ← rule.analyze e lctx with
    | some result => createNode e lctx parentId result
    | none => defaultRecurse e lctx parentId
  | none => defaultRecurse e lctx parentId

where
  createNode (e : Expr) (lctx : LocalContext) (parentId : Option Nat) (result : AnalyzeResult)
      : TraverseM (Option Nat) := do
    let state ← get
    let nodeId := state.nextId
    modify fun s => { s with nextId := s.nextId + 1, depth := s.depth + 1 }

    let childInfos ← result.children.foldlM (init := #[]) fun acc (childExpr, edgeKind, edgeLabel) => do
      match ← analyzeExpr childExpr lctx (some nodeId) with
      | some childId => pure (acc.push (childId, edgeKind, edgeLabel))
      | none => pure acc

    modify fun s => { s with depth := s.depth - 1 }

    let node : EffectNode := {
      id := nodeId, expr := e, displayExpr := result.displayExpr.getD e, lctx, kind := result.kind
      forwardOutput := ← ppOptExpr lctx result.forwardOutput
      givenBack := ← ppOptExpr lctx result.givenBack
      stateEffect := result.stateEffect.toString
      forwardDesc := result.forwardDesc, backwardDesc := result.backwardDesc
      children := childInfos, parent := parentId, depth := state.depth
      fromUnfolding := state.inUnfolding, extraMetadata := result.extraMetadata
    }
    modify fun s => { s with nodes := s.nodes.push node }
    return some nodeId

  tryUnfold (e : Expr) (lctx : LocalContext) (parentId : Option Nat) : TraverseM (Option Nat) := do
    let state ← get
    if state.depth > 1 then return none

    let some (name, us) := e.getAppFn.constName?.map (·, e.getAppFn.constLevels!) | return none
    if name.isAnonymous || name.isNum || name.hasMacroScopes then return none

    let some (.defnInfo val) := (← getEnv).find? name | return none
    let body := (val.value.instantiateLevelParams val.levelParams us).beta e.getAppArgs
    let wasInUnfolding := state.inUnfolding
    modify fun s => { s with inUnfolding := true }
    let result ← analyzeExpr body lctx parentId
    modify fun s => { s with inUnfolding := wasInUnfolding }
    return result

  defaultRecurse (e : Expr) (lctx : LocalContext) (parentId : Option Nat) : TraverseM (Option Nat) := do
    match e with
    | .app _ _ =>
      if let some result := ← tryUnfold e lctx parentId then return some result
      let fnId? ← analyzeExpr e.getAppFn lctx parentId
      let mut firstArgId? : Option Nat := none
      for arg in e.getAppArgs do
        if let some id := ← analyzeExpr arg lctx parentId then
          if firstArgId?.isNone then firstArgId? := some id
      return firstArgId?.orElse (fun () => fnId?)

    | .const .. => tryUnfold e lctx parentId

    | .lam name ty body bi =>
      let fvarId ← mkFreshFVarId
      let lctx' := lctx.mkLocalDecl fvarId name ty bi
      modify fun s => { s with depth := s.depth + 1 }
      let result ← analyzeExpr (body.instantiate1 (.fvar fvarId)) lctx' parentId
      modify fun s => { s with depth := s.depth - 1 }
      return result

    | .letE name ty value body _ =>
      let _ ← analyzeExpr value lctx parentId
      let fvarId ← mkFreshFVarId
      let lctx' := lctx.mkLetDecl fvarId name ty value
      modify fun s => { s with depth := s.depth + 1 }
      let result ← analyzeExpr (body.instantiate1 (.fvar fvarId)) lctx' parentId
      modify fun s => { s with depth := s.depth - 1 }
      return result

    | .mdata _ inner => analyzeExpr inner lctx parentId
    | _ => return none

/-! ## Position Assignment -/

def buildChildrenMap (nodes : Array EffectNode) : Std.HashMap Nat (Array Nat) :=
  nodes.zipIdx.foldl (init := {}) fun map (node, idx) =>
    match node.parent with
    | some pid => map.insert pid ((map.get? pid |>.getD #[]).push idx)
    | none => map

def deduplicatePositions (positions : Array (Expr × Nat)) : Array (Expr × Nat) :=
  let (_, result) : Std.HashSet (Name × Nat) × Array (Expr × Nat) :=
    positions.foldl (init := ({}, #[])) fun (seen, result) (e, off) =>
      match getHeadConstName e with
      | some n =>
        if seen.contains (n, off) then (seen, result)
        else (seen.insert (n, off), result.push (e, off))
      | none => (seen, result)
  result

/-- Walk up the parent chain to find the nearest ancestor with an assigned position. -/
def findAncestorPosition (nodes : Array EffectNode) (idToIdx : Std.HashMap Nat Nat)
    (node : EffectNode) (fuel : Nat := nodes.size) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    node.position <|> (node.parent >>= idToIdx.get? >>= fun idx =>
      if h : idx < nodes.size then findAncestorPosition nodes idToIdx nodes[idx] fuel
      else none)

def assignPositions (nodes : Array EffectNode) (allPositions : Array (Expr × Nat))
    : IO (Array EffectNode) := do
  if nodes.isEmpty then return nodes

  let positions := deduplicatePositions allPositions
  let childrenMap := buildChildrenMap nodes
  let some rootIdx := nodes.findIdx? (·.parent.isNone) | return nodes

  -- BFS to assign positions in tree order
  let mut result := nodes
  let mut claimed : Std.HashSet Nat := {}
  let mut occurrences : Std.HashMap Name Nat := {}
  let mut queue : Array Nat := #[rootIdx]
  let mut visited : Std.HashSet Nat := {}

  while !queue.isEmpty do
    let nodeIdx := queue[0]!
    queue := queue.eraseIdx! 0
    if visited.contains nodeIdx then continue
    visited := visited.insert nodeIdx

    if nodeIdx < result.size then
      let node := result[nodeIdx]!

      -- Skip unfolded nodes, try to assign position otherwise
      if !node.fromUnfolding then
        if let some name := getHeadConstName node.displayExpr then
          let occIdx := occurrences.get? name |>.getD 0
          occurrences := occurrences.insert name (occIdx + 1)

          -- Find nth unclaimed position for this name
          let matching := positions.filter fun (e, off) =>
            getHeadConstName e == some name && !claimed.contains off
          if let some (_, offset) := matching[occIdx]? then
            result := result.set! nodeIdx { node with position := some offset }
            claimed := claimed.insert offset

      -- Enqueue children
      for idx in childrenMap.get? result[nodeIdx]!.id |>.getD #[] do
        queue := queue.push idx

  -- Propagate parent positions to unpositioned children by walking up the parent chain
  let idToIdx := result.zipIdx.foldl (init := ({} : Std.HashMap Nat Nat)) fun m (node, idx) =>
    m.insert node.id idx
  result := result.map fun node =>
    if node.position.isSome then node
    else { node with position := findAncestorPosition result idToIdx node }

  -- Rebuild children arrays from parent relationships
  return result.map fun node =>
    let childIds := childrenMap.get? node.id |>.getD #[] |>.filterMap fun idx =>
      if idx < result.size then
        let childId := result[idx]!.id
        if node.children.any (·.1 == childId) then none else some (childId, "dataFlow", none)
      else none
    { node with children := node.children ++ childIds }

/-! ## Entry Point -/

def analyze (e : Expr) (lctx : LocalContext)
    (allPositions : Array (Expr × Nat) := #[]) : MetaM (Array EffectNode) := do
  let (_, state) ← analyzeExpr e lctx |>.run { allPositions }
  assignPositions state.nodes allPositions

end LeanDag.EffectFlow
