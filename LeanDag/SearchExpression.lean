import Lean
import LeanDag.Protocol

/-!
# Expression Search Utilities

Shared utilities for searching and extracting expressions from Lean's InfoTree.
Used by DataFlow, EffectFlow, and SemanticTableau display styles.
-/

open Lean Elab Server

namespace LeanDag.SearchExpression

/-! ## Pretty-Printing -/

/-- Pretty-print an expression to a string using the given PPContext. -/
def ppExprStr (ppCtx : PPContext) (e : Expr) : IO String :=
  return (← ppExprWithInfos ppCtx e).fmt.pretty

/-! ## Term Collection -/

/-- A collected term from the InfoTree with position information. -/
structure CollectedTerm where
  ctx : ContextInfo
  termInfo : TermInfo
  startPos : Option String.Pos.Raw
  endPos : Option String.Pos.Raw

/-- Collect all TermInfo nodes from an InfoTree with their positions. -/
def collectTerms (infoTree : InfoTree) : Array CollectedTerm :=
  infoTree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo termInfo =>
      acc.push { ctx, termInfo, startPos := info.pos?, endPos := info.tailPos? }
    | _ => acc

/-- Collect all expressions with their byte positions, sorted by position. -/
def collectExprPositions (infoTree : InfoTree) : Array (Expr × Nat) :=
  let unsorted := infoTree.foldInfo (init := #[]) fun _ info arr =>
    match info with
    | .ofTermInfo ti =>
      match info.pos? with
      | some pos => arr.push (ti.expr, pos.byteIdx)
      | none => arr
    | _ => arr
  unsorted.insertionSort fun (_, p1) (_, p2) => p1 < p2

/-- Collect terms and expression positions in a single InfoTree traversal. -/
def collectTermsAndPositions (infoTree : InfoTree)
    : Array CollectedTerm × Array (Expr × Nat) :=
  let (terms, unsorted) := infoTree.foldInfo (init := (#[], #[])) fun ctx info (terms, positions) =>
    match info with
    | .ofTermInfo termInfo =>
      let terms' := terms.push { ctx, termInfo, startPos := info.pos?, endPos := info.tailPos? }
      let positions' := match info.pos? with
        | some pos => positions.push (termInfo.expr, pos.byteIdx)
        | none => positions
      (terms', positions')
    | _ => (terms, positions)
  (terms, unsorted.insertionSort fun (_, p1) (_, p2) => p1 < p2)

/-! ## Outermost Expression Finding -/

/-- Filter and sort candidates by position, returning the outermost (earliest). -/
private def selectOutermost (candidates : Array (CollectedTerm × Lsp.Position × Lsp.Position))
    : Option CollectedTerm :=
  let sorted := candidates.insertionSort fun (_, s1, _) (_, s2, _) =>
    s1.line < s2.line || (s1.line == s2.line && s1.character < s2.character)
  sorted[0]?.map (·.1)

/-- Check if a term's position range contains the cursor position. -/
private def containsCursor (term : CollectedTerm) (text : FileMap) (cursor : Lsp.Position)
    : Option (CollectedTerm × Lsp.Position × Lsp.Position) :=
  match term.startPos, term.endPos with
  | some startPos, some endPos =>
    let startLsp := text.utf8PosToLspPos startPos
    let endLsp := text.utf8PosToLspPos endPos
    if startLsp.line <= cursor.line && endLsp.line >= cursor.line then
      some (term, startLsp, endLsp)
    else none
  | some startPos, none =>
    let startLsp := text.utf8PosToLspPos startPos
    if startLsp.line <= cursor.line then
      some (term, startLsp, startLsp)
    else none
  | _, _ => none

/-- Find the outermost expression matching a predicate, containing the cursor position. -/
def findOutermostTerm (terms : Array CollectedTerm) (text : FileMap) (cursor : Lsp.Position)
    (ruleApplies : Expr → Bool) : Option CollectedTerm :=
  let candidates := terms.filterMap fun term =>
    if ruleApplies term.termInfo.expr then containsCursor term text cursor else none
  selectOutermost candidates

/-! ## Current Node Selection -/

/-- Find the current node ID based on cursor position.
    Returns the ID of the last node whose position is at or before the cursor. -/
def findCurrentNodeId (nodes : Array GraphNode) (cursor : Lsp.Position) : Option Nat :=
  let best : Option (Nat × Nat) := nodes.foldl (init := none) fun best node =>
    if node.position.line <= cursor.line then
      match best with
      | some (_, bestLine) =>
        if node.position.line >= bestLine then some (node.id, node.position.line) else best
      | none => some (node.id, node.position.line)
    else best
  best.map (·.1)

/-! ## Binder Cache -/

abbrev BinderCache := Std.HashMap FVarId Lsp.Position

/-- Build a cache of binder positions by traversing InfoTree once.
    Used for efficient goto-definition on hypotheses/bindings. -/
def buildBinderCache (infoTree : InfoTree) (text : FileMap) : BinderCache :=
  infoTree.foldInfo (init := {}) fun _ctx info cache =>
    match info with
    | .ofTermInfo { isBinder := true, expr := .fvar fvarId .., .. } =>
      info.range?.map (fun r => cache.insert fvarId (text.utf8PosToLspPos r.start)) |>.getD cache
    | _ => cache

/-- Collect terms and binder cache in a single InfoTree traversal. -/
def collectTermsAndBinders (infoTree : InfoTree) (text : FileMap)
    : Array CollectedTerm × BinderCache :=
  infoTree.foldInfo (init := (#[], {})) fun ctx info (terms, cache) =>
    match info with
    | .ofTermInfo termInfo =>
      let terms' := terms.push { ctx, termInfo, startPos := info.pos?, endPos := info.tailPos? }
      let cache' := if termInfo.isBinder then
        match termInfo.expr with
        | .fvar fvarId => info.range?.map (fun r =>
            cache.insert fvarId (text.utf8PosToLspPos r.start)) |>.getD cache
        | _ => cache
      else cache
      (terms', cache')
    | _ => (terms, cache)

/-! ## Per-file Context -/

/-- Per-file context needed by all DAG builders. -/
structure DagContext where
  fileMap : FileMap
  fileUri : String

/-! ## Navigation Context -/

/-- Bundled context for goto-definition navigation on bindings. -/
structure NavigationContext where
  binderCache : BinderCache := {}
  fileUri : String := ""

/-! ## Binding Formatting -/

/-- Determine the binding kind from LocalDecl. -/
def bindingKindFromDecl (decl : LocalDecl) : BindingKind :=
  match decl.binderInfo with
  | .default => if decl.value?.isSome then .letBind else .funParam
  | .implicit | .strictImplicit => .funParam
  | .instImplicit => .funParam

/-- Format a local declaration to LocalBinding for the protocol. -/
def formatLocalBinding (ppCtx : PPContext) (decl : LocalDecl)
    (nav : NavigationContext := {}) : IO LocalBinding := do
  let typeStr ← ppExprStr ppCtx decl.type
  let valueStr ← decl.value?.mapM fun v => ppExprStr ppCtx v
  let navLoc := nav.binderCache.get? decl.fvarId |>.map fun pos =>
    { definition := some { uri := nav.fileUri, position := pos } : PreresolvedNavigationTargets }
  return {
    name := decl.userName.toString
    type := .plain typeStr
    value := valueStr.map AnnotatedTextTree.plain
    id := decl.fvarId.name.toString
    bindingKind := bindingKindFromDecl decl
    isImplicit := decl.binderInfo == .implicit || decl.binderInfo == .strictImplicit
    isInstance := decl.binderInfo == .instImplicit
    navigationLocations := navLoc
  }

/-- Extract function parameters from LocalContext. -/
def extractFunctionParams (ppCtx : PPContext) (lctx : LocalContext)
    (nav : NavigationContext := {}) : IO (Array LocalBinding) :=
  lctx.foldrM (init := #[]) fun decl acc => do
    if decl.isAuxDecl || decl.isImplementationDetail then return acc
    let binding ← formatLocalBinding ppCtx decl nav
    if binding.bindingKind == .funParam then return acc.push binding else return acc

end LeanDag.SearchExpression
