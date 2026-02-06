module

public import Lean
public import LeanDag.Protocol
public import LeanDag.Graph
public import LeanDag.NameUtils
public import LeanDag.SearchExpression

@[expose] public section

/-!
# Data Flow Decomposition Types

Core types for the extensible data flow decomposition framework.
Each expression form (let, lambda, if, match, etc.) has a decomposition rule that
extracts data flow structure from the expression.
-/

open Lean Elab Server
open LeanDag.SearchExpression (ppExprStr)

namespace LeanDag.DataFlow

/-! ## Node Types -/

/-- Kind of node in the data flow graph (from decomposition rules). -/
inductive NodeKind where
  | binding (name : Name)
  | lambda (name : Name)
  | branch (label : String)
  | condition
  | conditionPart (index : Nat)
  | matchScrutinee
  | result
  deriving Inhabited, BEq, Repr

def NodeKind.toLabel : NodeKind → String
  | .binding name => s!"let {name}"
  | .lambda name => s!"fun {name}"
  | .branch label => label
  | .condition => "condition"
  | .conditionPart i => s!"condition[{i}]"
  | .matchScrutinee => "match"
  | .result => "result"

instance : ToString NodeKind where
  toString
    | .binding _ => "binding"
    | .lambda _ => "lambda"
    | .branch _ => "branch"
    | .condition => "condition"
    | .conditionPart _ => "conditionPart"
    | .matchScrutinee => "matchScrutinee"
    | .result => "result"

def NodeKind.affectsParentStack : NodeKind → Bool
  | .conditionPart _ | .condition | .branch _ => false
  | _ => true

def NodeKind.branchLabel : NodeKind → Option String
  | .branch label => some label
  | .conditionPart i => some s!"condition {i + 1}"
  | _ => none

/-! ## Decomposition Types -/

/-- A node produced by decomposition, before ID assignment. -/
structure ProtoNode where
  kind : NodeKind
  expr : Expr
  position : Option Nat := none
  deriving Inhabited

/-- Result of decomposing an expression. -/
structure DecomposeResult where
  nodes : Array ProtoNode
  children : Option (Array Expr) := none
  displayExpr : Option Expr := none
  deriving Inhabited

/-! ## Builder Types -/

/-- A parsed binding from LocalContext. -/
structure ParsedBinding where
  binding : LocalBinding
  fvarId : FVarId
  deriving Inhabited

instance : BEq ParsedBinding where
  beq b1 b2 := b1.fvarId == b2.fvarId

/-- A parsed term step from TermInfo. -/
structure ParsedTermStep where
  expression : String
  bindings : List ParsedBinding
  expectedType : Option String
  isBinder : Bool
  position : Lsp.Position
  depth : Nat
  nodeKind : NodeKind := .result
  isComplete : Bool := true
  deriving Inhabited

/-- Intermediate node during DAG construction. -/
structure IntermediateNode where
  nodeKind : NodeKind
  expression : String
  bindings : List ParsedBinding
  parentBindings : List ParsedBinding
  expectedType : Option String
  position : Lsp.Position
  depth : Nat
  parentId : Option Nat
  isComplete : Bool
  deriving Inhabited

/-- Context for parsing term information. -/
structure TermParserContext where
  binderCache : Std.HashMap FVarId Lsp.Position
  fileUri : String
  text : FileMap
  position : Lsp.Position

def TermParserContext.toNavigationContext (pctx : TermParserContext) : SearchExpression.NavigationContext :=
  { binderCache := pctx.binderCache, fileUri := pctx.fileUri }

/-! ## Expression Utilities -/

def unwrapMdata : Expr → Expr
  | .mdata _ inner => unwrapMdata inner
  | e => e

def getDefaultChildren (e : Expr) : Array Expr :=
  match e with
  | .app fn arg => #[fn, arg]
  | .lam _ _ body _ => #[body]
  | .letE _ _ value body _ => #[value, body]
  | .forallE _ _ body _ => #[body]
  | .mdata _ inner => #[inner]
  | .proj _ _ struct => #[struct]
  | _ => #[]

partial def hasSorry : Expr → Bool
  | .const ``sorryAx _ => true
  | .app fn arg => hasSorry fn || hasSorry arg
  | .lam _ ty body _ => hasSorry ty || hasSorry body
  | .forallE _ ty body _ => hasSorry ty || hasSorry body
  | .letE _ ty val body _ => hasSorry ty || hasSorry val || hasSorry body
  | .mdata _ inner => hasSorry inner
  | .proj _ _ struct => hasSorry struct
  | _ => false

def isCompleteExpr (e : Expr) : Bool := !hasSorry e

/-! ## Binding Utilities -/

def bindingKindOf (decl : LocalDecl) : BindingKind :=
  match decl.binderInfo with
  | .default => if decl.value?.isSome then .letBind else .funParam
  | _ => .funParam

def formatBinding (ppCtx : PPContext) (decl : LocalDecl)
    (nav : SearchExpression.NavigationContext) : IO ParsedBinding := do
  let typeStr ← ppExprStr ppCtx decl.type
  let valueStr ← decl.value?.mapM fun v => ppExprStr ppCtx v
  let navLoc := nav.binderCache.get? decl.fvarId |>.map fun pos =>
    { definition := some { uri := nav.fileUri, position := pos } : PreresolvedNavigationTargets }
  pure {
    fvarId := decl.fvarId
    binding := {
      name := decl.userName.toString.filterName
      type := .plain typeStr
      value := valueStr.map .plain
      id := decl.fvarId.name.toString
      bindingKind := bindingKindOf decl
      isImplicit := decl.binderInfo == .implicit || decl.binderInfo == .strictImplicit
      isInstance := decl.binderInfo == .instImplicit
      navigationLocations := navLoc
    }
  }

def formatBindings (ppCtx : PPContext) (lctx : LocalContext)
    (nav : SearchExpression.NavigationContext) : IO (List ParsedBinding) :=
  lctx.foldrM (init := []) fun decl acc => do
    if decl.isAuxDecl || decl.isImplementationDetail then return acc
    return (← formatBinding ppCtx decl nav) :: acc

def bindingsToJson (bindings : Array LocalBinding) : Json :=
  .arr <| bindings.map fun b => Json.mkObj [
    ("name", b.name), ("id", b.id), ("type", b.type.toPlainText),
    ("binding_kind", match b.bindingKind with
      | .letBind => "let_bind" | .funParam => "fun_param"
      | .matchVar => "match_var" | .forVar => "for_var")
  ]

def newBindingIndices (parent child : List ParsedBinding) : Array Nat :=
  (child.zipIdx.filterMap fun (b, i) =>
    if parent.any (·.fvarId == b.fvarId) then none else some i).toArray

/-! ## Term Mode Detection -/

def isByProofTactic (tacticInfo : Elab.TacticInfo) : Bool :=
  match tacticInfo.stx with
  | .node _ kind _ =>
    let kindStr := kind.toString
    kindStr.startsWith "Lean.Parser.Tactic" || kindStr == "Lean.Parser.Command.declaration"
  | .atom _ val => val ∈ ["trivial", "assumption", "rfl", "decide"]
  | _ => false

def isTermModeTree (infoTree : InfoTree) : Bool :=
  let (hasTermInfo, hasByProofTactic) :=
    infoTree.foldInfo (init := (false, false)) fun _ info (ht, hp) =>
      match info with
      | .ofTermInfo _ => (true, hp)
      | .ofTacticInfo ti => (ht, hp || isByProofTactic ti)
      | _ => (ht, hp)
  hasTermInfo && !hasByProofTactic

end LeanDag.DataFlow
