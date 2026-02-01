module

public import Lean

@[expose] public section

open Lean

namespace LeanDag

/-! ## Diff Types (matching Lean.Widget.DiffTag) -/

/-- A tag indicating the diff status of a subexpression. Matches Lean.Widget.DiffTag. -/
inductive DiffTag where
  | wasChanged   -- Subexpression was modified (in "before" view)
  | willChange   -- Subexpression will be modified (in "after" view)
  | wasDeleted   -- Subexpression was deleted (in "before" view)
  | willDelete   -- Subexpression will be deleted (in "after" view)
  | wasInserted  -- Subexpression was inserted (in "before" view)
  | willInsert   -- Subexpression will be inserted (in "after" view)
  deriving Inhabited, BEq, Repr

instance : ToJson DiffTag where
  toJson
    | .wasChanged => "wasChanged"
    | .willChange => "willChange"
    | .wasDeleted => "wasDeleted"
    | .willDelete => "willDelete"
    | .wasInserted => "wasInserted"
    | .willInsert => "willInsert"

instance : FromJson DiffTag where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "wasChanged" => pure .wasChanged
    | "willChange" => pure .willChange
    | "wasDeleted" => pure .wasDeleted
    | "willDelete" => pure .willDelete
    | "wasInserted" => pure .wasInserted
    | "willInsert" => pure .willInsert
    | _ => throw s!"invalid DiffTag: {s}"

/-- Subexpression info with optional diff status. Simplified version of Lean.Widget.SubexprInfo. -/
structure SubexprInfo where
  /-- Diff status for this subexpression (for before/after highlighting). -/
  diffStatus : Option DiffTag := none
  deriving Inhabited, BEq, Repr, ToJson, FromJson

/-! ## Tagged Text (matching Lean.Widget.TaggedText structure) -/

/-- Tagged text that can carry diff information per subexpression.
    Matches the JSON structure of Lean.Widget.TaggedText. -/
inductive TaggedText where
  | text (s : String)
  | append (items : Array TaggedText)
  | tag (info : SubexprInfo) (content : TaggedText)
  deriving Inhabited, BEq, Repr

/-- Convert TaggedText to JSON matching Lean.Widget.TaggedText format. -/
partial def TaggedText.toJson : TaggedText → Json
  | .text s => Json.mkObj [("kind", "text"), ("text", s)]
  | .append items => Json.mkObj [("kind", "append"), ("items", Json.arr (items.map TaggedText.toJson))]
  | .tag info content => Json.mkObj [("kind", "tag"), ("info", Lean.toJson info), ("content", content.toJson)]

instance : ToJson TaggedText := ⟨TaggedText.toJson⟩

/-- Parse TaggedText from JSON. -/
partial def TaggedText.fromJson? (j : Json) : Except String TaggedText := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "text" => return .text (← j.getObjValAs? String "text")
  | "append" =>
    let items ← j.getObjValAs? (Array Json) "items"
    return .append (← items.mapM TaggedText.fromJson?)
  | "tag" =>
    let info ← j.getObjValAs? SubexprInfo "info"
    let content ← j.getObjVal? "content" >>= TaggedText.fromJson?
    return .tag info content
  | _ => throw s!"invalid TaggedText kind: {kind}"

instance : FromJson TaggedText := ⟨TaggedText.fromJson?⟩

/-- Create plain text (no diff info). -/
def TaggedText.plain (s : String) : TaggedText := .text s

/-- Wrap text with a diff tag. -/
def TaggedText.withDiff (t : TaggedText) (tag : DiffTag) : TaggedText :=
  .tag { diffStatus := some tag } t

/-- Extract plain text, stripping all tags. -/
partial def TaggedText.toPlainText : TaggedText → String
  | .text s => s
  | .append items => String.join (items.toList.map TaggedText.toPlainText)
  | .tag _ content => content.toPlainText

/-- Check if the TaggedText is empty. -/
def TaggedText.isEmpty (t : TaggedText) : Bool :=
  t.toPlainText.isEmpty

instance : ToString TaggedText where
  toString t := t.toPlainText

/-- Allow strings to be used where TaggedText is expected. -/
instance : Coe String TaggedText := ⟨TaggedText.text⟩

/-! ## Navigation Types -/

/-- A location for "go to definition" navigation. -/
structure GotoLocation where
  uri : String
  position : Lsp.Position
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-- Pre-resolved goto locations for navigation. -/
structure GotoLocations where
  definition : Option GotoLocation := none
  typeDef : Option GotoLocation := none
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Hypothesis Types -/

/-- Hypothesis info for the TUI proof DAG. -/
structure HypothesisInfo where
  /-- User-visible name. -/
  name : String
  /-- Type expression (with diff highlighting). -/
  type : TaggedText
  /-- Value for let-bindings (with diff highlighting). -/
  value : Option TaggedText := none
  /-- Internal ID for tracking. -/
  id : String
  /-- Whether this hypothesis is a proof term. -/
  isProof : Bool := false
  /-- Whether this is a type class instance. -/
  isInstance : Bool := false
  /-- Whether this hypothesis was removed (for diff display in "before" view). -/
  isRemoved : Bool := false
  /-- Pre-resolved navigation locations. -/
  gotoLocations : GotoLocations := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Goal Types -/

/-- Goal info for the TUI proof DAG. -/
structure GoalInfo where
  /-- Goal type expression (with diff highlighting). -/
  type : TaggedText
  /-- User-visible name (e.g., "case inl"). -/
  username : Option String := none
  /-- Internal goal ID for tracking. -/
  id : String
  /-- Whether this goal was removed (for diff display in "before" view). -/
  isRemoved : Bool := false
  /-- Pre-resolved navigation locations. -/
  gotoLocations : GotoLocations := {}
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Proof State -/

/-- A proof state (goals and hypotheses at a point in the proof). -/
structure ProofState where
  goals : List GoalInfo := []
  hypotheses : List HypothesisInfo := []
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Tactic Info -/

/-- Information about a tactic application. -/
structure TacticInfo where
  /-- The tactic text (e.g., "intro n"). -/
  text : String
  /-- Hypothesis names used by this tactic. -/
  dependsOn : List String := []
  /-- Theorem names referenced by this tactic. -/
  theoremsUsed : List String := []
  deriving Inhabited, ToJson, FromJson, BEq, Repr

/-! ## Proof DAG Node -/

/-- Single node in the proof DAG. -/
structure ProofDagNode where
  id : Nat
  /-- Tactic information. -/
  tactic : TacticInfo
  /-- Position in source file (line, character). -/
  position : Lsp.Position
  /-- State before tactic. -/
  stateBefore : ProofState
  /-- State after tactic. -/
  stateAfter : ProofState
  /-- Indices into stateAfter.hypotheses for new hypotheses. -/
  newHypotheses : List Nat := []
  /-- Child node IDs. -/
  children : List Nat := []
  /-- Parent node ID. -/
  parent : Option Nat := none
  /-- Depth in tree. -/
  depth : Nat := 0
  /-- True if node has spawned goals that are not solved (inline `by` blocks). -/
  hasUnsolvedSpawnedGoals : Bool := false
  deriving Inhabited, ToJson, FromJson, Repr

/-! ## Complete Proof DAG -/

/-- Complete proof DAG structure. -/
structure ProofDag where
  nodes : Array ProofDagNode := #[]
  root : Option Nat := none
  currentNode : Option Nat := none
  initialState : ProofState := {}
  definitionName : Option String := none
  orphans : List Nat := []
  deriving Inhabited, ToJson, FromJson, Repr

instance : BEq ProofDagNode where
  beq a b := a.id == b.id

instance : BEq ProofDag where
  beq a b := a.nodes.toList == b.nodes.toList && a.root == b.root && a.orphans == b.orphans

end LeanDag
