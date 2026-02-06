module

public import Lean
public import JsonSchemaToLean
public import JsonSchemaToLean.Types

@[expose] public section

open Lean

namespace LeanDag


gen_types_from_schema "../protocol-schema.json"

instance : ToString DisplayStyle where
  toString z :=  match z with
    | .effectflow => "effect flow style"
    | .dataflow => "data flow style"
    | _ => "generic style"

open Lean.Widget (DiffTag)

def SubexpressionDiffTag.fromWidgetDiffTag : DiffTag → SubexpressionDiffTag
  | .wasChanged => .wasChanged
  | .willChange => .willChange
  | .wasDeleted => .wasDeleted
  | .willDelete => .willDelete
  | .wasInserted => .wasInserted
  | .willInsert => .willInsert

def SubexpressionDiffTag.toWidgetDiffTag : SubexpressionDiffTag → DiffTag
  | .wasChanged => .wasChanged
  | .willChange => .willChange
  | .wasDeleted => .wasDeleted
  | .willDelete => .willDelete
  | .wasInserted => .wasInserted
  | .willInsert => .willInsert

instance : Coe DiffTag SubexpressionDiffTag := ⟨SubexpressionDiffTag.fromWidgetDiffTag⟩
instance : Coe SubexpressionDiffTag DiffTag := ⟨SubexpressionDiffTag.toWidgetDiffTag⟩

/-! ## Position Conversion Functions -/

def LineCharacterPosition.toLspPosition (p : LineCharacterPosition) : Lsp.Position :=
  ⟨p.line, p.character⟩

def LineCharacterPosition.fromLspPosition (p : Lsp.Position) : LineCharacterPosition :=
  ⟨p.line, p.character⟩

instance : Coe LineCharacterPosition Lsp.Position := ⟨LineCharacterPosition.toLspPosition⟩
instance : Coe Lsp.Position LineCharacterPosition := ⟨LineCharacterPosition.fromLspPosition⟩

/-! ## AnnotatedTextTree Extension Methods -/

def AnnotatedTextTree.plain (s : String) : AnnotatedTextTree := .text s

def AnnotatedTextTree.withDiff (t : AnnotatedTextTree) (tag : SubexpressionDiffTag) : AnnotatedTextTree :=
  .tag { diffStatus := some tag } t

partial def AnnotatedTextTree.toPlainText : AnnotatedTextTree → String
  | .text s => s
  | .append children => String.join (children.toList.map (·.toPlainText))
  | .tag _ content => content.toPlainText

def AnnotatedTextTree.isEmpty (t : AnnotatedTextTree) : Bool :=
  t.toPlainText.isEmpty

instance : ToString AnnotatedTextTree where
  toString t := t.toPlainText

instance : Coe String AnnotatedTextTree := ⟨AnnotatedTextTree.text⟩

/-! ## GraphNode and GenericDag instances -/

instance : BEq GraphEdge where
  beq a b := a.target == b.target && a.label == b.label && a.kind == b.kind

instance : BEq GraphNode where
  beq a b := a.id == b.id

instance : BEq GenericDag where
  beq a b := a.nodes == b.nodes && a.rootNodeId == b.rootNodeId && a.displayStyle == b.displayStyle

/-! ## GenericDag Helper Functions -/

def GenericDag.isEmpty (dag : GenericDag) : Bool :=
  dag.nodes.isEmpty

def GenericDag.len (dag : GenericDag) : Nat :=
  dag.nodes.size

def GenericDag.get (dag : GenericDag) (id : Nat) : Option GraphNode :=
  dag.nodes.find? (·.id == id)




end LeanDag
