import Lean
import LeanDag.Protocol

open Lean

namespace LeanDag

/-! ## Proof-Specific Types

These types are used internally for proof visualization but are not part of the
wire protocol schema. They are serialized into the `metadata` field of GraphNode
when building proof DAGs, allowing display-style-specific data to be passed
through the generic DAG structure.
-/

/-- A hypothesis in a proof context.

Represents a local hypothesis available in the proof state, with its type,
optional value (for let-bindings), and metadata for navigation and diff display.
-/
structure ProofContextHypothesis where
  name : String
  type : AnnotatedTextTree
  value : Option AnnotatedTextTree := none
  id : String
  isProofTerm : Bool := false
  isTypeclassInstance : Bool := false
  isImplicit : Bool := false
  isInstance : Bool := false
  isRemoved : Bool := false
  navigationLocations : Option PreresolvedNavigationTargets := none
  deriving Inhabited, ToJson, FromJson

/-- A proof obligation (goal) to be proven.

Represents a goal in the proof state, with its type and metadata for
navigation and diff display.
-/
structure ProofObligation where
  type : AnnotatedTextTree
  username : Option String := none
  id : String
  isRemoved : Bool := false
  navigationLocations : Option PreresolvedNavigationTargets := none
  deriving Inhabited, ToJson, FromJson

/-- A proof state containing goals and hypotheses.

Used to represent the state before and after a tactic application,
enabling diff computation and before/after visualization.
-/
structure TacticProofState where
  goals : Array ProofObligation := #[]
  hypotheses : Array ProofContextHypothesis := #[]
  deriving Inhabited, ToJson, FromJson

/-! ## Node Kind Constants -/

namespace ProofKind
def tactic := "tactic"
end ProofKind

end LeanDag
