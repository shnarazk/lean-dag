module

public import Lean
public import LeanDag.Protocol
public import LeanDag.Graph

@[expose] public section

/-!
# Effect Flow Core Types

This module defines the core types for the effect flow decomposition framework.

Each monadic operation (bind, get, put, throw, catch) is decomposed into:
- Return component: what the operation produces as its result
- Effect component: what state changes are given back to the environment
-/

open Lean

namespace LeanDag.EffectFlow

/-! ## Effect Analysis Result -/

/-- State effect type for classifying how an operation affects state -/
inductive StateEffect where
  | none      -- No state effect (pure computation)
  | read      -- Reads state without modifying
  | write     -- Writes/replaces state
  | modify    -- Modifies state via function
  | error     -- Error/exception effect
  deriving Inhabited, BEq

def StateEffect.toString : StateEffect → String
  | .none => "none"
  | .read => "read"
  | .write => "write"
  | .modify => "modify"
  | .error => "error"

/-- Result of analyzing an expression for effects.
    Used by rules to return the decomposition of an effectful expression.

    Return/effect decomposition of a monadic operation:
    - Return: what the operation produces as its result
    - Effect: what state changes are given back to the environment -/
structure AnalyzeResult where
  /-- Node kind (e.g., "stateRead", "effectBind") -/
  kind : String
  /-- Child expressions with edge metadata -/
  children : Array (Expr × String × Option String) := #[]  -- (expr, edgeKind, edgeLabel)
  /-- Expression to display as node content (overrides default of showing full expr) -/
  displayExpr : Option Expr := none
  /-- Return expression - what the operation produces (e.g., state for get, () for set) -/
  forwardOutput : Option Expr := none
  /-- Effect expression - what state changes are given back (e.g., new state for set) -/
  givenBack : Option Expr := none
  /-- Type of state effect -/
  stateEffect : StateEffect := .none
  /-- Symbolic return description (used when no concrete expression) -/
  forwardDesc : String := ""
  /-- Symbolic effect description (used when no concrete expression) -/
  backwardDesc : String := ""
  /-- Additional metadata key-value pairs -/
  extraMetadata : List (String × String) := []
  deriving Inhabited

/-! ## Effect Rule Structure -/

/-- A rule for analyzing effectful expressions.

Like DataFlow rules, but specialized for monadic effect analysis.
Each rule handles a specific monadic pattern and extracts return/effect
decompositions.

- `name`: Unique identifier for this rule
- `priority`: Higher priority rules are checked first (default: 100)
- `appliesTo`: Predicate that determines if this rule applies
- `analyze`: Extracts the effect structure from the expression
-/
structure EffectRule where
  /-- Unique name for this rule -/
  name : Name
  /-- Higher priority rules are checked first -/
  priority : Nat := 100
  /-- Predicate: does this rule apply to the expression? -/
  appliesTo : Expr → Bool
  /-- Analyze the expression and extract effect structure.
      Takes the expression and local context.
      Returns `none` if the rule doesn't actually apply. -/
  analyze : Expr → LocalContext → MetaM (Option AnalyzeResult)
  deriving Inhabited

/-- Compare rules by priority (higher first). -/
def EffectRule.compareByPriority (r1 r2 : EffectRule) : Ordering :=
  compare r2.priority r1.priority

/-! ## Rule Construction Helpers -/

/-- Create a simple effect rule that produces a leaf node (no children). -/
def EffectRule.leaf (name : Name) (priority : Nat := 100)
    (appliesTo : Expr → Bool)
    (analyze : Expr → LocalContext → MetaM (Option (String × Option Expr × Option Expr × StateEffect))) : EffectRule :=
  { name, priority, appliesTo
    analyze := fun e lctx => do
      match ← analyze e lctx with
      | some (kind, fwdOut, givenBack, effect) =>
        return some { kind, forwardOutput := fwdOut, givenBack, stateEffect := effect }
      | none => return none }

/-- Create an effect rule with explicit children. -/
def EffectRule.withChildren (name : Name) (priority : Nat := 100)
    (appliesTo : Expr → Bool)
    (analyze : Expr → LocalContext → MetaM (Option AnalyzeResult)) : EffectRule :=
  { name, priority, appliesTo, analyze }

/-! ## Metadata Helpers -/

def mkEffectMetadata (forward backward : String) : Json :=
  Json.mkObj [("forward", forward), ("backward", backward)]

def getMetadataStr (metadata : Option Json) (key : String) : Option String :=
  metadata.bind fun j => j.getObjValAs? String key |>.toOption

def addToMetadata (metadata : Option Json) (key : String) (value : String) : Json :=
  match metadata with
  | none => Json.mkObj [(key, value)]
  | some j =>
    match j with
    | .obj kvs => .obj (kvs.insert key (.str value))
    | _ => Json.mkObj [(key, value)]

end LeanDag.EffectFlow
