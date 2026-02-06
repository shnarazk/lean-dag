module

public import Lean
public import LeanDag.DataFlow.Types

@[expose] public section

/-!
# Data Flow Decomposition Rules

This module defines the `Rule` structure for decomposition rules and provides
the API for working with rules.

Rules are registered globally via an environment extension and can be added
using the `@[dataflow_rule]` attribute.
-/

open Lean Meta

namespace LeanDag.DataFlow

/-! ## Rule Structure -/

/-- A decomposition rule that extracts data flow structure from expressions.

Like semantic tableaux rules for logical connectives, each rule handles a specific
expression form and decomposes it into nodes and child expressions.

- `name`: Unique identifier for this rule
- `priority`: Higher priority rules are checked first (default: 100)
- `primaryKind`: The primary kind of node this rule produces (for classification)
- `appliesTo`: Predicate that determines if this rule applies to an expression
- `decompose`: Extracts the data flow structure from the expression

The `decompose` function returns `Option DecomposeResult`:
- `some result` → Rule applies, use these nodes and recurse into specified children
- `none` → Rule doesn't apply (shouldn't happen if `appliesTo` returned true)
-/
structure Rule where
  /-- Unique name for this rule -/
  name : Name
  /-- Higher priority rules are checked first -/
  priority : Nat := 100
  /-- The primary kind of node this rule produces -/
  primaryKind : NodeKind := .result
  /-- Predicate: does this rule apply to the expression? -/
  appliesTo : Expr → Bool
  /-- Extract data flow structure from the expression.
      Takes the expression and local context.
      Returns `none` if the rule doesn't actually apply. -/
  decompose : Expr → LocalContext → MetaM (Option DecomposeResult)
  deriving Inhabited

/-- Compare rules by priority (higher first). -/
def Rule.compareByPriority (r1 r2 : Rule) : Ordering :=
  compare r2.priority r1.priority  -- Note: reversed for descending order

/-! ## Rule Helpers -/

/-- Create a simple rule that only produces nodes (uses default children). -/
def Rule.simple (name : Name) (priority : Nat := 100)
    (appliesTo : Expr → Bool)
    (decompose : Expr → LocalContext → MetaM (Option (Array ProtoNode))) : Rule :=
  { name, priority, appliesTo
    decompose := fun e lctx => do
      match ← decompose e lctx with
      | some nodes => return some { nodes, children := none }
      | none => return none }

/-- Create a rule that handles an expression and specifies explicit children. -/
def Rule.withChildren (name : Name) (priority : Nat := 100)
    (appliesTo : Expr → Bool)
    (decompose : Expr → LocalContext → MetaM (Option (Array ProtoNode × Array Expr))) : Rule :=
  { name, priority, appliesTo
    decompose := fun e lctx => do
      match ← decompose e lctx with
      | some (nodes, children) => return some { nodes, children := some children }
      | none => return none }

end LeanDag.DataFlow
