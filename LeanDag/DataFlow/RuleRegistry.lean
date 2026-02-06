import Lean
import LeanDag.DataFlow.Rule

/-!
# Data Flow Rule Registry

This module provides a global registry for data flow decomposition rules.
Rules can be registered at module initialization time using `initialize`.

## Usage

To register a custom rule:
```lean
import LeanDag.DataFlow

def myRule : LeanDag.DataFlow.Rule where
  name := `MyProject.myRule
  priority := 85
  primaryKind := .binding `x
  appliesTo e := e.isAppOf ``myFunction
  decompose e lctx := do
    return some { nodes := #[...], children := some #[...] }

initialize LeanDag.DataFlow.registerRule myRule
```
-/

open Lean Meta

namespace LeanDag.DataFlow

/-! ## Global Rule Registry -/

/-- Global registry of decomposition rules, stored sorted by priority (highest first). -/
initialize rulesRef : IO.Ref (Array Rule) ← IO.mkRef #[]

/-- Insert a rule maintaining priority order (highest first). -/
def insertSorted (rules : Array Rule) (rule : Rule) : Array Rule :=
  let idx := rules.findIdx? fun r => r.priority < rule.priority
  match idx with
  | some i =>
    let (before, after) := rules.toList.splitAt i
    (before ++ [rule] ++ after).toArray
  | none => rules.push rule

/-! ## Rule Access API -/

/-- Get all registered rules, sorted by priority (highest first). -/
def getRules : IO (Array Rule) :=
  rulesRef.get

/-- Find the first matching rule for an expression. -/
def findRule (e : Expr) : MetaM (Option Rule) :=
  (·.find? fun r => r.appliesTo e) <$> getRules

/-- Find all matching rules for an expression (for debugging). -/
def findAllRules (e : Expr) : MetaM (Array Rule) :=
  (·.filter fun r => r.appliesTo e) <$> getRules

/-- Register a rule. Can be called from `initialize` blocks. -/
def registerRule (rule : Rule) : IO Unit :=
  rulesRef.modify (insertSorted · rule)

/-- Check if any registered rule applies to an expression.
    Handles mdata unwrapping before checking rules.
    Pure function that takes rules array explicitly. -/
def anyRuleApplies (rules : Array Rule) (e : Expr) : Bool :=
  let e := unwrapMdata e
  rules.any fun r => r.appliesTo e

end LeanDag.DataFlow
