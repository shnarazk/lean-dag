module

public import Lean
public import LeanDag.EffectFlow.Types

@[expose] public section

/-!
# Effect Flow Rule Registry

This module provides a global registry for effect flow analysis rules.
Rules can be registered at module initialization time using `initialize`.

## Usage

To register a custom rule:
```lean
import LeanDag.EffectFlow

def myRule : LeanDag.EffectFlow.EffectRule where
  name := `MyProject.myRule
  priority := 85
  appliesTo e := e.isAppOf ``myMonadOp
  analyze e lctx := do
    return some { kind := "custom", forwardDesc := "...", backwardDesc := "..." }

initialize LeanDag.EffectFlow.registerRule myRule
```
-/

open Lean Meta

namespace LeanDag.EffectFlow

/-! ## Global Rule Registry -/

/-- Global registry of effect rules, stored sorted by priority (highest first). -/
initialize rulesRef : IO.Ref (Array EffectRule) ← IO.mkRef #[]

/-- Insert a rule maintaining priority order (highest first). -/
def insertSorted (rules : Array EffectRule) (rule : EffectRule) : Array EffectRule :=
  let idx := rules.findIdx? fun r => r.priority < rule.priority
  match idx with
  | some i =>
    let (before, after) := rules.toList.splitAt i
    (before ++ [rule] ++ after).toArray
  | none => rules.push rule

/-! ## Rule Access API -/

/-- Get all registered rules, sorted by priority (highest first). -/
def getRules : IO (Array EffectRule) :=
  rulesRef.get

/-- Find the first matching rule for an expression. -/
def findRule (e : Expr) : MetaM (Option EffectRule) :=
  (·.find? fun r => r.appliesTo e) <$> getRules

/-- Check if any registered rule applies to an expression. -/
def hasMatchingRule (e : Expr) : IO Bool :=
  (·.any fun r => r.appliesTo e) <$> getRules

/-- Register a rule. Can be called from `initialize` blocks. -/
def registerRule (rule : EffectRule) : IO Unit :=
  rulesRef.modify (insertSorted · rule)

end LeanDag.EffectFlow
