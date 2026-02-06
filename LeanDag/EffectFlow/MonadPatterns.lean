import Lean
import LeanDag.EffectFlow.RuleRegistry
import LeanDag.NameUtils

/-!
# Built-in Effect Rules

This module provides built-in effect rules for common monadic patterns:
- StateM/StateT: get, set, modify
- Except/ExceptT: throw, tryCatch
- Monad: bind (>>= and do-notation)
- Pure: pure/return
-/

open Lean Meta
open LeanDag.EffectFlow

namespace LeanDag.EffectFlow

/-! ## Helper Functions -/

/-- Unwrap mdata wrappers from an expression. -/
def unwrapMdata : Expr → Expr
  | .mdata _ inner => unwrapMdata inner
  | e => e

/-- Check if expression is a monadic bind operation. -/
def isMonadBind (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``Bind.bind ||
    name.toString.endsWith ".bind"
  | _ => false

/-- Check if expression is a state get operation. -/
def isStateGet (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``StateT.get ||
    name == ``MonadState.get ||
    name == ``getThe ||
    name.toString.endsWith ".get"
  | _ => false

/-- Check if expression is a state set/put operation. -/
def isStatePut (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``StateT.set ||
    name == ``MonadState.set ||
    name == ``set ||
    name.toString.endsWith ".set" ||
    name.toString.endsWith ".put"
  | _ => false

/-- Check if expression is a state modify operation. -/
def isStateModify (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``StateT.modifyGet ||
    name == ``modify ||
    name == ``modifyGet ||
    name.toString.endsWith ".modify"
  | _ => false

/-- Check if expression is a throw/error operation. -/
def isThrow (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``throw ||
    name == ``Except.error ||
    name == ``throwThe ||
    name.toString.endsWith ".throw"
  | _ => false

/-- Check if expression is a catch/tryCatch operation. -/
def isCatch (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``tryCatch ||
    name == ``MonadExcept.tryCatch ||
    name == ``Except.tryCatch ||
    name.toString.endsWith ".tryCatch" ||
    name.toString.endsWith ".catch"
  | _ => false

/-- Check if expression is a pure/return operation. -/
def isPure (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``Pure.pure ||
    name == ``Except.ok ||
    name.toString.endsWith ".pure"
  | _ => false

/-- Check if expression is an if-then-else operation. -/
def isIfThenElse (e : Expr) : Bool :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  match fn with
  | .const name _ =>
    name == ``ite ||
    name == ``dite ||
    name == ``cond ||
    name.toString.endsWith ".ite" ||
    name.toString.endsWith ".dite"
  | _ => false

/-! ## Built-in Rules

These rules implement return/effect decomposition for monadic operations:
- Return: what the operation produces as its result
- Effect (GivenBack): what state changes are given back to the environment
-/

/-- Rule for state get operations: `get` / `StateT.get`

    - Return: the current state s
    - Effect: identity (read-only, nothing given back)
-/
def stateGetRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.stateGet
  priority := 100
  appliesTo := isStateGet
  analyze _ _ := do
    return some {
      kind := "stateRead"
      stateEffect := .read
      forwardDesc := "λs. (s, s)"
      backwardDesc := "identity"
    }

/-- Rule for state set operations: `set v` / `StateT.set v`

    - Return: () (unit)
    - Effect: the new state value v (given back)
-/
def statePutRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.statePut
  priority := 100
  appliesTo := isStatePut
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    let valueExpr := if args.size > 0 then some args[args.size - 1]! else none
    return some {
      kind := "stateWrite"
      stateEffect := .write
      forwardOutput := none
      givenBack := valueExpr
      forwardDesc := "λs. ((), v)"
      backwardDesc := "v"
    }

/-- Rule for state modify operations: `modify f`

    - Return: () (unit)
    - Effect: f (the modifier function that transforms state)
-/
def stateModifyRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.stateModify
  priority := 100
  appliesTo := isStateModify
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    let fExpr := if args.size > 0 then some args[args.size - 1]! else none
    return some {
      kind := "stateModify"
      stateEffect := .modify
      forwardOutput := none
      givenBack := fExpr
      forwardDesc := "λs. ((), f s)"
      backwardDesc := "f"
    }

/-- Rule for monadic bind: `ma >>= f` or `do x ← ma; ...`

    - Return: sequences the return values of sub-operations
    - Effect: composes state effects in reverse order
-/
def monadBindRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.bind
  priority := 90
  appliesTo := isMonadBind
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    if args.size < 2 then return none

    let ma := args[args.size - 2]!
    let f := args[args.size - 1]!

    -- Try to extract binding name from lambda, filtering out hygienic names
    let bindingLabel := match f with
      | .lam name _ _ _ =>
        let s := name.eraseMacroScopes.toString
        if s.isUserVisible && !s.isSyntheticParamName then some s else none
      | _ => none

    return some {
      kind := "effectBind"
      stateEffect := .none
      children := #[
        (ma, "data_flow", none),
        (f, "continuation", bindingLabel)
      ]
      displayExpr := some ma
      forwardOutput := some ma
      givenBack := none
      forwardDesc := ""
      backwardDesc := ""
    }

/-- Rule for throw/error: `throw e`

    - Return: Err e (error case)
    - Effect: ⊥ (bottom - unreachable, no value given back on error path)
-/
def throwRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.throw
  priority := 100
  appliesTo := isThrow
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    let errExpr := if args.size > 0 then some args[args.size - 1]! else none
    return some {
      kind := "effectThrow"
      stateEffect := .error
      forwardOutput := errExpr
      givenBack := none
      forwardDesc := "λs. Err e"
      backwardDesc := "⊥"
    }

/-- Rule for catch/tryCatch: `tryCatch ma handler`

    - Return: tries ma, on error applies handler
    - Effect: combines state effects based on execution path
-/
def catchRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.catch
  priority := 100
  appliesTo := isCatch
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    if args.size < 2 then return none

    let ma := args[args.size - 2]!
    let handler := args[args.size - 1]!

    return some {
      kind := "effectCatch"
      stateEffect := .none
      children := #[
        (ma, "control_flow", some "try"),
        (handler, "error_propagation", some "catch")
      ]
      forwardDesc := "match fwd_ma with Ok x => x | Err e => fwd_h e"
      backwardDesc := "match path with Ok => bwd_ma | Err => bwd_h"
    }

/-- Rule for pure/return: `pure a`

    - Return: the value a wrapped in Ok
    - Effect: identity (pure has no effects)
-/
def pureRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.pure
  priority := 80  -- Lower priority so bind matches first
  appliesTo := isPure
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    let valueExpr := if args.size > 0 then some args[args.size - 1]! else none
    return some {
      kind := "effectReturn"
      stateEffect := .none
      forwardOutput := valueExpr
      givenBack := none
      forwardDesc := "λs. (Ok v, s)"
      backwardDesc := "identity"
    }

/-- Rule for if-then-else: `if cond then thenBranch else elseBranch`

    Creates control flow edges to both branches so they get analyzed.
-/
def ifThenElseRule : EffectRule where
  name := `LeanDag.EffectFlow.MonadPatterns.ifThenElse
  priority := 95  -- Higher than bind (90) but lower than state ops (100)
  appliesTo := isIfThenElse
  analyze e _ := do
    let e := unwrapMdata e
    let args := e.getAppArgs
    if args.size < 3 then return none
    let thenBranch := args[args.size - 2]!
    let elseBranch := args[args.size - 1]!

    return some {
      kind := "effectBranch"
      stateEffect := .none
      children := #[
        (thenBranch, "control_flow", some "then"),
        (elseBranch, "control_flow", some "else")
      ]
      forwardDesc := "if cond then ... else ..."
      backwardDesc := ""
    }

/-! ## Rule Registration -/

/-- Register all built-in effect rules at module load time. -/
initialize do
  for rule in #[stateGetRule, statePutRule, stateModifyRule, monadBindRule, ifThenElseRule, throwRule, catchRule, pureRule] do
    registerRule rule

end LeanDag.EffectFlow
