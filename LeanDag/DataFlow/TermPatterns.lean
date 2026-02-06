import Lean
import LeanDag.DataFlow.RuleRegistry
import LeanDag.NameUtils


open Lean Meta

namespace LeanDag.DataFlow.TermPatterns

-- Use unwrapMdata from LeanDag.DataFlow (Types.lean)
open LeanDag.DataFlow (unwrapMdata)


/-- Check if expression is an if-then-else (application of ite or dite). -/
def isIfThenElse (e : Expr) : Bool :=
  match (unwrapMdata e).getAppFn with
  | .const name _ => name == ``ite || name == ``dite
  | _ => false

/-- Extract condition and branches from ite/dite expression.
    Returns (condition, thenBranch, elseBranch) if it's an if-then-else. -/
def getIfThenElseBranches (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``ite then
      -- ite : {α : Sort u} → (c : Prop) → [Decidable c] → α → α → α
      -- args: [α, c, inst, thenBranch, elseBranch]
      if args.size >= 5 then
        some (args[1]!, args[3]!, args[4]!)
      else none
    else if name == ``dite then
      -- dite : {α : Sort u} → (c : Prop) → [Decidable c] → (c → α) → (¬c → α) → α
      -- args: [α, c, inst, thenFn, elseFn]
      if args.size >= 5 then
        some (args[1]!, args[3]!, args[4]!)
      else none
    else none
  | _ => none

/-- Check if expression is a match/casesOn expression.
    Matches casesOn, recOn, and match_* auxiliary definitions. -/
def isMatchExpr (e : Expr) : Bool :=
  match (unwrapMdata e).getAppFn with
  | .const name _ =>
    match name with
    | .str _ s =>
      s == "casesOn" || s == "recOn" || s.startsWith "match_"
    | _ => false
  | _ => false

/-- Check if lambda is elaboration-generated (wraps a match with synthetic name).
    Pattern-match syntax elaborates to `fun x_n => match x_n with ...`.
    This lambda is not user-written and should be skipped. -/
def isElaborationLambda (e : Expr) : Bool :=
  match e with
  | .lam name _ body _ =>
    name.toString.isSyntheticParamName && isMatchExpr (unwrapMdata body)
  | _ => false

/-- Get the scrutinee from a match expression. -/
def getMatchScrutinee (e : Expr) : Option Expr :=
  let e := unwrapMdata e
  let args := e.getAppArgs
  -- The scrutinee is typically the first non-motive argument
  if args.size >= 2 then some args[1]! else none

/-- Get match arms from a match expression.
    Returns the lambda expressions representing each arm. -/
def getMatchArms (e : Expr) : Array Expr :=
  let e := unwrapMdata e
  let args := e.getAppArgs
  -- Arms start after motive and scrutinee (typically index 2+)
  if args.size > 2 then
    args.extract 2 args.size
  else #[]

/-- Check if expression is a boolean AND (&&) or logical And. -/
def isConjunction (e : Expr) : Bool :=
  match (unwrapMdata e).getAppFn with
  | .const name _ => name == ``And || name == ``Bool.and || name == ``and
  | _ => false

/-- Extract the two sides of a conjunction.
    Returns (left, right) if it's a conjunction. -/
def getConjunctionParts (e : Expr) : Option (Expr × Expr) :=
  let e := unwrapMdata e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const name _ =>
    if name == ``And then
      if args.size >= 2 then some (args[0]!, args[1]!) else none
    else if name == ``Bool.and || name == ``and then
      if args.size >= 2 then some (args[0]!, args[1]!) else none
    else none
  | _ => none

/-- Flatten nested conjunctions into a list of atomic conditions.
    E.g., (a && b && c) becomes [a, b, c]. -/
partial def flattenConjunction (e : Expr) : List Expr :=
  match getConjunctionParts e with
  | some (left, right) => flattenConjunction left ++ flattenConjunction right
  | none => [e]

/-- Extract the actual boolean expression from an ite condition.
    For Bool conditions: ite uses `@Eq Bool boolExpr true` as the Prop,
    so we extract the actual Bool expression. -/
def extractBoolCondition (cond : Expr) : Expr :=
  let cond := unwrapMdata cond
  let fn := cond.getAppFn
  let args := cond.getAppArgs
  match fn with
  | .const name _ =>
    -- Eq args: [type, left, right] -> we want left (the Bool expr)
    if name == ``Eq && args.size >= 2 then args[1]!
    else cond
  | _ => cond

/-! ## Built-in Rules -/

/-- Rule for let bindings: `let x := v; body` -/
def letRule : Rule where
  name := `LeanDag.DataFlow.TermPatterns.let
  priority := 100
  primaryKind := .binding `x  -- Placeholder name, actual name comes from decompose
  appliesTo e := e.isLet
  decompose e _ := do
    match e with
    | .letE name _ value body _ =>
      let nodes := #[{ kind := .binding name, expr := value : ProtoNode }]
      return some { nodes, children := some #[body] }
    | _ => return none

/-- Rule for lambda abstractions: `fun x => body`
    Skips elaboration-generated lambdas that wrap match expressions. -/
def lambdaRule : Rule where
  name := `LeanDag.DataFlow.TermPatterns.lambda
  priority := 100
  primaryKind := .lambda `x  -- Placeholder name, actual name comes from decompose
  appliesTo e := e.isLambda && !isElaborationLambda e
  decompose e _ := do
    match e with
    | .lam name _ body _ =>
      let nodes := #[{ kind := .lambda name, expr := e : ProtoNode }]
      return some { nodes, children := some #[body] }
    | _ => return none

/-- Rule for if-then-else expressions. -/
def ifThenElseRule : Rule where
  name := `LeanDag.DataFlow.TermPatterns.ifThenElse
  priority := 90
  primaryKind := .condition
  appliesTo := isIfThenElse
  decompose e _ := do
    match getIfThenElseBranches e with
    | some (cond, thenBr, elseBr) =>
      -- Extract the boolean condition and flatten conjunctions
      let boolCond := extractBoolCondition cond
      let condParts := flattenConjunction boolCond

      -- Create condition part nodes
      let condNodes : Array ProtoNode := condParts.toArray.mapIdx fun i part =>
        { kind := .conditionPart i, expr := part }

      -- Main condition node
      let condNode : ProtoNode := { kind := .condition, expr := cond }

      -- Branch nodes
      let thenNode : ProtoNode := { kind := .branch "then", expr := thenBr }
      let elseNode : ProtoNode := { kind := .branch "else", expr := elseBr }

      let allNodes := condNodes ++ #[condNode, thenNode, elseNode]
      return some { nodes := allNodes, children := some #[thenBr, elseBr] }
    | none => return none

/-- Rule for boolean conjunction (&&).
    Only applies when used as a standalone expression, not inside if-then-else condition.
    Lower priority than ifThenElse to avoid double-processing conditions. -/
def conjunctionRule : Rule where
  name := `LeanDag.DataFlow.TermPatterns.conjunction
  priority := 80  -- Lower than ifThenElse
  primaryKind := .conditionPart 0
  appliesTo e := isConjunction e && !isIfThenElse e
  decompose e _ := do
    let parts := flattenConjunction e
    let nodes : Array ProtoNode := parts.toArray.mapIdx fun i part =>
      { kind := .conditionPart i, expr := part }
    return some { nodes, children := some #[] }  -- No further recursion into parts

/-- Rule for match expressions. -/
def matchRule : Rule where
  name := `LeanDag.DataFlow.TermPatterns.match
  priority := 90
  primaryKind := .matchScrutinee
  appliesTo := isMatchExpr
  decompose e _ := do
    let scrutinee := getMatchScrutinee e
    let arms := getMatchArms e

    let mut nodes : Array ProtoNode := #[]

    -- Add scrutinee node
    if let some scrut := scrutinee then
      nodes := nodes.push { kind := .matchScrutinee, expr := scrut }

    -- Add arm nodes (each arm is typically a lambda)
    for h : i in [:arms.size] do
      let arm := arms[i]
      let label := s!"arm {i + 1}"
      nodes := nodes.push { kind := .branch label, expr := arm }

    return some { nodes, children := some arms }

/-! ## Rule Registration -/

/-- Register all built-in decomposition rules at module load time. -/
initialize do
  for rule in #[letRule, lambdaRule, ifThenElseRule, conjunctionRule, matchRule] do
    registerRule rule

end LeanDag.DataFlow.TermPatterns
