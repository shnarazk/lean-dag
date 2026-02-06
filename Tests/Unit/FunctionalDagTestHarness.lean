import Lean
import Lean.Elab.Frontend
import LeanDag
import Tests.Harness

namespace Tests.Unit.FunctionalDagTestHarness

open Lean Elab Command Meta LeanDag LeanDag.DataFlow.Builder Tests.Harness

/-! ## Test Harness for FunctionalDagBuilder

This module provides infrastructure to elaborate Lean code and run the
FunctionalDagBuilder's `isSignificantTerm` check against real elaborated expressions.
-/

/-- Result of elaborating test code with InfoTree. -/
structure ElaborationResult where
  env : Environment
  messages : MessageLog
  infoTrees : PersistentArray InfoTree
  fileMap : FileMap

/-- Elaborate Lean source code and return the result with InfoTrees.
    The code should include its own imports (e.g., "import Init"). -/
def elaborateCode (code : String) (fileName : String := "<test>") : IO ElaborationResult := do
  -- Initialize search path from LEAN_PATH environment variable
  Lean.initSearchPath (← Lean.findSysroot)

  -- Create input context
  let inputCtx := Parser.mkInputContext code fileName

  -- Parse the header (import statements) from the code
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  -- Process the header to create the environment with all imports
  let (env, messages) ← processHeader header {} messages inputCtx

  -- Run the frontend to elaborate the rest of the code
  let state ← Lean.Elab.IO.processCommands inputCtx parserState (Command.mkState env messages {})

  return {
    env := state.commandState.env
    messages := state.commandState.messages
    infoTrees := state.commandState.infoState.trees
    fileMap := inputCtx.fileMap
  }

/-- Check if elaboration succeeded (no errors). -/
def elaborationSucceeded (result : ElaborationResult) : Bool :=
  !result.messages.hasErrors

/-- Get error messages from elaboration. -/
def getErrors (result : ElaborationResult) : IO (List String) := do
  let errMsgs := result.messages.toList.filter (·.severity == .error)
  errMsgs.mapM fun msg => do
    let text ← msg.data.toString
    pure s!"[line {msg.pos.line}, col {msg.pos.column}] {text}"

/-! ## InfoTree Analysis -/

/-- Check if this is a significant term (matches FunctionalDagBuilder.isSignificantTerm). -/
def isSignificantTerm (expr : Expr) : Bool :=
  match expr with
  | .letE .. => true
  | .lam .. => true
  | .mdata _ (.letE ..) => true
  | .mdata _ (.lam ..) => true
  | _ => false

/-- A captured term from InfoTree. -/
structure CapturedTerm where
  expr : Expr
  exprKind : String
  position : Option String.Pos.Raw
  deriving Inhabited

/-- Get the kind of an expression as a string. -/
def exprKindStr : Expr → String
  | .bvar _ => "bvar"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"
  | .mdata _ e => s!"mdata({exprKindStr e})"
  | .proj _ _ _ => "proj"

/-- Collect all TermInfo nodes from an InfoTree. -/
def collectTermInfos (tree : InfoTree) : List (Elab.TermInfo × Option String.Pos.Raw) :=
  tree.foldInfo (init := []) fun _ctx info acc =>
    match info with
    | .ofTermInfo termInfo =>
      let pos := info.pos?
      (termInfo, pos) :: acc
    | _ => acc

/-- Collect significant terms (those that would be captured by FunctionalDagBuilder). -/
def collectSignificantTerms (tree : InfoTree) : List CapturedTerm :=
  let termInfos := collectTermInfos tree
  termInfos.filterMap fun (termInfo, pos) =>
    if isSignificantTerm termInfo.expr then
      some { expr := termInfo.expr, exprKind := exprKindStr termInfo.expr, position := pos }
    else
      none

/-- Count significant terms across all InfoTrees. -/
def countSignificantTerms (result : ElaborationResult) : Nat :=
  result.infoTrees.toList.map collectSignificantTerms |>.flatten.length

/-- Get expression kinds of significant terms only. -/
def getSignificantExprKinds (result : ElaborationResult) : List String :=
  result.infoTrees.toList.map collectSignificantTerms |>.flatten.map (·.exprKind)

/-! ## isTermModeTree Check -/

/-- Get tactic syntax kinds for debugging. -/
def getTacticKinds (tree : InfoTree) : List String :=
  tree.foldInfo (init := []) fun _ info acc =>
    match info with
    | .ofTacticInfo ti =>
      let kind := match ti.stx with
        | .node _ k _ => k.toString
        | .atom _ v => s!"atom:{v}"
        | _ => "other"
      kind :: acc
    | _ => acc

/-- Count TermInfo nodes in a tree. -/
def countTermInfo (tree : InfoTree) : Nat :=
  tree.foldInfo (init := 0) fun _ info acc =>
    match info with
    | .ofTermInfo _ => acc + 1
    | _ => acc

/-- Debug dump of InfoTree contents. -/
def debugInfoTree (tree : InfoTree) (idx : Nat) : IO Unit := do
  let termCount := countTermInfo tree
  let tacticKinds := getTacticKinds tree
  let passesFilter := isTermModeTree tree
  IO.println s!"  Tree {idx}: terms={termCount}, tactics={tacticKinds.length}, isTermMode={passesFilter}"
  if !tacticKinds.isEmpty then
    IO.println s!"    tactic kinds: {tacticKinds.take 10}"

/-! ## Test Assertions -/

/-- Assert that code elaborates without errors. -/
def assertElaborates (code : String) : IO ElaborationResult := do
  let result ← elaborateCode code
  if elaborationSucceeded result then
    IO.println "  ✓ code elaborates successfully"
    return result
  else
    let errors ← getErrors result
    IO.println s!"  ✗ elaboration failed with {errors.length} error(s):"
    for err in errors do
      IO.println s!"    {err}"
    throw <| IO.userError "Elaboration failed"

/-- Assert that at least N significant terms are captured. -/
def assertAtLeastSignificantTerms (result : ElaborationResult) (minExpected : Nat) : IO Unit := do
  let actual := countSignificantTerms result
  if actual >= minExpected then
    IO.println s!"  ✓ captured {actual} significant term(s) (>= {minExpected})"
  else
    IO.println s!"  ✗ expected at least {minExpected} significant terms, got {actual}"
    IO.println s!"    significant kinds: {getSignificantExprKinds result}"
    throw <| IO.userError s!"Expected at least {minExpected} significant terms, got {actual}"

/-- Assert that at least one InfoTree with TermInfo passes isTermModeTree. -/
def assertIsTermModeTree (result : ElaborationResult) : IO Unit := do
  let mut definitionTreePasses := false
  for tree in result.infoTrees.toList do
    let termCount := countTermInfo tree
    let passes := isTermModeTree tree
    if termCount > 0 then
      if passes then
        IO.println s!"  ✓ Definition tree: isTermModeTree=true ({termCount} terms)"
        definitionTreePasses := true
      else
        let tacticKinds := getTacticKinds tree
        IO.println s!"  ✗ Definition tree: isTermModeTree=false ({termCount} terms)"
        IO.println s!"    BUG: Should be true! Tactic kinds: {tacticKinds}"
        throw <| IO.userError "isTermModeTree bug: returned false for definition with TermInfo"
  if !definitionTreePasses then
    throw <| IO.userError "No definition tree found with TermInfo"

end Tests.Unit.FunctionalDagTestHarness
