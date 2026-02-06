module

public import Lean
public import Lean.Meta.Basic
public import Lean.Meta.CollectMVars
public import LeanDag.Protocol
public import LeanDag.SearchExpression
public import LeanDag.SemanticTableau.Types
public import LeanDag.NameUtils

@[expose] public section

open Lean Elab Server Lean.Elab
open LeanDag.SearchExpression (BinderCache NavigationContext buildBinderCache ppExprStr)

namespace LeanDag.SemanticTableau.InfoTreeParser

/-! ## Tactic Substring Extraction -/

def getTacticSubstring (tInfo : Elab.TacticInfo) : Option Substring.Raw :=
  tInfo.stx.getSubstring?.join

/-! ## Goals At Position -/

partial def goalsAt? (t : InfoTree) (text : FileMap) (hoverPos : String.Pos.Raw) : List GoalsAtResult :=
  let gs := t.collectNodesBottomUp fun ctx i cs gs => Id.run do
    let .ofTacticInfo ti := i | return gs
    let some pos := i.pos? | return gs
    let some tailPos := i.tailPos? | return gs
    let trailSize := i.stx.getTrailingSize
    let atEOF := tailPos.byteIdx + trailSize == text.source.rawEndPos.byteIdx
    unless pos ≤ hoverPos ∧ (hoverPos.byteIdx < tailPos.byteIdx + max 1 trailSize || atEOF) do return gs
    let isClosingBracket := ti.stx.getAtomVal == "]"
    unless (gs.isEmpty || (hoverPos ≥ tailPos && gs.all (·.indented))) && !isClosingBracket do return gs
    return [{
      ctxInfo := ctx
      tacticInfo := ti
      useAfter := hoverPos > pos && !cs.any (hasNestedTactic pos tailPos)
      indented := (text.toPosition pos).column > (text.toPosition hoverPos).column && !isEmptyBy ti.stx
      priority := if hoverPos.byteIdx == tailPos.byteIdx + trailSize then 0 else 1
    }]
  let maxPrio? := gs.map (·.priority) |>.max?
  gs.filter (some ·.priority == maxPrio?)
where
  hasNestedTactic (pos tailPos) : InfoTree → Bool
    | .node i@(.ofTacticInfo _) cs => Id.run do
      if let `(by $_) := i.stx then return false
      let some pos' := i.pos? | return cs.any (hasNestedTactic pos tailPos)
      let some tailPos' := i.tailPos? | return cs.any (hasNestedTactic pos tailPos)
      if tailPos' > hoverPos && (pos', tailPos') != (pos, tailPos) then return true
      cs.any (hasNestedTactic pos tailPos)
    | .node (.ofMacroExpansionInfo _) cs => cs.any (hasNestedTactic pos tailPos)
    | _ => false
  isEmptyBy (stx : Syntax) : Bool :=
    stx.getNumArgs == 2 && stx[0].isToken "by" && stx[1].getNumArgs == 1 && stx[1][0].isMissing

/-! ## Theorem Extraction (only for single_tactic mode) -/

structure ArgumentInfo where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

structure TheoremSignature where
  name            : String
  instanceArgs    : List ArgumentInfo := []
  implicitArgs    : List ArgumentInfo := []
  explicitArgs    : List ArgumentInfo := []
  type            : String := ""
  declarationType : String := ""
  body            : Option String := none
  deriving Inhabited, FromJson, ToJson

def extractArgsWithTypes (expr : Expr) : MetaM (List ArgumentInfo × List ArgumentInfo × List ArgumentInfo × String) := do
  Meta.forallTelescope expr fun args body => do
    let mut lctx := LocalContext.empty
    for arg in args do
      lctx := lctx.addDecl (← arg.fvarId!.getDecl)
    let ppCtx : PPContext := {
      env := ← getEnv, mctx := ← getMCtx, lctx
      opts := (← getOptions).setBool `pp.fullNames true
    }
    let mut instanceArgs := []
    let mut implicitArgs := []
    let mut explicitArgs := []
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      let typeStr ← ppExprStr ppCtx decl.type
      let argInfo : ArgumentInfo := { name := decl.userName.toString, type := typeStr }
      match decl.binderInfo with
      | .instImplicit => instanceArgs := instanceArgs ++ [argInfo]
      | .implicit | .strictImplicit => implicitArgs := implicitArgs ++ [argInfo]
      | .default => explicitArgs := explicitArgs ++ [argInfo]
    let bodyStr ← ppExprStr ppCtx body
    return (instanceArgs, implicitArgs, explicitArgs, bodyStr)

def declarationKind : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def formatDeclaration (name : Name) (ctx : ContextInfo) (goalDecl : MetavarDecl) : MetaM (Option TheoremSignature) := do
  let constInfo ← getConstInfo name
  let declType := declarationKind constInfo
  unless declType ∈ ["theorem", "axiom", "def"] do return none
  let sanitizedLctx := goalDecl.lctx.sanitizeNames.run' {options := {}}
  let ppCtx := { ctx.toPPContext sanitizedLctx with
    opts := (ctx.toPPContext goalDecl.lctx).opts.setBool `pp.fullNames true }
  let nameStr ← ppExprStr ppCtx (mkConst constInfo.name)
  let (instanceArgs, implicitArgs, explicitArgs, typeStr) ← extractArgsWithTypes constInfo.type
  let declBody ← match declType, constInfo.value? with
    | "def", some expr => some <$> ppExprStr ppCtx expr
    | _, _ => pure none
  return some { name := nameStr, instanceArgs, implicitArgs, explicitArgs, type := typeStr, declarationType := declType, body := declBody }

def extractConstName (expr : Expr) (lctx : LocalContext) : Option Name := do
  guard (!expr.isSyntheticSorry)
  let cleanExpr := expr.consumeMData
  match cleanExpr with
  | .const name _ => name
  | .app .. => expr.getAppFn.consumeMData.constName?
  | .fvar .. =>
    let ldecl ← lctx.findFVar? cleanExpr
    let val ← ldecl.value?
    val.getAppFn.consumeMData.constName?
  | _ => none

def getTheorems (infoTree : InfoTree) (tacticInfo : Elab.TacticInfo) (ctx : ContextInfo) : RequestM (List TheoremSignature) := do
  let some goalDecl := ctx.mctx.findDecl? tacticInfo.goalsBefore.head!
    | throwThe RequestError ⟨.invalidParams, "noGoalDecl"⟩
  let some sub := getTacticSubstring tacticInfo
    | throwThe RequestError ⟨.invalidParams, "noTacticSubstring"⟩
  ctx.runMetaM goalDecl.lctx do
    let mut theoremNames : NameSet := {}
    let mut pos := sub.startPos
    while pos < sub.stopPos do
      if let some info ← infoTree.hoverableInfoAtM? pos then
        if let .ofTermInfo termInfo := info.info then
          if let some name := extractConstName termInfo.expr termInfo.lctx then
            theoremNames := theoremNames.insert name
      pos := ⟨pos.byteIdx + 3⟩
    theoremNames.toList.filterMapM fun name => do
      formatDeclaration (← resolveGlobalConstNoOverloadCore name) ctx goalDecl

/-! ## Parsed Proof Types

These types use the protocol types directly (ProofObligation, ProofContextHypothesis)
but add MVarId for tracking goal identity during parsing.
-/

/-- A goal with its MVarId for tracking during parsing. -/
structure ParsedGoal where
  obligation : LeanDag.ProofObligation
  hypotheses : List LeanDag.ProofContextHypothesis
  mvarId : MVarId
  deriving Inhabited

instance : BEq ParsedGoal where beq g1 g2 := g1.mvarId == g2.mvarId
instance : Hashable ParsedGoal where hash g := hash g.mvarId

structure SourceRange where
  start : Lsp.Position
  stop  : Lsp.Position
  deriving Inhabited, ToJson, FromJson

structure ParsedStep where
  tacticString            : String
  goalBefore              : ParsedGoal
  goalsAfter              : List ParsedGoal
  hypothesisDependencies  : List String
  spawnedGoals            : List ParsedGoal
  position                : SourceRange
  theorems                : List TheoremSignature
  deriving Inhabited

structure ParseResult where
  steps    : List ParsedStep
  allGoals : Std.HashSet ParsedGoal

/-- A single goal transformation from a tactic application. -/
structure GoalChange where
  hypothesisDependencies : List String
  goalBefore             : ParsedGoal
  goalsAfter             : List ParsedGoal
  deriving Inhabited

/-! ## Parsing Helpers -/

def findUsedHypotheses (goalId : MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId | return []
  let fullExpr ← instantiateExprMVars expr
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  return (fvarIds.filterMap goalDecl.lctx.find?).map (·.userName.toString) |>.toList

def findAssignedMVars (goalId : MVarId) (mctxAfter : MetavarContext) : MetaM (List MVarId) := do
  let some expr := mctxAfter.eAssignment.find? goalId | return []
  let (_, s) ← (Meta.collectMVars expr).run {}
  return s.result.toList




/-- Mode for parsing tactics. -/
inductive ParserMode where
  | full         -- Normal tree traversal
  | singleTactic -- Extract theorems for single tactic analysis

/-- Stable context for parsing, created once per tree traversal. -/
structure ParserContext where
  infoTree    : InfoTree
  binderCache : BinderCache
  fileUri     : String
  mode        : ParserMode := .full

def ParserContext.toNavigationContext (pctx : ParserContext) : NavigationContext :=
  { binderCache := pctx.binderCache, fileUri := pctx.fileUri }

/-- Extended parser context with FileMap for pure parsing. -/
structure ParserContextWithText extends ParserContext where
  text : FileMap

/-- Format a hypothesis directly to ProofContextHypothesis. -/
def formatHypothesis (ppCtx : PPContext) (hypDecl : LocalDecl) (nav : NavigationContext)
    : IO LeanDag.ProofContextHypothesis := do
  let typeStr ← ppExprStr ppCtx hypDecl.type
  let valueStr ← hypDecl.value?.mapM fun v => ppExprStr ppCtx v
  let navigationLocations : Option LeanDag.PreresolvedNavigationTargets := match nav.binderCache.get? hypDecl.fvarId with
    | some pos => some { definition := some { uri := nav.fileUri, position := pos } }
    | none => none
  return {
    name := hypDecl.userName.toString.filterName
    type := LeanDag.AnnotatedTextTree.plain typeStr
    value := valueStr.map LeanDag.AnnotatedTextTree.plain
    id := hypDecl.fvarId.name.toString
    isProofTerm := hypDecl.type.isProp
    isTypeclassInstance := false
    navigationLocations
  }

/-- Format goal directly to ParsedGoal with ProofObligation. Pure version. -/
def formatGoalPure (ctx : ContextInfo) (id : MVarId) (nav : NavigationContext)
    : IO (Option ParsedGoal) := do
  let some decl := ctx.mctx.findDecl? id | return none
  let lctx := decl.lctx.sanitizeNames.run' {options := {}}
  let ppCtx := ctx.toPPContext lctx
  let hyps ← lctx.foldrM (init := []) fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then return acc
    let hyp ← formatHypothesis ppCtx hypDecl nav
    return hyp :: acc
  let typeStr ← ppExprStr ppCtx decl.type
  let obligation : LeanDag.ProofObligation := {
    type := LeanDag.AnnotatedTextTree.plain typeStr
    username := decl.userName.toString.filterNameOpt
    id := id.name.toString
    navigationLocations := none
  }
  return some { obligation, hypotheses := hyps, mvarId := id }

/-- Format goal directly to ParsedGoal with ProofObligation. -/
def formatGoal (ctx : ContextInfo) (id : MVarId) (nav : NavigationContext)
    : RequestM ParsedGoal := do
  let some result ← formatGoalPure ctx id nav
    | throwThe RequestError ⟨.invalidParams, "goalNotFoundInMctx"⟩
  return result

def filterUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : List MVarId :=
  goals.filter fun id =>
    (mctx.findDecl? id).isSome && !mctx.eAssignment.contains id && !mctx.dAssignment.contains id

/-- Pure version of computeGoalChanges that uses IO instead of RequestM. -/
def computeGoalChangesPure (pctx : ParserContext) (ctx : ContextInfo) (tInfo : Elab.TacticInfo)
    : IO (List GoalChange) := do
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  let ppCtx := { ctx with mctx := tInfo.mctxAfter }
  let goalsBefore := filterUnassignedGoals goalMVars tInfo.mctxBefore
  let goalsAfter := filterUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter goalsAfter.contains
  let uniqueBefore := goalsBefore.filter (!commonGoals.contains ·)
  let uniqueAfter := goalsAfter.filter (!commonGoals.contains ·)
  uniqueBefore.filterMapM fun goalBefore => do
    let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore | return none
    let (assignedMVars, hypothesisDependencies) ← ctx.runMetaM goalDecl.lctx do
      let assignedMVars ← findAssignedMVars goalBefore tInfo.mctxAfter
      let hypothesisDependencies ← findUsedHypotheses goalBefore goalDecl tInfo.mctxAfter
      return (assignedMVars, hypothesisDependencies)
    let nav := pctx.toNavigationContext
    let some goalBefore ← formatGoalPure ppCtx goalBefore nav | return none
    let goalsAfter ← (uniqueAfter.filter assignedMVars.contains).filterMapM fun id =>
      formatGoalPure ppCtx id nav
    return some { hypothesisDependencies, goalBefore, goalsAfter }

def computeGoalChanges (pctx : ParserContext) (ctx : ContextInfo) (tInfo : Elab.TacticInfo)
    : RequestM (List GoalChange) :=
  computeGoalChangesPure pctx ctx tInfo

def formatRewriteSteps (stx : Syntax) (steps : List ParsedStep) : List ParsedStep :=
  match stx with
  | `(tactic| rw [$args,*] $(_)?)
  | `(tactic| rewrite [$args,*] $(_)?) =>
    let rules := args.getElems.toList
    steps.zipWith (fun step rule =>
      let ruleStr := rule.raw.getSubstring?.map (·.toString.trimAscii.toString) |>.getD step.tacticString
      { step with tacticString := s!"rw [{ruleStr}]" }) rules
  | _ => steps

def compareNameNum : Name → Name → Bool
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _, _ => true
  | _, _ => false

def formatTacticString (s : String) : String :=
  (s.splitOn "\n").headD "" |>.trimAscii.toString

def getSourceRangePure (sub : Substring.Raw) (text : FileMap) : SourceRange :=
  { start := text.utf8PosToLspPos sub.startPos, stop := text.utf8PosToLspPos sub.stopPos }

def getSourceRange (sub : Substring.Raw) : RequestM SourceRange := do
  let text := (← RequestM.readDoc).meta.text
  return getSourceRangePure sub text

/-! ## Main Parser -/

/-- Pure version of parseTacticInfo that uses IO instead of RequestM.
    Note: singleTactic mode is not supported in pure version. -/
partial def parseTacticInfoPure (pctx : ParserContextWithText) (ctx : ContextInfo) (info : Info) (acc : ParseResult)
    : IO ParseResult := do
  let some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info | return acc
  let some sub := getTacticSubstring tInfo | return acc
  let tacticString := formatTacticString sub.toString
  let steps := formatRewriteSteps tInfo.stx acc.steps
  let position := getSourceRangePure sub pctx.text
  let changes ← computeGoalChangesPure pctx.toParserContext ctx tInfo
  let currentGoals := changes.flatMap fun c => c.goalBefore :: c.goalsAfter
  let allGoals := acc.allGoals.insertMany currentGoals
  let stepGoals := steps.flatMap fun s => s.goalsAfter ++ s.spawnedGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (stepGoals.foldl Std.HashSet.erase allGoals)
    |>.toArray.insertionSort (compareNameNum ·.mvarId.name ·.mvarId.name) |>.toList
  let theorems := []  -- singleTactic mode not supported in pure version
  let existingGoals := steps.map (·.goalBefore)
  let newSteps := changes.filterMap fun c =>
    if existingGoals.elem c.goalBefore then none
    else some { tacticString, goalBefore := c.goalBefore, goalsAfter := c.goalsAfter,
                hypothesisDependencies := c.hypothesisDependencies, spawnedGoals := orphanedGoals, position, theorems }
  return { steps := newSteps ++ steps, allGoals }

partial def parseTacticInfo (pctx : ParserContext) (ctx : ContextInfo) (info : Info) (acc : ParseResult)
    : RequestM ParseResult := do
  let some ctx := info.updateContext? ctx | panic! "unexpected context node"
  let .ofTacticInfo tInfo := info | return acc
  let some sub := getTacticSubstring tInfo | return acc
  let tacticString := formatTacticString sub.toString
  let steps := formatRewriteSteps tInfo.stx acc.steps
  let position ← getSourceRange sub
  let changes ← computeGoalChanges pctx ctx tInfo
  let currentGoals := changes.flatMap fun c => c.goalBefore :: c.goalsAfter
  let allGoals := acc.allGoals.insertMany currentGoals
  let stepGoals := steps.flatMap fun s => s.goalsAfter ++ s.spawnedGoals
  let orphanedGoals := currentGoals.foldl Std.HashSet.erase (stepGoals.foldl Std.HashSet.erase allGoals)
    |>.toArray.insertionSort (compareNameNum ·.mvarId.name ·.mvarId.name) |>.toList
  let theorems ← match pctx.mode with
    | .singleTactic => getTheorems pctx.infoTree tInfo ctx
    | .full => pure []
  let existingGoals := steps.map (·.goalBefore)
  let newSteps := changes.filterMap fun c =>
    if existingGoals.elem c.goalBefore then none
    else some { tacticString, goalBefore := c.goalBefore, goalsAfter := c.goalsAfter,
                hypothesisDependencies := c.hypothesisDependencies, spawnedGoals := orphanedGoals, position, theorems }
  return { steps := newSteps ++ steps, allGoals }

/-- Pure version of visitNode. -/
partial def visitNodePure (pctx : ParserContextWithText) (ctx : ContextInfo) (info : Info) (results : List (Option ParseResult))
    : IO ParseResult := do
  let results := results.filterMap id
  let steps := results.flatMap (·.steps)
  let allGoals := Std.HashSet.ofList (results.flatMap (·.allGoals.toList))
  parseTacticInfoPure pctx ctx info { steps, allGoals }

partial def visitNode (pctx : ParserContext) (ctx : ContextInfo) (info : Info) (results : List (Option ParseResult))
    : RequestM ParseResult := do
  let results := results.filterMap id
  let steps := results.flatMap (·.steps)
  let allGoals := Std.HashSet.ofList (results.flatMap (·.allGoals.toList))
  parseTacticInfo pctx ctx info { steps, allGoals }

/-- Parse InfoTree with explicit text and fileUri. Pure version for standalone use. -/
def parseInfoTreePure (infoTree : InfoTree) (text : FileMap) (fileUri : String)
    : IO (Option ParseResult) := do
  let pctx : ParserContextWithText := {
    infoTree
    binderCache := buildBinderCache infoTree text
    fileUri
    text
  }
  infoTree.visitM (postNode := fun ctx info _ results => visitNodePure pctx ctx info results)

/-- Parse InfoTree with cached binder locations for efficient goto resolution. -/
def parseInfoTree (infoTree : InfoTree) : RequestM (Option ParseResult) := do
  let doc ← RequestM.readDoc
  let text := doc.meta.text
  let pctx : ParserContext := {
    infoTree
    binderCache := buildBinderCache infoTree text
    fileUri := doc.meta.uri
  }
  infoTree.visitM (postNode := fun ctx info _ results => visitNode pctx ctx info results)

end LeanDag.SemanticTableau.InfoTreeParser
