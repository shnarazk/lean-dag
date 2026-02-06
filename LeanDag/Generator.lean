module

public import Lean
public import LeanDag.Protocol
public import LeanDag.DataFlow.Compute
public import LeanDag.DataFlow.Types
public import LeanDag.DataFlow.TermPatterns
public import LeanDag.EffectFlow.Compute
public import LeanDag.SemanticTableau.InfoTreeParser
public import LeanDag.SemanticTableau.Builder
public import LeanDag.NameUtils

/-!
# DAG Generator

Shared classification and dispatch for computing a `GenericDag` from an
`InfoTree`.  Used by both the LSP server and the `print-json` CLI.
-/

open Lean Elab Server
open LeanDag.SemanticTableau.InfoTreeParser (parseInfoTreePure)
open LeanDag.SemanticTableau (GenericDag.buildProof)

@[expose] public section

namespace LeanDag.Generator

abbrev DagContext := LeanDag.SearchExpression.DagContext

/-- The three kinds of DAG the generator can produce. -/
inductive DagKind
  | proof
  | effectFlow
  | dataFlow

/-- Pure, deterministic classification of an InfoTree. -/
def classifyTree (tree : InfoTree) : DagKind :=
  if !LeanDag.DataFlow.isTermModeTree tree then .proof
  else if LeanDag.EffectFlow.isEffectfulTree tree then .effectFlow
  else .dataFlow

/-- Classify `tree` and run the matching builder. -/
def computeDag (tree : InfoTree) (position : Lsp.Position)
    (ctx : DagContext) : IO (Option GenericDag) :=
  match classifyTree tree with
  | .proof => do
    let some r ← parseInfoTreePure tree ctx.fileMap ctx.fileUri
      | return none
    if r.steps.isEmpty then return none
    let name := LeanDag.getDefinitionName tree
    return some (GenericDag.buildProof r.steps position name)
  | .effectFlow =>
    LeanDag.EffectFlow.computeEffectFlowDagPure tree position ctx.fileMap
  | .dataFlow =>
    LeanDag.DataFlow.computeFunctionalDagPure tree position ctx

/-- Try each tree in order, returning the first successful DAG. -/
def computeDagFromTrees (trees : PersistentArray InfoTree)
    (position : Lsp.Position) (ctx : DagContext) : IO (Option GenericDag) := do
  for tree in trees.toList do
    let dag ← computeDag tree position ctx
    if dag.isSome then return dag
  return none

end LeanDag.Generator
