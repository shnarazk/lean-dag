module

public import Lean
public import Lean.Server.FileWorker
public import Lean.Server.Watchdog
public import Lean.Server.Requests
public import LeanDag.Types
public meta import LeanDag.InfoTreeParser
public import LeanDag.NameUtils
public import LeanDag.Conversion
public import LeanDag.DiffComputation
public import LeanDag.DagBuilder

@[expose] public section

open Lean Elab Server Lsp JsonRpc
open Lean.Server.FileWorker Lean.Server.Snapshots
open LeanDag.InfoTreeParser

namespace LeanDag

/-! ## RPC Types -/

structure GetProofDagParams where
  textDocument : TextDocumentIdentifier
  position     : Lsp.Position
  mode         : String := "tree"
  deriving FromJson, ToJson

structure GetProofDagResult where
  proofDag : ProofDag
  version  : Nat := 5
  deriving FromJson, ToJson

/-! ## RPC Handler -/

def handleGetProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) := do
  let doc ← RequestM.readDoc
  let utf8Pos := doc.meta.text.lspPosToUtf8Pos params.position
  IO.eprintln s!"[RPC] getProofDag mode={params.mode} pos={params.position} utf8={utf8Pos} uri={doc.meta.uri}"
  IO.eprintln s!"[RPC] document version={doc.meta.version} headerSnap exists"
  RequestM.withWaitFindSnapAtPos params.position fun snap => do
    IO.eprintln s!"[RPC] snapshot found endPos={snap.endPos}"
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos params.position
    match params.mode with
    | "tree" =>
      match ← parseInfoTree snap.infoTree with
      | some result =>
        let definitionName := getDefinitionName snap.infoTree
        IO.eprintln s!"[RPC] tree mode: {result.steps.length} steps, def={definitionName}"
        return { proofDag := buildProofDag result.steps params.position definitionName }
      | none =>
        IO.eprintln "[RPC] tree mode: no result"
        return { proofDag := {} }
    | "single_tactic" =>
      match goalsAt? snap.infoTree text hoverPos with
      | r :: _ =>
        let binderCache := buildBinderCache snap.infoTree text
        let result ← parseTacticInfo r.ctxInfo (.ofTacticInfo r.tacticInfo) [] {} true snap.infoTree binderCache doc.meta.uri
        let definitionName := getDefinitionName snap.infoTree
        IO.eprintln s!"[RPC] single_tactic mode: {result.steps.length} steps, def={definitionName}"
        return { proofDag := buildProofDag result.steps params.position definitionName }
      | [] =>
        IO.eprintln "[RPC] single_tactic mode: no goals at position"
        return { proofDag := {} }
    | _ =>
      IO.eprintln s!"[RPC] unknown mode: {params.mode}"
      return { proofDag := {} }

/-! ## RPC Registration -/

/--
Get proof DAG for the current position in a document.

This RPC method is registered via `@[server_rpc_method]` for library mode
(when users `import LeanDag` in their Lean files).
-/
-- @[server_rpc_method]
def getProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) :=
  handleGetProofDag params

/-! ## Standalone Binary Support

When running as a standalone binary (lean-dag executable), the RPC method must be
registered as a builtin procedure since the worker processes don't import LeanDag.
-/

builtin_initialize
  Lean.Server.registerBuiltinRpcProcedure
    `LeanDag.getProofDag GetProofDagParams GetProofDagResult handleGetProofDag

/-- Entry point for running as a watchdog process (standalone binary mode). -/
def watchdogMain (args : List String) : IO UInt32 :=
  Lean.Server.Watchdog.watchdogMain args

/-- Entry point for running as a worker process (standalone binary mode). -/
def workerMain (opts : Lean.Options := {}) : IO UInt32 :=
  Lean.Server.FileWorker.workerMain opts

end LeanDag
