import Lean
import Lean.Server.FileWorker
import Lean.Server.Watchdog
import Lean.Server.Requests
import LeanDag.Protocol
import LeanDag.TcpServer
import LeanDag.Generator
import LeanDag.Logging

open Lean Elab Server Lsp JsonRpc
open Lean.Server.FileWorker Lean.Server.Snapshots
open LeanDag (ensureTuiServer)
open LeanDag.Generator (DagContext)

namespace LeanDag

/-! ## Cursor State -/

/-- Cached cursor position for rebroadcasting after edits. -/
initialize lastCursorRef : IO.Ref (Option (String × Lsp.Position)) ← IO.mkRef none

/-! ## Server Request Emitter for Navigation -/

/-- Type alias for server request emitter function. -/
abbrev ServerRequestEmitterFn := String → Json → BaseIO (ServerTask (ServerRequestResponse Json))

/-- Global reference to the server request emitter (captured from RequestM context). -/
initialize serverRequestEmitterRef : IO.Ref (Option ServerRequestEmitterFn) ← IO.mkRef none

/-- ShowDocumentParams for window/showDocument request. -/
structure ShowDocumentParams where
  uri : String
  external : Option Bool := none
  takeFocus : Option Bool := some true
  selection : Option Lsp.Range := none
  deriving ToJson, FromJson

/-- Send a showDocument request to the editor. -/
def sendShowDocument (uri : String) (line : Nat) (character : Nat) : IO Unit := do
  log! s!"sendShowDocument: uri={uri} line={line} char={character}"
  match ← serverRequestEmitterRef.get with
  | some emitter =>
    let range : Lsp.Range := {
      start := { line := line, character := character }
      «end» := { line := line, character := character }
    }
    let params : ShowDocumentParams := {
      uri := uri
      takeFocus := some true
      selection := some range
    }
    let _ ← emitter "window/showDocument" (toJson params)
    log! "showDocument request sent"
  | none =>
    log! "No server request emitter available"

/-! ## RPC Types -/

structure GetProofDagParams where
  textDocument : TextDocumentIdentifier
  position     : Lsp.Position
  deriving FromJson, ToJson

structure GetProofDagResult where
  dag : GenericDag
  version  : Nat := 5
  deriving FromJson, ToJson

/-! ## RPC Handler -/

/-- Compute DAG from a snapshot using the shared Generator dispatch. -/
def computeDag (snap : Snapshot) (position : Lsp.Position) : RequestM (Option GenericDag) := do
  let doc ← RequestM.readDoc
  let ctx : DagContext := { fileMap := doc.meta.text, fileUri := doc.meta.uri }
  Generator.computeDag snap.infoTree position ctx

@[server_rpc_method]
def getProofDag (params : GetProofDagParams) : RequestM (RequestTask GetProofDagResult) := do
  RequestM.withWaitFindSnapAtPos params.position fun snap => do
    match ← computeDag snap params.position with
    | some dag => return { dag }
    | none => return { dag := { displayStyle := .proof, nodes := #[], metadata := Json.mkObj [] } }

builtin_initialize
  Lean.Server.registerBuiltinRpcProcedure
    `LeanDag.getProofDag GetProofDagParams GetProofDagResult getProofDag

/-! ## DAG Broadcasting

Chain onto textDocument/hover to compute and broadcast DAG to TUI clients.
This uses the same worker that already has elaboration cached, avoiding redundant work.
-/

/-- Broadcast DAG to TUI server with logging. -/
def broadcastDag (srv : TcpServer) (uri : String) (position : Lsp.Position)
    (dag : Option GenericDag) : IO Unit := do
  let kindName := dag.map (fun d => toString d.displayStyle) |>.getD "none"
  let nodeCount := dag.map (·.nodes.size) |>.getD 0
  log! s!"  broadcasting dag ({kindName}): nodes={nodeCount}"
  srv.broadcast (.dag (uri := uri) (position := position) (dag := dag))

/-- Rebroadcast proof DAG at cached cursor position after document changes. -/
def rebroadcastProofDag : RequestM (RequestTask Unit) := do
  let some (uri, position) ← lastCursorRef.get | return .pure ()
  let doc ← RequestM.readDoc
  -- Only rebroadcast if same document
  if doc.meta.uri != uri then return .pure ()

  let some srv ← ensureTuiServer (some (toString uri)) | return .pure ()

  RequestM.withWaitFindSnapAtPos position fun snap => do
    let dag ← computeDag snap position
    broadcastDag srv uri position dag

/-- Compute and broadcast proof DAG when hover request is received.

Note: We emit `FileFocused` here because Lean's server architecture doesn't support
custom notification handlers (they're hardcoded in FileWorker.lean). Some editors
send `textDocument/didFocus` when switching tabs, but we can't register a handler
for it. Instead, we emit `FileFocused` on every hover request, which effectively
signals file focus whenever the user interacts with a file. -/
def broadcastProofDagOnHover (params : Lsp.HoverParams) : RequestM (RequestTask Unit) := do
  let doc ← RequestM.readDoc
  let uri := doc.meta.uri
  let position := params.position

  -- Cache cursor position for rebroadcast after edits
  lastCursorRef.set (some (uri, position))

  -- Ensure TCP server is running and get reference
  let some srv ← ensureTuiServer (some (toString uri)) | return .pure ()

  -- Broadcast file focus notification (allows TUI to immediately switch files)
  -- This is emitted on every hover since we can't hook into textDocument/didFocus
  srv.broadcast (.fileFocused (uri := uri) (focused := true))

  -- Broadcast cursor position immediately
  let cursorInfo : EditorCursorPosition := { uri, position, method := "hover" }
  srv.broadcast (.cursor (uri := cursorInfo.uri) (position := cursorInfo.position) (method := cursorInfo.method))

  -- Capture the server request emitter if not already captured
  if (← serverRequestEmitterRef.get).isNone then
    let ctx ← read
    serverRequestEmitterRef.set (some ctx.serverRequestEmitter)
    setNavigateHandler fun navUri navPos => do
      sendShowDocument navUri navPos.line navPos.character
    log! "Captured serverRequestEmitter and set navigate handler"

  -- Compute and broadcast DAG using cached elaboration
  RequestM.withWaitFindSnapAtPos position fun snap => do
    let dag ← computeDag snap position
    broadcastDag srv uri position dag

builtin_initialize
  Lean.Server.chainLspRequestHandler "textDocument/hover" Lsp.HoverParams (Option Lsp.Hover)
    fun params prevTask => do
      let _ ← broadcastProofDagOnHover params
      return prevTask

/-- Chain onto documentColor request to rebroadcast after edits.
This request is sent by the editor after document changes. -/
builtin_initialize
  Lean.Server.chainLspRequestHandler "textDocument/documentColor"
    Lsp.DocumentColorParams (Array Lsp.ColorInformation)
    fun _ prevTask => do
      let _ ← rebroadcastProofDag
      return prevTask

builtin_initialize
  Lean.Server.chainLspRequestHandler "$/lean/plainGoal"
    Lsp.PlainGoalParams (Option Lsp.PlainGoal)
    fun _ prevTask => do
      let _ ← rebroadcastProofDag
      return prevTask

end LeanDag
