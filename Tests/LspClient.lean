import Lean
import Lean.Data.Lsp.Ipc
import LeanDag

namespace Tests.LspClient

open Lean Lsp Ipc JsonRpc IO LeanDag

/-!
## Position Convention

All line/column parameters in this module use **1-indexed positions** matching
what editors display (e.g., line 1 is the first line, column 1 is the first character).

Internally, these are converted to LSP's 0-indexed format before sending requests.
LSP uses UTF-16 code units for columns, which matters for unicode characters.
-/

/-- Convert 1-indexed editor position to 0-indexed LSP position -/
def editorToLsp (line col : Nat) : (Nat × Nat) := (line - 1, col - 1)

def testProjectPath : System.FilePath := "Demo"

def fileUri (path : System.FilePath) : IO String := do
  let cwd ← IO.currentDir
  return s!"file://{cwd}/{path}"

def rootUri : IO String := fileUri testProjectPath

def initializeServer (requestId : Nat := 0) : IpcM InitializeResult := do
  let root ← rootUri
  let params : InitializeParams := {
    processId? := none
    rootUri? := some root
    capabilities := {}
  }
  writeRequest ⟨requestId, "initialize", params⟩
  let resp ← readResponseAs requestId InitializeResult
  writeNotification ⟨"initialized", InitializedParams.mk⟩
  return resp.result

def openDocument (uri : String) (content : String) : IpcM Unit := do
  let params : DidOpenTextDocumentParams := {
    textDocument := {
      uri := uri
      languageId := "lean4"
      version := 1
      text := content
    }
  }
  writeNotification ⟨"textDocument/didOpen", params⟩

def waitForFileReady (uri : String) (version : Nat := 1) : IpcM Unit := do
  let _ ← collectDiagnostics 100 uri version

/-- Call RPC method. Line/col are 1-indexed (editor style). -/
def callRpc (requestId : Nat) (sessionId : UInt64) (uri : String) (line col : Nat) (method : String) (innerParams : Json) : IpcM Json := do
  let (lspLine, lspCol) := editorToLsp line col
  let mode := innerParams.getObjValAs? String "mode" |>.toOption.getD "tree"
  let procedureParams := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("position", Json.mkObj [("line", lspLine), ("character", lspCol)]),
    ("mode", mode)
  ]

  let rpcParams := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("position", Json.mkObj [("line", lspLine), ("character", lspCol)]),
    ("sessionId", toJson sessionId),
    ("method", toJson method),
    ("params", procedureParams)
  ]
  writeRequest (α := Json) ⟨requestId, "$/lean/rpc/call", rpcParams⟩
  let resp ← readResponseAs requestId Json
  return resp.result

def connectRpcSession (requestId : Nat) (uri : String) : IpcM UInt64 := do
  let params := Json.mkObj [("uri", toJson uri)]
  writeRequest (α := Json) ⟨requestId, "$/lean/rpc/connect", params⟩
  let resp ← readResponseAs requestId Json
  match resp.result.getObjValAs? UInt64 "sessionId" with
  | .ok sessionId => return sessionId
  | .error e => throw <| IO.userError s!"Failed to parse sessionId: {e}"

/-- Request hover info. Line/col are 1-indexed (editor style). -/
def hoverRequest (requestId : Nat) (uri : String) (line col : Nat) : IpcM (Option Hover) := do
  let (lspLine, lspCol) := editorToLsp line col
  let params : HoverParams := {
    textDocument := { uri := uri }
    position := ⟨lspLine, lspCol⟩
  }
  writeRequest ⟨requestId, "textDocument/hover", params⟩
  let resp ← readResponseAs requestId (Option Hover)
  return resp.result

def LeanDagPath : IO System.FilePath := do
  let cwd ← IO.currentDir
  return cwd / ".lake" / "build" / "bin" / "lean-dag"

def runWithLeanDag (action : IpcM α) : IO α := do
  let cwd ← IO.currentDir
  let serverPath ← LeanDagPath
  let projectDir := cwd / testProjectPath
  Ipc.runWith "sh" #["-c",
    s!"cd {projectDir} && unset LEAN_PATH LEAN_SYSROOT && exec lake env sh -c 'LEAN_WORKER_PATH={serverPath} exec {serverPath}'"] action

def parseCompleteProofDag (json : Json) : Except String CompleteProofDag :=
  match json.getObjVal? "proofDag" with
  | .ok dagJson => FromJson.fromJson? dagJson
  | .error e => .error s!"Missing proofDag field: {e}"

/-- Get proof DAG at position. Line/col are 1-indexed (editor style). -/
def getCompleteProofDagAt (uri : String) (sessionId : UInt64) (line col : Nat) (requestId : Nat) : IpcM (Option CompleteProofDag) := do
  let result ← callRpc requestId sessionId uri line col "LeanDag.getCompleteProofDag" (Json.mkObj [("mode", "tree")])
  match parseCompleteProofDag result with
  | .ok dag => return some dag
  | .error _ => return none

end Tests.LspClient
