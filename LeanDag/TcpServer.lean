module

public import Lean
public import Std.Internal.Async
public import LeanDag.Protocol
public import LeanDag.Logging

open Lean
open Std.Net
open Std.Internal.IO.Async

@[expose] public section

namespace LeanDag

/-! ## Navigate Handler -/

/-- Type for navigate handler callback. Uses LineCharacterPosition from generated types. -/
abbrev NavigateHandler := String → LineCharacterPosition → IO Unit

/-- Global reference to the navigate handler (set by LspServer). -/
initialize navigateHandlerRef : IO.Ref (Option NavigateHandler) ← IO.mkRef none

/-- Set the navigate handler. Called from LspServer after capturing serverRequestEmitter. -/
def setNavigateHandler (handler : NavigateHandler) : IO Unit :=
  navigateHandlerRef.set (some handler)

/-! ## Port Configuration -/

/-- Default port range for TUI servers. Each worker gets a unique port from this range. -/
def defaultPortRangeMin : UInt16 := 9742
def defaultPortRangeMax : UInt16 := 9842

/-- Parse port from environment variable string. -/
def parsePort (s : String) (default_ : UInt16) : UInt16 :=
  match s.toNat? with
  | some n => if n > 0 && n < 65536 then n.toUInt16 else default_
  | none => default_

/-- Get TCP port range from environment or use defaults. -/
def getPortRange : IO (UInt16 × UInt16) := do
  let minPort ← match ← IO.getEnv "LEAN_DAG_PORT_MIN" with
    | some s => pure (parsePort s defaultPortRangeMin)
    | none => pure defaultPortRangeMin
  let maxPort ← match ← IO.getEnv "LEAN_DAG_PORT_MAX" with
    | some s => pure (parsePort s defaultPortRangeMax)
    | none => pure defaultPortRangeMax
  return (minPort, maxPort)

/-! ## Client Connection -/

/-- A connected TUI client. -/
structure ClientConnection where
  socket : TCP.Socket.Client
  id : Nat

/-! ## Cached State -/

/-- Cached DAG with its document context. -/
structure CachedDag where
  uri : String
  position : LineCharacterPosition
  dag : Option GenericDag

/-- Cached state for newly connecting clients. Stores typed data instead of full Messages. -/
structure CachedState where
  cursor : Option EditorCursorPosition := none
  dag : Option CachedDag := none

/-! ## TCP Server -/

/-- TCP server that broadcasts messages to TUI clients. -/
structure TcpServer where
  /-- The underlying TCP server socket. -/
  server : TCP.Socket.Server
  /-- Connected clients. -/
  clients : IO.Ref (Array ClientConnection)
  /-- Next client ID counter. -/
  nextId : IO.Ref Nat
  /-- Server mode for RPC communication. -/
  serverMode : ServerOperatingMode
  /-- Port the server is listening on. -/
  port : UInt16
  /-- File URI this worker is handling. -/
  fileUri : Option String
  /-- Minimum port in the configured range (for client discovery). -/
  portRangeMin : UInt16
  /-- Maximum port in the configured range (for client discovery). -/
  portRangeMax : UInt16
  /-- Cached state sent to newly connected clients. -/
  cachedState : IO.Ref CachedState

namespace TcpServer

/-- Create a new TCP server bound to the specified port. -/
def create (port : UInt16) (serverMode : ServerOperatingMode := .standalone)
    (fileUri : Option String := none) (portRangeMin : UInt16 := 9742) (portRangeMax : UInt16 := 9842) : IO TcpServer := do
  let server ← TCP.Socket.Server.mk
  let addr := SocketAddressV4.mk (IPv4Addr.ofParts 127 0 0 1) port
  server.bind addr
  server.listen 16
  let clients ← IO.mkRef #[]
  let nextId ← IO.mkRef 0
  let cachedState ← IO.mkRef {}
  log! s!"[TcpServer] Listening on 127.0.0.1:{port} for {fileUri.getD "unknown file"}"
  return { server, clients, nextId, serverMode, port, fileUri, portRangeMin, portRangeMax, cachedState }

def sendToClient (client : ClientConnection) (msg : ServerToClientMessage) : IO Bool := do
  let json := Lean.toJson msg
  let line := json.compress ++ "\n"
  let bytes := line.toUTF8
  try
    (client.socket.send bytes).block
    return true
  catch _ =>
    return false

/-- Broadcast a message to all connected clients. -/
def broadcast (srv : TcpServer) (msg : ServerToClientMessage) : IO Unit := do
  -- Cache typed data for newly connecting clients
  srv.cachedState.modify fun state =>
    match msg with
    | .cursor (uri := uri) (position := pos) (method := method) =>
        { state with cursor := some ⟨uri, pos, method⟩ }
    | .dag (uri := uri) (position := pos) (dag := dag) =>
        { state with dag := some { uri, position := pos, dag } }
    | _ => state
  let clients ← srv.clients.get
  log! s!"[TcpServer] Broadcasting to {clients.size} clients"
  let mut activeClients := #[]
  for client in clients do
    if ← sendToClient client msg then
      log! s!"[TcpServer] Sent to client {client.id}"
      activeClients := activeClients.push client
    else
      log! s!"[TcpServer] Failed to send to client {client.id}"
  -- Update clients list, removing disconnected ones
  srv.clients.set activeClients

def findNewlineIdx (s : String) : Option Nat := Id.run do
  let mut idx := 0
  for c in s.toList do
    if c == '\n' then
      return some idx
    idx := idx + 1
  return none

/-- Read a line from the client socket. Returns none on EOF or error. -/
partial def readLine (client : TCP.Socket.Client) (buffer : String := "") : Async (Option String) := do
  let chunk? ← client.recv? 1024
  match chunk? with
  | none => return none  -- EOF
  | some chunk =>
    let newData := String.fromUTF8! chunk
    let combined := buffer ++ newData
    -- Look for newline
    match findNewlineIdx combined with
    | some idx =>
      -- Found newline, extract line before it (convert Slice to String)
      let line := (combined.take idx).toString
      return some line
    | none =>
      -- No newline found, keep reading
      readLine client combined

/-- Handle a single client connection. -/
def handleClient (srv : TcpServer) (client : ClientConnection) : Async Unit := do
  log! s!"[TcpServer] Client {client.id} connected"

  -- Send Connected message and cached state immediately
  let _ ← IO.asTask do
    let connectedMsg := ServerToClientMessage.connected
      (fileUri := srv.fileUri)
      (port := some srv.port.toNat)
      (portRangeMax := some srv.portRangeMax.toNat)
      (portRangeMin := some srv.portRangeMin.toNat)
      (serverMode := some srv.serverMode)
    let _ ← sendToClient client connectedMsg
    -- Send cached state to newly connected client
    let state ← srv.cachedState.get
    if let some info := state.cursor then
      log! s!"[TcpServer] Sending cached cursor to client {client.id}"
      let _ ← sendToClient client (.cursor (uri := info.uri) (position := info.position) (method := info.method))
    if let some cached := state.dag then
      log! s!"[TcpServer] Sending cached DAG to client {client.id}"
      let _ ← sendToClient client (.dag (uri := cached.uri) (position := cached.position) (dag := cached.dag))

  -- Read loop for commands from client
  for _ in Lean.Loop.mk do
    let line? ← readLine client.socket
    match line? with
    | none =>
      log! s!"[TcpServer] Client {client.id} disconnected"
      break
    | some line =>
      if !line.isEmpty then
        match Lean.Json.parse line >>= ClientToServerCommand.fromJson? with
        | .ok cmd =>
          match cmd with
          | .navigate (uri := uri) (position := pos) =>
            log! s!"[TcpServer] Received navigate command from client {client.id}: {uri}:{pos.line}:{pos.character}"
            -- Call the navigate handler if set
            if let some handler ← navigateHandlerRef.get then
              handler uri pos
            else
              log! "[TcpServer] Navigate handler not set"
          | .getProofDag (uri := uri) (position := pos) (mode := mode) =>
            log! s!"[TcpServer] Received getProofDag command from client {client.id}: {uri}:{pos.line}:{pos.character} mode={mode}"
            -- Note: In library mode, this command cannot be directly handled here
            -- because we don't have access to the document context.
            -- The lean-tui client should use its own RPC client instead.
          | .ready =>
            log! s!"[TcpServer] Received ready command from client {client.id}"
            -- Send cached state to the client
            let state ← srv.cachedState.get
            if let some info := state.cursor then
              log! s!"[TcpServer] Sending cached cursor to ready client {client.id}"
              let _ ← sendToClient client (.cursor (uri := info.uri) (position := info.position) (method := info.method))
            if let some cached := state.dag then
              log! s!"[TcpServer] Sending cached DAG to ready client {client.id}"
              let _ ← sendToClient client (.dag (uri := cached.uri) (position := cached.position) (dag := cached.dag))
        | .error e =>
          log! s!"[TcpServer] Failed to parse command: {e}"

  -- Remove client from list
  let clients ← srv.clients.get
  srv.clients.set (clients.filter (·.id != client.id))

/-- Accept loop - accepts new connections and spawns handlers. -/
partial def acceptLoop (srv : TcpServer) : Async Unit := do
  for _ in Lean.Loop.mk do
    let client ← srv.server.accept
    let id ← srv.nextId.modifyGet fun n => (n, n + 1)
    let conn : ClientConnection := { socket := client, id }

    -- Add to clients list
    srv.clients.modify (·.push conn)

    -- Spawn client handler in background
    background (handleClient srv conn)

/-- Start the server accept loop in the background. -/
def start (srv : TcpServer) : IO Unit := do
  let _ ← IO.asTask do
    (acceptLoop srv).block

/-- Try to create a TcpServer on the given port. Returns none if port is in use. -/
def tryCreate (port : UInt16) (mode : ServerOperatingMode)
    (fileUri : Option String) (minPort maxPort : UInt16) : IO (Option TcpServer) := do
  try
    let srv ← TcpServer.create port mode fileUri minPort maxPort
    return some srv
  catch _ =>
    return none

/-- Find an available port and create the server. -/
def createWithAvailablePort (minPort maxPort : UInt16) (mode : ServerOperatingMode)
    (fileUri : Option String) : IO (Option TcpServer) := do
  let mut port := minPort
  while port ≤ maxPort do
    if let some srv ← tryCreate port mode fileUri minPort maxPort then
      return some srv
    port := port + 1
  return none

end TcpServer

/-! ## Global Server Management -/

/-- Global reference to the TUI TCP server (if started). -/
initialize tuiServerRef : IO.Ref (Option TcpServer) ← IO.mkRef none

/-- Lazily start the TCP server on first use. Returns the server if available.
    The fileUri parameter is used to identify which file this worker is handling. -/
def ensureTuiServer (fileUri : Option String := none) : IO (Option TcpServer) := do
  match ← tuiServerRef.get with
  | some srv => return some srv
  | none =>
    log! "ensureTuiServer: starting TCP server lazily"
    try
      let (minPort, maxPort) ← getPortRange
      let fileDesc := fileUri.getD "unknown file"
      log! s!"Looking for available port in range {minPort}-{maxPort} for {fileDesc}"
      match ← TcpServer.createWithAvailablePort minPort maxPort .library fileUri with
      | some srv =>
        log! s!"TCP server created on port {srv.port}"
        srv.start
        tuiServerRef.set (some srv)
        log! s!"TCP server started on port {srv.port} for {fileDesc}"
        log! s!"[LeanDag] TCP server started on port {srv.port} for {fileDesc}"
        return some srv
      | none =>
        log! s!"No available port in range {minPort}-{maxPort}"
        log! s!"[LeanDag] No available port in range {minPort}-{maxPort}"
        return none
    catch e =>
      log! s!"Failed to start TCP server: {e}"
      log! s!"[LeanDag] Failed to start TCP server: {e}"
      return none

end LeanDag
