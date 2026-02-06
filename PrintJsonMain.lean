import LeanDag.Elaboration
import LeanDag.Generator
import LeanDag.Logging



open Lean LeanDag
open LeanDag.Elaboration (ElaborationResult elaborateFile)
open LeanDag.Generator (DagContext computeDagFromTrees)

def parsePosition (s : String) : Option Lsp.Position := do
  let parts := s.splitOn ":"
  guard (parts.length == 2)
  let line ← parts[0]?.bind String.toNat?
  let col ← parts[1]?.bind String.toNat?
  guard (line > 0 && col > 0)
  return ⟨line - 1, col - 1⟩

structure Config where
  filePath : System.FilePath
  position : Lsp.Position
  verbose : Bool := false

def parseArgs (args : List String) : Option Config := do
  let verbose := args.contains "-v"
  let rest := args.filter (· != "-v")
  guard (rest.length == 2)
  let position ← parsePosition rest[1]!
  return { filePath := rest[0]!, position, verbose }

def filePathToUri (path : System.FilePath) : IO String := do
  let absPath ← IO.FS.realPath path
  return s!"file://{absPath}"

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none =>
    IO.eprintln "Usage: print-json [-v] <filename> <line>:<column>"
    IO.eprintln ""
    IO.eprintln "Position format: 1-indexed (editor style)"
    IO.eprintln "  Line 1 is the first line"
    IO.eprintln "  Column 1 is the first character"
    IO.eprintln ""
    IO.eprintln "Example:"
    IO.eprintln "  lake exe print-json Demo/Basic.lean 10:5"
    return 1
  | some config =>
    if config.verbose then
      LeanDag.verboseRef.set true
      LeanDag.logToStderrRef.set true
    unless (← config.filePath.pathExists) do
      IO.eprintln s!"Error: File not found: {config.filePath}"
      return 1

    log! s!"Elaborating {config.filePath}..."
    let result ← elaborateFile config.filePath config.position

    if result.messages.hasErrors then
      IO.eprintln "Elaboration failed with errors:"
      for msg in result.messages.toList.filter (·.severity == .error) do
        let text ← msg.data.toString
        IO.eprintln s!"  [line {msg.pos.line}, col {msg.pos.column}] {text}"
      return 1

    log! s!"Elaboration succeeded. InfoTrees: {result.infoTrees.size}"
    log! s!"Computing DAG at position {config.position.line + 1}:{config.position.character + 1}..."

    let fileUri ← filePathToUri config.filePath
    let ctx : DagContext := { fileMap := result.fileMap, fileUri }
    match ← computeDagFromTrees result.infoTrees config.position ctx with
    | some dag =>
      IO.println (toJson dag).pretty
      return 0
    | none =>
      IO.eprintln s!"No DAG found at position {config.position.line + 1}:{config.position.character + 1}"
      return 1
