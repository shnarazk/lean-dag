import Lean.Elab.Frontend
import Lean.Elab.Import

/-!
# Standalone Elaboration

Partial file elaboration for the `print-json` CLI.  Processes commands
only up to the cursor position so declarations after the cursor are
skipped.
-/

open Lean Elab

namespace LeanDag.Elaboration

/-- Result of elaborating a file. -/
structure ElaborationResult where
  messages : MessageLog
  infoTrees : PersistentArray InfoTree
  fileMap : FileMap

open Lean.Elab in
/-- Process commands one at a time, stopping once the parser position passes `target`. -/
partial def processCommandsUntil (target : String.Pos.Raw) : Frontend.FrontendM Unit := do
  let ps ← Frontend.getParserState
  if ps.pos > target then return
  let done ← Frontend.processCommand
  if done then return
  processCommandsUntil target

/-- Elaborate a Lean file up to `position` and return the result with InfoTrees. -/
def elaborateFile (filePath : System.FilePath) (position : Lsp.Position) : IO ElaborationResult := do
  let code ← IO.FS.readFile filePath
  Lean.initSearchPath (← Lean.findSysroot)
  let inputCtx := Parser.mkInputContext code filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx

  let targetPos := inputCtx.fileMap.lspPosToUtf8Pos position
  let ctx : Frontend.Context := { inputCtx }
  let initState : Frontend.State := {
    commandState := Command.mkState env messages {}
    parserState
    cmdPos := parserState.pos
  }
  let (_, finalState) ←
    (processCommandsUntil targetPos |>.run ctx).run initState

  return {
    messages := finalState.commandState.messages
    infoTrees := finalState.commandState.infoState.trees
    fileMap := inputCtx.fileMap
  }

end LeanDag.Elaboration
