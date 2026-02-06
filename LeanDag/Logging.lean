import Lean

register_option leanDag.verbose : Bool := {
  defValue := false
  descr := "Enable verbose logging for LeanDag (source locations included)."
}

namespace LeanDag

initialize logPathRef : IO.Ref String ← do
  let home := (← IO.getEnv "HOME").getD "/tmp"
  IO.mkRef s!"{home}/.cache/lean-dag.log"

initialize logToStderrRef : IO.Ref Bool ← IO.mkRef false

initialize verboseRef : IO.Ref Bool ← IO.mkRef false

def formatElapsedTime (ms : Nat) : String :=
  let hours := ms / 3600000
  let minutes := (ms % 3600000) / 60000
  let seconds := (ms % 60000) / 1000
  let millis := ms % 1000
  let pad2 (n : Nat) := if n < 10 then s!"0{n}" else toString n
  let pad3 (n : Nat) := if n < 10 then s!"00{n}" else if n < 100 then s!"0{n}" else toString n
  s!"{pad2 hours}:{pad2 minutes}:{pad2 seconds}.{pad3 millis}"

def logImpl (loc msg : String) : IO Unit := do
  let toStderr ← logToStderrRef.get
  if toStderr then
    IO.eprintln s!"{loc} {msg}"
  else
    let path ← logPathRef.get
    let ms ← IO.monoMsNow
    let h ← IO.FS.Handle.mk path .append
    h.putStr s!"[{formatElapsedTime ms}] {loc} {msg}\n"

open Lean Elab Term in
scoped elab "log! " msg:term : term => do
  let pos := (← getRef).getPos?.getD 0
  let ctx ← readThe Core.Context
  let ⟨line, col⟩ := ctx.fileMap.toPosition pos
  let cwdStr := (← IO.currentDir).toString
  let root := if cwdStr.endsWith "/" then cwdStr else cwdStr ++ "/"
  let relPath := if ctx.fileName.startsWith root
    then ctx.fileName.drop root.length
    else ctx.fileName
  let locStx := Syntax.mkStrLit s!"{relPath}:{line}:{col}"
  if leanDag.verbose.get ctx.options then
    elabTerm (← `(logImpl $locStx $msg)) none
  else
    elabTerm (← `(do if (← verboseRef.get) then logImpl $locStx $msg)) none

end LeanDag
