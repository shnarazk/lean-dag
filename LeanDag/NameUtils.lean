module

public import Lean

@[expose] public section

open Lean Elab

/-! ## Name Filtering -/

def containsSubstr (s pattern : String) : Bool :=
  (s.splitOn pattern).length > 1

def String.isHygienic (s : String) : Bool :=
  containsSubstr s "._hyg." || containsSubstr s "._@."

def String.isUserVisible (s : String) : Bool :=
  !s.isEmpty && s != "[anonymous]" && !s.isHygienic

/-- Check if a name follows the elaborator's synthetic parameter naming pattern.
    Lean may represent these as:
    - Name.num: "x.1", "a.2"
    - Name.str: "x_1", "a_2"
    - Hygienic names: "x._@.Module._hyg.N" -/
def String.isSyntheticParamName (s : String) : Bool :=
  -- Handle Name.str pattern: "x_1", "a_2", etc.
  let underscorePattern := (s.startsWith "x_" || s.startsWith "a_") && (s.drop 2).all Char.isDigit
  -- Handle Name.num pattern: "x.1", "a.2", etc.
  let dotNumPattern := (s.startsWith "x." || s.startsWith "a.") && (s.drop 2).all Char.isDigit
  -- Compiler-generated names: "__discr", "__do_lift", etc.
  let compilerGenerated := s.startsWith "__"
  underscorePattern || dotNumPattern || compilerGenerated || s.isHygienic

def String.filterName (s : String) : String :=
  if s.isUserVisible then s else ""

def String.filterNameOpt (s : String) : Option String :=
  if s.isUserVisible then some s else none

/-! ## Definition Name Extraction -/

namespace LeanDag

/-- Extract the definition name from the InfoTree by finding the enclosing command.
    Uses the same pattern as Lean's DocumentSymbol handler. -/
def getDefinitionName (tree : InfoTree) : Option String :=
  let names := tree.collectNodesBottomUp fun _ctx i _cs acc =>
    match i with
    | .ofCommandInfo ci =>
      let declId := ci.stx.getArg 1 |>.getArg 1
      let id := declId.getArg 0 |>.getId
      if id.isAnonymous then acc else id.toString :: acc
    | _ => acc
  names.head?

end LeanDag
