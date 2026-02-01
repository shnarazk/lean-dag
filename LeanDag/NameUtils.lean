module

@[expose] public section

namespace LeanDag

/-! ## Name Filtering -/

/-- Check if pattern is a substring of s by splitting. -/
def containsSubstr (s pattern : String) : Bool :=
  (s.splitOn pattern).length > 1

def isHygienicName (s : String) : Bool :=
  containsSubstr s "._hyg." || containsSubstr s "._@."

def isUserVisibleName (s : String) : Bool :=
  !s.isEmpty && s != "[anonymous]" && !isHygienicName s

def filterName (s : String) : String :=
  if isUserVisibleName s then s else ""

def filterNameOpt (s : String) : Option String :=
  if isUserVisibleName s then some s else none

end LeanDag
