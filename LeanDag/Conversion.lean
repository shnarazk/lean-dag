module

public import LeanDag.Types
public import LeanDag.NameUtils
public import LeanDag.InfoTreeParser

@[expose] public section

namespace LeanDag

open LeanDag.InfoTreeParser

/-! ## Conversion from Parsed Types to Output Types -/

def convertGoalInfo (g : ParsedGoal) : GoalInfo where
  type := .plain g.type
  username := filterNameOpt g.username
  id := g.id.name.toString
  gotoLocations := {}

def convertHypothesis (h : ParsedHypothesis) : HypothesisInfo where
  name := filterName h.username
  type := .plain h.type
  value := h.value.map TaggedText.plain
  id := h.id
  isProof := h.isProof
  isInstance := false
  gotoLocations := h.gotoLocations

end LeanDag
