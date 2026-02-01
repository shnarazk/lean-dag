module

public import LeanDag.Types
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

namespace LeanDag

/-! ## Diff Computation -/

def diffHypotheses (source target : List HypothesisInfo)
    (changedTag : DiffTag) (missingTag : DiffTag) (markRemoved : Bool) : List HypothesisInfo :=
  let targetIds := Std.HashSet.ofList (target.map (·.id))
  let targetById : Std.HashMap String HypothesisInfo :=
    target.foldl (init := {}) fun m h => m.insert h.id h
  source.map fun h =>
    if targetIds.contains h.id then
      match targetById.get? h.id with
      | some th =>
        if h.type.toPlainText != th.type.toPlainText then
          { h with type := h.type.withDiff changedTag }
        else h
      | none => h
    else if markRemoved then
      { h with isRemoved := true, type := h.type.withDiff missingTag }
    else
      { h with type := h.type.withDiff missingTag }

def diffGoals (source target : List GoalInfo)
    (changedTag : DiffTag) (missingTag : DiffTag) (markRemoved : Bool) : List GoalInfo :=
  let targetIds := Std.HashSet.ofList (target.map (·.id))
  let targetById : Std.HashMap String GoalInfo :=
    target.foldl (init := {}) fun m g => m.insert g.id g
  source.map fun g =>
    if targetIds.contains g.id then
      match targetById.get? g.id with
      | some tg =>
        if g.type.toPlainText != tg.type.toPlainText then
          { g with type := g.type.withDiff changedTag }
        else g
      | none => g
    else if markRemoved then
      { g with isRemoved := true, type := g.type.withDiff missingTag }
    else
      { g with type := g.type.withDiff missingTag }

/-- Compute diff for a "before" state by comparing with "after" state.
    Marks hypotheses/goals that will change or be deleted. -/
def diffStateBefore (before after : ProofState) : ProofState :=
  { hypotheses := diffHypotheses before.hypotheses after.hypotheses .willChange .willDelete true
    goals := diffGoals before.goals after.goals .willChange .willDelete true }

/-- Compute diff for an "after" state by comparing with "before" state.
    Marks hypotheses/goals that changed or were inserted. -/
def diffStateAfter (before after : ProofState) : ProofState :=
  { hypotheses := diffHypotheses after.hypotheses before.hypotheses .wasChanged .wasInserted false
    goals := diffGoals after.goals before.goals .wasChanged .wasInserted false }

end LeanDag
