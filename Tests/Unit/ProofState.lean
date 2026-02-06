import Lean
import LeanDag
import Tests.Harness

namespace Tests.Unit.ProofState

open Lean LeanDag Tests.Harness

/-! ## Hypothesis Tracking Tests -/

/-- Test: New hypotheses are tracked with indices into proofStateAfter.hypotheses -/
def testNewHypothesesTracking : IO Unit := do
  IO.println "\n  [New Hypotheses Tracking]"

  -- intro n introduces hypothesis 'n'
  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "intro n" }
    position := ⟨3, 2⟩
    proofStateBefore := {
      goals := #[{ type := "Nat → Nat → Nat", id := "g1" }]
      hypotheses := #[]  -- No hypotheses before
    }
    proofStateAfter := {
      goals := #[{ type := "Nat → Nat", id := "g2" }]
      hypotheses := #[{ name := "n", type := "Nat", id := "h1" }]
    }
    newHypothesisIndices := #[0]  -- Index 0 in proofStateAfter.hypotheses
  }

  assertEqual "one new hypothesis" node.newHypothesisIndices.size 1
  assertEqual "new hyp index is 0" node.newHypothesisIndices[0]! 0
  assertEqual "can lookup new hyp" node.proofStateAfter.hypotheses[0]!.name "n"

/-- Test: Multiple hypotheses introduced at once (e.g., intro a b c) -/
def testMultipleNewHypotheses : IO Unit := do
  IO.println "\n  [Multiple New Hypotheses]"

  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "intro a b c" }
    position := ⟨3, 2⟩
    proofStateBefore := {
      goals := #[{ type := "A → B → C → D", id := "g1" }]
      hypotheses := #[]
    }
    proofStateAfter := {
      goals := #[{ type := "D", id := "g2" }]
      hypotheses := #[
        { name := "a", type := "A", id := "h1" },
        { name := "b", type := "B", id := "h2" },
        { name := "c", type := "C", id := "h3" }
      ]
    }
    newHypothesisIndices := #[0, 1, 2]  -- All three are new
  }

  assertEqual "three new hypotheses" node.newHypothesisIndices.size 3
  -- Verify all can be looked up
  for i in [0, 1, 2] do
    assertTrue s!"hyp {i} exists" (node.proofStateAfter.hypotheses[i]?.isSome)

/-- Test: Theorem parameters are not marked as new hypotheses -/
def testTheoremParametersNotNew : IO Unit := do
  IO.println "\n  [Theorem Parameters vs Introduced Hypotheses]"

  -- theorem foo (h : P) : P ∧ P := by constructor <;> exact h
  -- The hypothesis 'h' comes from the theorem signature, not from a tactic
  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "constructor" }
    position := ⟨3, 2⟩
    proofStateBefore := {
      goals := #[{ type := "P ∧ P", id := "g1" }]
      hypotheses := #[{ name := "h", type := "P", id := "h_param" }]  -- From theorem
    }
    proofStateAfter := {
      goals := #[
        { type := "P", username := some "left", id := "g2" },
        { type := "P", username := some "right", id := "g3" }
      ]
      hypotheses := #[{ name := "h", type := "P", id := "h_param" }]
    }
    newHypothesisIndices := #[]  -- No NEW hypotheses, 'h' existed before
  }

  assertEqual "no new hypotheses" node.newHypothesisIndices.size 0
  assertEqual "hypothesis preserved" node.proofStateAfter.hypotheses.size 1

/-- Test: Cases tactic introduces new hypotheses per branch -/
def testCasesIntroducesHypotheses : IO Unit := do
  IO.println "\n  [Cases Introduces Branch-Specific Hypotheses]"

  -- In the inl branch, we get hypothesis 'ha : A'
  let inlBranch : ProofDagTacticNode := {
    id := 1
    tactic := { text := "case inl ha =>" }
    position := ⟨4, 4⟩
    proofStateBefore := {
      goals := #[{ type := "C", username := some "case inl", id := "g2" }]
      hypotheses := #[{ name := "h", type := "A ∨ B", id := "h1" }]
    }
    proofStateAfter := {
      goals := #[{ type := "C", id := "g2" }]
      hypotheses := #[
        { name := "h", type := "A ∨ B", id := "h1" },
        { name := "ha", type := "A", id := "h2" }  -- New from case
      ]
    }
    newHypothesisIndices := #[1]  -- Only 'ha' is new
    parent := some 0
  }

  assertEqual "one new hypothesis in branch" inlBranch.newHypothesisIndices.size 1
  assertEqual "new hyp is 'ha'" inlBranch.proofStateAfter.hypotheses[1]!.name "ha"

/-! ## Goal Change Tests -/

/-- Test: Goal solved (proofStateAfter.goals is empty) -/
def testGoalSolved : IO Unit := do
  IO.println "\n  [Goal Solved Detection]"

  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "rfl" }
    position := ⟨3, 2⟩
    proofStateBefore := { goals := #[{ type := "n = n", id := "g1" }], hypotheses := #[] }
    proofStateAfter := { goals := #[], hypotheses := #[] }  -- Empty = solved
  }

  assertTrue "goals empty means solved" node.proofStateAfter.goals.isEmpty

/-- Test: Goal spawned (more goals after than before) -/
def testGoalSpawned : IO Unit := do
  IO.println "\n  [Goal Spawned - Constructor/Cases]"

  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "constructor" }
    position := ⟨3, 2⟩
    proofStateBefore := { goals := #[{ type := "P ∧ Q", id := "g1" }], hypotheses := #[] }
    proofStateAfter := {
      goals := #[
        { type := "P", username := some "left", id := "g2" },
        { type := "Q", username := some "right", id := "g3" }
      ]
      hypotheses := #[]
    }
  }

  assertEqual "spawned two goals" node.proofStateAfter.goals.size 2
  assertTrue "more goals than before" (node.proofStateAfter.goals.size > node.proofStateBefore.goals.size)

/-- Test: Goal modified (type changed but same logical goal) -/
def testGoalModified : IO Unit := do
  IO.println "\n  [Goal Modified - Simp/Rewrite]"

  let node : ProofDagTacticNode := {
    id := 0
    tactic := { text := "simp [Nat.add_zero]" }
    position := ⟨3, 2⟩
    proofStateBefore := { goals := #[{ type := "n + 0 = n", id := "g1" }], hypotheses := #[] }
    proofStateAfter := { goals := #[{ type := "n = n", id := "g1'" }], hypotheses := #[] }
  }

  assertEqual "still one goal" node.proofStateAfter.goals.size 1
  -- Type changed from "n + 0 = n" to "n = n"
  assertTrue "goal type changed" (node.proofStateBefore.goals[0]!.type != node.proofStateAfter.goals[0]!.type)

/-! ## Hypothesis Kind Tests -/

/-- Test: is_proof_term flag distinguishes proof terms from data -/
def testHypothesisKinds : IO Unit := do
  IO.println "\n  [Hypothesis Kinds - Proof vs Data]"

  let state : TacticProofState := {
    goals := #[{ type := "C", id := "g1" }]
    hypotheses := #[
      { name := "n", type := "Nat", id := "h1", isProofTerm := false },           -- Data
      { name := "h", type := "n > 0", id := "h2", isProofTerm := true },          -- Proof
      { name := "inst", type := "Decidable P", id := "h3", isTypeclassInstance := true } -- Instance
    ]
  }

  assertTrue "n is data" (!state.hypotheses[0]!.isProofTerm)
  assertTrue "h is proof" state.hypotheses[1]!.isProofTerm
  assertTrue "inst is instance" state.hypotheses[2]!.isTypeclassInstance

/-! ## Hygienic Name Filtering Tests -/

/-- Test: Hygienic names are filtered out -/
def testHygienicNameFiltering : IO Unit := do
  IO.println "\n  [Hygienic Name Filtering]"

  -- These should be filtered (empty name in output)
  assertTrue "._hyg. is hygienic" (String.isHygienic "x._hyg.123")
  assertTrue "._@. is hygienic" (String.isHygienic "foo._@.bar")

  -- These should be visible
  assertTrue "normal name is visible" (String.isUserVisible "n")
  assertTrue "case name is visible" (String.isUserVisible "case inl")

  -- Filter function
  assertEqual "hygienic filtered to empty" (String.filterName "x._hyg.123") ""
  assertEqual "normal name preserved" (String.filterName "hypothesis") "hypothesis"

/-! ## Test Runner -/

def runTests : IO Unit := do
  IO.println "\n══════════════════════════════════════════════════════════════"
  IO.println "  ProofState Change Tests (Unit)"
  IO.println "══════════════════════════════════════════════════════════════"

  testNewHypothesesTracking
  testMultipleNewHypotheses
  testTheoremParametersNotNew
  testCasesIntroducesHypotheses
  testGoalSolved
  testGoalSpawned
  testGoalModified
  testHypothesisKinds
  testHygienicNameFiltering

  IO.println "\n  ✓ ProofState unit tests passed"

end Tests.Unit.ProofState
