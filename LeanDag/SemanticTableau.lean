import LeanDag.SemanticTableau.Types
import LeanDag.SemanticTableau.InfoTreeParser
import LeanDag.SemanticTableau.DiffComputation
import LeanDag.SemanticTableau.Builder

/-!
# Semantic Tableau Module

This module provides proof visualization using semantic tableau style:
- **InfoTreeParser**: Extracts tactic steps from Lean's InfoTree
- **DiffComputation**: Computes diffs between proof states
- **Builder**: Builds GenericDag with display_style="proof"

## Usage

```lean
import LeanDag.SemanticTableau

open LeanDag.SemanticTableau

-- Parse proof steps from InfoTree
let steps ← parseProofSteps snap text

-- Build unified DAG
let dag := GenericDag.buildProof steps cursorPos definitionName
```
-/
