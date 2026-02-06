module

public import LeanDag.DataFlow.Types
public import LeanDag.DataFlow.Rule
public import LeanDag.DataFlow.RuleRegistry
public import LeanDag.DataFlow.TermPatterns
public import LeanDag.DataFlow.Compute

@[expose] public section

/-!
# Data Flow Decomposition Framework

This module provides an extensible framework for decomposing Lean expressions
into data flow graphs, inspired by semantic tableaux rules for logical connectives.

## Architecture

- **Types**: Basic types (`NodeKind`, `ProtoNode`, `DecomposeResult`)
- **Rule**: The `Rule` structure and rule construction helpers
- **RuleRegistry**: Environment extension for rule registration
- **TermPatterns**: Built-in rules for let, lambda, if, match, etc.
- **Compute**: Main entry point (`computeFunctionalDagPure`)

## Usage

### Using Built-in Rules

```lean
import LeanDag.DataFlow

open LeanDag.DataFlow

-- The rules are automatically registered and used by computeFunctionalDagPure
```

### Adding Custom Rules

```lean
import LeanDag.DataFlow

open LeanDag.DataFlow

-- Define a custom rule
def myCustomRule : Rule where
  name := `MyProject.myRule
  priority := 85  -- Between built-in rules
  appliesTo e := e.isAppOf ``MyFunction
  decompose e lctx := do
    -- Custom decomposition logic
    return some { nodes := #[...], children := some #[...] }

-- Register at module initialization
initialize do
  registerRule myCustomRule
```

## Extension Points

1. **New expression forms**: Add rules with appropriate priority
2. **Override built-in behavior**: Use higher priority than default (100)
-/
