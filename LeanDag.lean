module

public import LeanDag.Types
public import LeanDag.LspServer
public import LeanDag.Environment

@[expose] public section

/-!
# LeanDag

A Lean 4 library that provides proof DAG visualization via RPC.

## Usage as a Library

Add LeanDag to your lakefile.lean:
```lean
require LeanDag from git
  "https://github.com/wvhulle/lean-dag.git" @ "main"
```

Then import in your Lean files:
```lean
import LeanDag
```

This automatically registers the `LeanDag.getProofDag` RPC method.

## Usage as a Standalone Binary

Build and run:
```
lake build lean-dag
.lake/build/bin/lean-dag --worker
```
-/
