# Native compact-builder array audit

The harness instruments emitted calls to `lean_array_fset`, `lean_array_set`,
`lean_array_uset`, and `lean_array_push` in the compact builder's 111 generated
C modules. It records the initialized cells present on shared inputs and on
pushes at capacity. Graph construction and output cleanup are outside the
measurement. The harness calls the generated entry point with erased proofs
on valid topologically numbered flat quotients.

The adjacent-hubs graph has one root and one leaf for each consecutive hub
pair. The ladder has two vertices per layer, complete arcs to the next layer,
and parallel labelled occurrences. The harness checks the output dictionary
length on every fixture.

From the pinned `release-core` checkout after `lake build`, run the following.
Use the Lean toolchain prefix reported by `lean --print-prefix` and a separate
scratch directory for native outputs.

```sh
python3 /path/to/audit/build.py "$PWD/.lake/build/ir" "$(lean --print-prefix)" /path/to/scratch
/path/to/scratch/audit
```

The baseline has two shared updates per run. One is the first write to the
interval arrays, whose initial zero-filled buffers are shared in generated C.
The other is the first in-place map of the shared back-key source array.
The initialized cells at those updates are linear in the graph size on these
fixtures. The preallocated parent/depth extraction removes the observed
growth copies. These runs give finite evidence about the instrumented sites.
Copies internal to runtime helpers and all-input ownership remain separate
proof obligations.
