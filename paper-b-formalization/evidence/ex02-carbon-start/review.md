# First Lean checkpoint for Paper B v1.2

Gemini 4 Carbon Medium supplied the first sixteen lemmas for EX0.2. Each theorem and proof occurs verbatim in the original code checkpoint. The source compiled as returned. Codex split the definitions and proofs into three modules, added the pointwise exit-transfer identity below and ran a clean local replay. The [verification record](verification.json) binds the source files, checkpoint, provider receipts and Lean build. The [published statement](../../../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-4-1) fixes the scope.

## What Lean proves

[Challenge.lean](../../release-core/Challenge.lean) represents adjacency lists with parallel arcs, failures of size at most two, and quotient exits labelled by their original arc tails. A length-zero path requires a live vertex. The graph retains its original identifiers and exposes acyclicity as a separate mathematical condition.

[Spec.lean](../../release-core/PaperB/Spec.lean) proves the path facts used on both the original graph and the quotient. [ExitPaths.lean](../../release-core/PaperB/ExitPaths.lean) proves both exit-transfer inclusions. Its final theorem, `exitTailMem_iff_of_paths`, fixes a particular physical tail, an endpoint of the parent pair, and a target properly lost by the child pair. It equates parent membership with the union of fresh-endpoint memberships and the child's membership at a shared endpoint. It requires three explicit facts.

1. Each endpoint of the child outside the parent can reach the target while avoiding both parent endpoints.
2. Each endpoint of the parent outside the child can be reached from the root while avoiding both child endpoints.
3. The pairs share at most one endpoint.

For Theorem 4.1 these must follow for the actual child and parent of the forest in Lemma 3.1. Flatness, proper-loss nesting and the topological order supply the path arguments in the paper. For the intersection fact use distinct unordered pairs or a canonical endpoint order. With ordered records, swapping both endpoints gives different records for the same cut. The term indexed by fresh endpoints already has no target parameter.

## Replay

From the project root run

```sh
python3 -B paper-b-formalization/evidence/ex02-carbon-start/replay.py
```

The replay builds the package from source with Lean 4.35.0-rc3 and its standard library. It checks all seventeen project theorems for axiom dependencies, then replays the three compiled modules with Lean's own `leanchecker`. The [audit input](Audit.lean) has twelve concrete examples including the three deletion answers in Figure 1. Deleting either \(h,V\) or \(\ell,V\) leaves a route to \(y\). Deleting \(U,V\) removes every route. A separate parallel-arc example checks two positive original-tail memberships and rules out borrowing a third label from another endpoint. The actual Figure 1 quotient exit sets remain a further fixture. [Local build log](build.txt)

Three existing controller lemmas on live endpoints and shrinking failure sets also replayed without axioms on this pin. The replay uses a hash-checked slice of the legacy file with the imports replaced by `Std`. The full legacy library and the renumbering adapter remain outside this check. [Reuse notes](../../REUSE.md)

## Handoff

The first Antigravity turn wrote the code checkpoint and timed out before writing its interface note. One retry resumed the same conversation and timed out without a second file. Both processes have exited. The checked-in code and local review supply the handoff.

EX0.2 remains open. Its next deliverables are the elaborated public statement for real forest edges and the type of one uniform costed build/query pair. The latter must build once for the graph and source before receiving any failure set or target, charge time and peak space during construction, and give the retained size and query cost. Deriving the three path facts for forest edges is the next mathematical step toward Theorem 4.1. All nine numbered statements retain their previous certification status. [Task tracker](../../TASKS.md#ex02)
