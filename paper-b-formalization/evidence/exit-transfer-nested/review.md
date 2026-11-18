# Exit transfer for nested cuts

The Lean declaration `exitTailMem_iff_of_nested_cuts` proves the exit-tail identity pointwise for each original arc tail. It uses a flat acyclic quotient and distinct cuts whose child endpoints are lost when the parent cut is deleted. It derives the topological rank inequalities, the onward path from a fresh endpoint, and the survival of an old endpoint. It reuses the path and transfer lemmas from the first Carbon checkpoint. [Lean source](../../release-core/PaperB/ExitPaths.lean)

The next proof obligation is to construct the proper-loss forest in Lemma 3.1 and obtain those distinctness and nesting conditions for a real parent and child. A first step is to show that the earliest proper loss of a pair has exactly the two cut endpoints as its distinct predecessors. The full statement of Theorem 4.1 stays open in the tracker. [Paper B v1.2](../../../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-3-1)

Carbon Medium received the old-endpoint and fresh-endpoint declarations in two consecutive turns of the same native conversation. Both turns timed out before writing their Lean checkpoints. Codex supplied the additional proofs locally. The scoped build succeeded, and the elaborated main declaration had no axiom dependencies. [Build and statement](build.txt) · [Verification and relay receipts](verification.json)
