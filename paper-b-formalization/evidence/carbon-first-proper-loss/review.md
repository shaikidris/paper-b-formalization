# First proper loss and its two predecessors

In a flat quotient with a topological rank, every distinct predecessor of the first proper loss belongs to the cut. Conversely, both cut endpoints are predecessors. This is the local characterization used to discover an effective pair in Lemma 3.1 of Paper B v1.2. The proof uses the final-arc lemma from Carbon's preceding task. It treats parallel arcs by their endpoint relation. [Lean source](../../release-core/PaperB/ExitPaths.lean)

Carbon Medium delivered a complete Lean declaration to `0001.md`. Codex made one elaboration repair by supplying the endpoint equality as an explicit argument to `AvoidPath.target_alive`. The theorem statement and remaining proof text were preserved. The scoped `PaperB.ExitPaths` build succeeded on Lean 4.35.0-rc3, and the elaborated declaration had no axiom dependencies. [Build evidence](build.txt) · [Relay and verification record](verification.json)

The relay was closed after Lean had checked the saved declaration. It recorded a partial file report because Carbon had yet to write the completion marker.

The next forest step is to use this characterization during the topological sweep, including vertices with no proper loss and repeated appearances of a pair. The constructed forest and its complete correspondence with Lemma 3.1 remain open. [Paper B v1.2](../../../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-3-1)
