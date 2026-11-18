# Paper B draft coverage

The source lock binds the active v1.2 manuscript and its preserved public v1.0 base (DOI 10.5281/zenodo.24142496). Each row records the scope of a planned Lean statement.

| Item | Statement | Formal status | Work packages | Claim facets |
|---|---|---|---|---|
| 1.1 | two-failure reachability oracle ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-1-1)) | NOT_CERTIFIED | EX0.1, EX0.2, EX0.3, EX1.1, EX1.2, EX1.3, EX1.4, EX2.1, EX2.2, EX2.3, EX2.4, EX4.1, EX4.2, EX4.3, EX4.4, EX5.1, EX5.2, EX5.3, EX5.4 | same precomputed index, every later failure set and target, deterministic build, peak and retained words, query time |
| 1.2 | listed target sets ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-1-2)) | NOT_CERTIFIED | EX5.5 | target-list disjunction, input and output charges |
| 2.1 | sibling quotients ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-2-1)) | NOT_CERTIFIED | EX1.1, EX1.2, EX1.3 | flat siblings, labelled path lifting, global quotient size |
| 2.2 | last-exit test ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-2-2)) | NOT_CERTIFIED | EX1.1, EX1.2, EX1.4 | outside and within-block queries, last-exit equivalence |
| 3.1 | forest of proper losses ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-3-1)) | NOT_CERTIFIED | EX2.1, EX2.2 | effective pairs, ancestor labels, nested proper losses |
| 3.2 | constructing the forest ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-3-2)) | NOT_CERTIFIED | EX0.3, EX2.3, EX2.4, EX5.1, EX5.2 | first appearances, dynamic depth jumps, key lookup, scan and storage costs |
| 4.1 | exit transfer ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-4-1)) | NOT_CERTIFIED | EX0.1, EX0.2, EX2.2, EX3.1, EX3.2, EX3.3 | fresh child endpoints, shared endpoint bypass, reverse inclusion, physical exit tails |
| 5.1 | compressed exit summaries ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-5-1)) | NOT_CERTIFIED | EX0.3, EX1.2, EX2.3, EX4.1, EX4.2, EX4.3, EX5.1, EX5.2 | LCA join, two-coordinate composition, chronological availability, jump evaluations and costs |
| 6.1 | a guarded output of residual multiplicity two ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-6-1)) | NOT_CERTIFIED | EX6.1, EX6.2 | single healthy-zero output, test witness, incidence and list costs |
| 6.2 | higher sensitivity ([statement](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md#statement-6-2)) | OPEN_RESEARCH | open research | open question |

Theorem 1.1 is proved in Section 5. The ledger records a separate hash for its deferred proof. Question 6.2 concerns three or more failures.

## Root obligations

The first two formal targets are the oracle theorem and its exit-set transfer identity. These obligations specify what each formal statement must capture.

| Obligation | Paper root | Owner | Status | Consumer |
|---|---|---|---|---|
| O11.1 — One admissible word model and a build independent of any future failures or target | 1.1 | cost model | OPEN | oracle contract |
| O11.2 — All original query cases and labelled projections | 1.1 | oracle | OPEN | query correctness |
| O11.3 — Construction and charged discovery on all sibling quotients | 1.1 | cost model | OPEN | preprocessing time |
| O11.4 — Peak workspace and retained size for the same index | 1.1 | cost model | OPEN | final oracle layout |
| O11.5 — Post-build query program using only retained records | 1.1 | cost model | OPEN | per-query time |
| O11.6 — Single implementation and formal correspondence with Theorem 1.1 | 1.1 | integration | OPEN | closed headline theorem |
| O41.1 — Proper-loss nesting and topological order of fresh endpoints | 4.1 | cuts | OPEN | exit transfer |
| O41.2 — Forward inclusion for fresh and inherited physical tails | 4.1 | cuts | OPEN | set inclusion |
| O41.3 — Reverse inclusion and full two-coordinate set equality | 4.1 | cuts | OPEN | closed structural theorem |

## Structural extension obligations

The listed batch and the guarded-output application depend on the oracle.

| Obligation | Paper item | Tasks | Status |
|---|---|---|---|
| O12.1 — Each target list and the full output vector with input charges | 1.2 | EX5.5 | OPEN |
| O61.1 — Find a detecting set with explicit incidence costs | 6.1 | EX6.1, EX6.2 | OPEN |
