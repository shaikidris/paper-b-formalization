# Published Paper B statement map

Each row binds a paper statement to its proposed Lean declaration, immediate paper inputs and work packages. Independent acceptance uses the elaborated type and replay evidence.

| Item | Statement | Proposed declaration | Paper inputs | Formal status | Work packages |
|---|---|---|---|---|---|
| 1.1 | two-failure reachability oracle ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-1-1)) | PaperB.two_failure_dag_oracle | 2.1, 2.2, 3.2, 5.1 | NOT_CERTIFIED | EX0.1, EX0.2, EX0.3, EX1.1, EX1.2, EX1.3, EX1.4, EX1.5, EX1.6, EX2.1, EX2.2, EX2.3, EX2.4, EX4.1, EX4.2, EX4.3, EX4.4, EX5.1, EX5.2, EX5.3, EX5.4 |
| 1.2 | listed target sets ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-1-2)) | PaperB.listed_target_sets | 1.1 | NOT_CERTIFIED | EX5.5 |
| 2.1 | sibling quotients ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-2-1)) | PaperB.sibling_quotients | — | NOT_CERTIFIED | EX1.1, EX1.2, EX1.3 |
| 2.2 | last-exit test ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-2-2)) | PaperB.last_exit_test | 2.1 | NOT_CERTIFIED | EX1.1, EX1.2, EX1.4 |
| 3.1 | forest of proper losses ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-3-1)) | PaperB.proper_loss_forest | — | NOT_CERTIFIED | EX2.1, EX2.2 |
| 3.2 | constructing the forest ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-3-2)) | PaperB.build_proper_loss_forest | 3.1 | NOT_CERTIFIED | EX0.3, EX2.3, EX2.4 |
| 4.1 | exit transfer ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-4-1)) | PaperB.exit_set_transfer | 2.1, 3.1 | NOT_CERTIFIED | EX0.1, EX0.2, EX2.2, EX3.1, EX3.2, EX3.3 |
| 5.1 | compressed exit summaries ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-5-1)) | PaperB.compressed_exit_summaries | 3.2, 4.1 | NOT_CERTIFIED | EX0.3, EX1.2, EX1.6, EX2.3, EX4.1, EX4.2, EX4.3 |
| 6.1 | a guarded output of residual multiplicity two ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-6-1)) | PaperB.healthy_zero_detection | 1.2 | NOT_CERTIFIED | EX6.1, EX6.2 |
| 6.2 | higher sensitivity ([statement](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.md#statement-6-2)) | — | — | OPEN_RESEARCH | — |

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
