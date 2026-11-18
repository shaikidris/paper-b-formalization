# Milestones for the exit-transfer oracle

The input is a finite adjacency-list DAG and a source. A later query supplies up to two failed vertices and one target. Construction, correctness, query time and space are statements about the same index. The [formal interfaces](INTERFACES.md) spell out this dependency.

| Stage | Deliverable | Dependency that matters |
|---|---|---|
| EX0 | Source identity, supported Lean environment, typed statements and cost model | Pin the full graph representation and word model before certifying asymptotic claims. |
| EX1 | Normalization, ordinary dominators, labelled sibling graphs and last exits | Keep original arc tails when different exits have the same quotient endpoints. |
| EX2 | Separating-pair forest and its charged construction | Prove membership in the proper-loss set by inclusive ancestry. Count every distinct-predecessor scan. |
| EX3 | Both inclusions in Theorem 4.1 | Treat fresh and shared endpoints before compressing exits to LCAs. |
| EX4 | Executable index and query procedures | Prove each map and base has been installed before use. |
| EX5 | Resource and correctness theorem for the uniform oracle, then listed-target corollary | Discard input arcs at the end of construction. The query takes only the retained index. |
| EX6 | Healthy-zero guarded-output application | Charge residual guard memberships, declared labels and every terminal occurrence. |

The [task DAG](TASKS.md) gives prerequisites and acceptance evidence per package. [Root obligations](obligations.json) separate the structural theorem from the uniform algorithm theorem. The paper proves the batch and decoder results as downstream consequences. A problem with three or more failures is recorded as [Question 6.2](sources/paper-b-v1.2-draft.md#statement-6-2).
