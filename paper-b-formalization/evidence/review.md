# v1.2 formalization plan review

The [active paper](../../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md) contains nine proof-bearing items and one open question. The source map binds each statement and proof separately. In particular Theorem 1.1 is stated in Section 1, Corollary 1.2 has its own nearby proof, and the actual proof of Theorem 1.1 appears in Section 5. A regression test exchanges these proof identities and requires rejection.

The first formal targets are Theorems 1.1 and 4.1. The oracle needs one uniform implementation, its peak and retained space, its preprocessing time and the time and correctness of every later query. The transfer identity is an equality of physical tail sets. Its proof obligations distinguish fresh endpoints, shared endpoints and the reverse inclusion. The [editions review](../../evidence/controller-paper-b-v1.2-20261118/README.md) records the corresponding manuscript checks.

The 25 task packages cover seven milestones. Nine selected-root obligations and two downstream obligations are open. Source mapping is complete, EX0.2 is ready, and the number of new certified Lean roots is zero. The [check record](plan-validation.json) reports actual validator and regression-control outputs. The [archived ledgers](../archive/v1.1/README.md) retain distinct identifiers for the earlier scope.
