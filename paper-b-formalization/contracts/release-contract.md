# Proposed core release contract

The core has two mathematical targets. The Lean names below are proposed. Their elaborated types and supported environment belong to EX0.2.

1. `PaperB.exit_set_transfer` gives the equality of the sets of original exit tails in Theorem 4.1. Its hypotheses include a real child and parent, proper loss of the child, and an endpoint of the parent. Its output includes both the target-independent fresh part and the inherited part when the endpoint is shared.
2. `PaperB.two_failure_dag_oracle` witnesses one deterministic build and one query program. For every input the same built object satisfies correctness for every later query, the cubic-log time bounds, linear peak construction space in the explicit graph, and linear retained words in its vertex count. See the [quantifiers and units](../INTERFACES.md).

Acceptance requires an elaborated statement checked against the pinned paper, a reproducible build, declared axioms and dependencies, and independent replay against that exact surface. An external dominator or RAM cost assumption that lacks a checked bridge must be recorded as an assumption of the corresponding partial result. The [obligation ledger](../obligations.json) gives the required evidence for a complete root. Batch aggregation and the guarded application have separate closure rows. The current [coverage report](../COVERAGE.md) records the formal status.
