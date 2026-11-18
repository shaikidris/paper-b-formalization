# Formalizing the two-failure reachability oracle

The active [Paper B manuscript](../papers/controller/paper-b-two-failure-reachability-v1.2-draft.md) gives a deterministic index for a fixed source in an arbitrary DAG. The first two Lean targets are the online oracle (Theorem 1.1) and the equality of its physical exit-tail sets (Theorem 4.1). The article proves nine numbered results and poses one open question. No Paper B root currently has a Lean certificate.

Start with the [dashboard](DASHBOARD.md) for current counts, the [milestones](MILESTONES.md) for the proof order, and the [statement map](COVERAGE.md) for the tasks attached to each result. The [interface specification](INTERFACES.md) and [release contract](contracts/release-contract.md) describe exactly what the two root statements must express.

From the project root run

~~~sh
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
python3 -B paper-b-formalization/plan.py ready
python3 -B paper-b-formalization/plan.py show EX3.2
~~~

The editable ledgers are [tasks](tasks.json), [coverage](coverage.json) and [obligations](obligations.json). After a ledger change, run `plan.py render` to update the four generated views. The [source lock](sources/source-lock.json) identifies the active text, the prior editions and the proof evidence. The [threshold companion](../papers/controller/paper-b-threshold-companion-v1.2.md) and its [archived v1.1 plan](archive/v1.1/README.md) preserve the earlier results and task identifiers.
