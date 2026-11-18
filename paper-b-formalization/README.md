# Formalizing Paper B v1.2 in Lean 4

The [published ten-page paper](../submissions/paper-b-v1.2-20261118/paper-b-v1.2.pdf) gives a two-vertex-failure reachability oracle on DAGs. Begin with the [formalization design](PLAN.md) for its two central theorems, nine proved statements, task order and Figure 1 checks. The [reuse map](REUSE.md) identifies relevant Lean declarations already in the project.

Use the [dashboard](DASHBOARD.md) for current status, the [milestone list](MILESTONES.md) and [task cards](TASKS.md) for assignment, and the [coverage map](COVERAGE.md) for proposed declarations and theorem dependencies. The [interfaces](INTERFACES.md), [release contract](contracts/release-contract.md), and [handoff instructions](DISPATCH.md) define acceptance. The [source lock](sources/source-lock.json) identifies the deposited edition. [Version DOI](https://doi.org/10.5281/zenodo.24339761)

From the project root:

```sh
python3 -B paper-b-formalization/plan.py validate
python3 -B paper-b-formalization/test_plan.py
python3 -B paper-b-formalization/plan.py ready
python3 -B paper-b-formalization/plan.py show EX3.2
```

Edit [tasks](tasks.json), [coverage](coverage.json), [root obligations](obligations.json) and [module dependencies](module-graph.json). Run `plan.py render` after ledger changes. All formal statements await Lean implementation and independent replay.
