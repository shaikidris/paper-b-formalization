# Paper B EX2 Pair Forest

Formalize the full EX2 milestone for Paper B. The semantic goal is published Lemma 3.1. The executable and resource goal is Lemma 3.2 of v1.3 with deterministic \(O((n_H+m_H)L^2)\) preprocessing, linear working and retained space, \(O(L)\) pair lookup, and \(O(1)\) known-node membership. EX2.1 through EX2.4 are in scope. The v1.2 structural statements express the same forest and exit-transfer requirements.

| Carbon Medium lane | Task | Deliverable |
|---|---|---|
| Forest | EX2.1 and EX2.2 | A finite forest construction from the topological sweep, with exact labels, shared parent on key reuse, nesting, and the node bound. |
| Skew jumps | EX2.3 | Insertion and level-ancestor correctness with one jump per node and logarithmic moves on a growing tree. |
| Forest build | EX2.4 | The deterministic construction and membership costs for the same forest and jump code. |

The first two lanes can work concurrently. When a slot is available, start the construction lane and supply checked predecessor artifacts where available. Workers write proof checkpoints and short progress notes in their assigned directories. The local verifier builds candidates in a restricted scratch environment, preserves dependencies and exact declarations in its logs, and reports blockers. The paper-level milestone closes after the actual constructors, word-model bridge and statements are checked together.

[Paper B v1.3, Lemma 3.1](../../submissions/paper-b-v1.3-20261118/paper-b-v1.3.md#statement-3-1) · [Formalization tracker](../../paper-b-formalization/TASKS.md#ex21)
