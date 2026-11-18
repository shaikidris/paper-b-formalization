# External inputs for formalization

The [dependency register](external-inputs.json) records the consumers of each input. Graph libraries must realize the directed path, deletion and ancestor conventions of Section 2. An imported dominator constructor must provide its correctness and the time and space bounds needed on our adjacency-list model. The accounting also needs word arrays, deterministic sorting, binary search, and a proof of which temporary allocations remain live.

The [authority records](sources/authority-retrieval.json) preserve earlier source, toolchain, registry and public-edition checks. Toolchain selection and a clean replay for the proposed core are EX0.2 and EX5.4. The theorem statements’ reliance on particular algorithms is recorded in the [core contract](contracts/release-contract.md).

The independent mathematical [analogue and literature comparison](../evidence/paper-b-space-20261118/exit-transfer-literature-and-paper-b.md) gives context for derived sibling graphs, two-cut hierarchies and Choudhary's general-digraph oracle. Paper A's image theorem is used only for the physical interpretation of the guarded application.
