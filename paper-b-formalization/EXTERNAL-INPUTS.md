# External inputs for formalization

The [dependency register](external-inputs.json) records the consumers of each input. Graph libraries must realize the directed path, deletion and ancestor conventions of Section 2. An imported dominator constructor must provide its correctness and the time and space bounds needed on our adjacency-list model. The accounting also needs word arrays, deterministic sorting, binary search, and a proof of which temporary allocations remain live.

The [authority records](sources/authority-retrieval.json) preserve earlier source, toolchain, registry and public-edition checks. Toolchain selection and a clean replay for the proposed core are EX0.2 and EX5.4. The theorem statements’ reliance on particular algorithms is recorded in the [core contract](contracts/release-contract.md).

The [v1.2 proof and literature review](../evidence/paper-b-v12-adversarial-20261118/local-review.md) compares the exit-transfer construction with earlier dominator algorithms. Paper A's image theorem is used only for the physical interpretation of the guarded application.
