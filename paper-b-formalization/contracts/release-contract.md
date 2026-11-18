# Proposed Paper B release contract

**State: PROPOSED — NOT APPROVED; no exact Lean signatures frozen.** This document records an architecture for review. PB0.4 must attach elaborated signatures and their hashes and record approval before theorem proof edits. Task preparation is not that approval.

## Selected surface

First release: the v1.1 draft's all-query **Theorem 3.2**, with proposed Challenge names `PaperB.threshold_all_queries_correct`, `PaperB.threshold_all_queries_time`, and `PaperB.threshold_all_queries_space`. These three declarations together must certify the same fixed solver/program family, input encoding, threshold convention and uniform constants. Splitting the claims into declarations must not allow unrelated programs or incompatible cost models.

Follow-on release: Proposition 3.3, proposed `PaperB.interned_batch_correct`, `PaperB.interned_batch_time`, `PaperB.interned_batch_space`, and `PaperB.historical_payload_bound`, sharing one implementation witness. Its additional Solution cone contains only the exact interning proof and its required support.

Exact informal statements and hashes are in [coverage.json](../coverage.json); interface details are in [INTERFACES.md](../INTERFACES.md). Proposed names are not existing declarations and the pseudo-signatures in that file are not frozen theorem types.

Nonclaims: individual-target memberships or witness paths for every query; linear time for unrestricted sensitivity two; universal near-linear sharing space; general 3-SAT; P versus NP; new literature priority; the paper's conditional lower bounds; whole-paper formalization; any automatic publication or registration.

## Mode and source identity

The future `release-core/` repository is to begin **PALOMAR-FIRST** after approval. The broader extension workspace is research-first and is not in the initial prospective registry tree. The present directory contains planning and evidence only. The existing controller repository is an extraction source with dirty work preserved; it is not relabelled Palomar-first retroactively.

Authoritative active source: local **v1.1 draft**, SHA-256 `957acfa0914524ab7e6501d90b3da09cf9babf1901b3cdddac09d52f6205fada`, at `papers/controller/paper-b-guarded-reachability-v1.1-draft.md`. It is unpublished and has no corresponding rendered PDF. The preserved published baseline is [Paper B v1.0](https://zenodo.org/records/24142496), PDF SHA-256 `88094f3d8aadb7fbca837dacd991a54483b466cd588c4a90896e5c26960ddea6`. Exact source/version boundaries are in [the source lock](../sources/source-lock.json). The first root requires every original query's Boolean answer from one fixed program; the existential OR is a derived consequence.

The user authorized the all-query, width and weighted-cover manuscript scope and corresponding plan update on 2026-11-12. The exact typed Challenge is still unelaborated and therefore not approved. Future proof/repository commits remain unset.

## Challenge and dependency boundary

Challenge is a small, standalone, inspectable specification. Its transitive imports may use only currently accepted Lean/Mathlib/Tau Ceti/CSLib roots. **No project-controlled proof module may enter Challenge, including a registered Paper A module.** Definitions essential to interpreting the result must be visible there or use genuinely trusted standard definitions. Opaque aliases must not hide reachability, program choice, resource semantics, asymptotic regimes or forbidden degenerate cases.

Solution contains the substantive proof cone, and Comparator checks its exact match to the frozen Challenge. Do not prove the selected goal by importing its deliberately unproved Challenge declaration. The mirrored specification and its hidden instances require an identity audit, not only matching source names.

Paper A dependencies, if needed by a later application entry, may enter Solution through an exact supported source pin or substantive audited port. No Paper A dependency is required for the first graph-only theorem. Use the current allowed standard-library revisions and pin the complete lockfile.

## Environment decision

The legacy controller tree uses Lean 4.33 and is not an eligible fresh-release baseline under the retrieved minimum `v4.35.0-rc2`. A known Paper A registration uses Lean `v4.35.0-rc3` with Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; this is a **candidate for the environment pilot**, not a verified new dependency choice. A stable supported pair is also acceptable after exact pinning and a clean pilot. Recheck current policy and toolchain eligibility at the actual freeze.

PB0.5 must establish the exact Lean release commit, supported dependency closure, usable caches/builds and module-system requirements. No new first-release proof should accumulate against an obsolete toolchain and rely on a later migration.

## Ownership and dependency graph

[tasks.json](../tasks.json) assigns exactly one writer role to each proposed owner module and records all immediate task dependencies. [obligations.json](../obligations.json) is the first-root burn-down. The module list is an admission envelope, not permission to create unused files. Admit a file only with a named root obligation, immediate consuming module, reason not to extend an existing owner, and current budget check.

Core owners: graph semantics/normalization/dominators; primitive/resource model; split network/bounded flow/path ranks/kernel; scheduler; amortization/resources; coordinator for the final Solution; reviewer for Audit. Resource review of a kernel does not grant simultaneous unsynchronized writes to its file. The optional interning owner is separate.

## Proposed review thresholds

These are **initial architecture thresholds for approval, not effort estimates or proven proof-size bounds**:

- first-release selected declarations: three, jointly describing one solver;
- Challenge: target at most 500 lines; mandatory architecture review before 800 lines;
- first-release local Lean modules: at most 18, including genuine proof/audit support;
- first-release total local Lean lines: review before 20,000;
- owner module: review before 2,000 lines; any applicable upstream per-file hard cap also applies;
- unreachable local release modules: exactly zero;
- unproved assumptions in the selected Solution cone: exactly zero, apart from the explicit valid-input/model hypotheses frozen in Challenge;
- no project axiom, `sorryAx`, or unapproved enlarged computation trust in Solution.

Each batch reports total/reachable modules and lines, new modules, unreachable code, root obligations before/after and exact theorem-type narrowing. Crossing a threshold requires an architectural decision before further expansion; it is not repaired by silently raising the number.

## Evidence and stop gates

Architecture approval alone allows environment and statement elaboration. **Exact signature approval** is required before theorem proofs. Record the immutable source, selected signatures and author confirmation for that gate.

A root is accepted only with literal paper correspondence, clean owner/root builds, placeholder and transitive axiom scans, complete operational/resource composition, strict-cone metrics, current official Comparator, required independent-kernel replay and a successful Challenge-rendering/assessability check. Finite tests, historical logs and metadata validation are separate evidence.

Stop and re-plan if a required graph theorem is newly conjectured, a cost primitive remains unjustified, the theorem must be weakened, an incompatible model is substituted, the proof cone gains unused modules, or two proof batches fail to close or narrow a root obligation. New mathematics belongs in the research workspace before porting its final proof.

Live registry operations are **handoff-only** in the current workflow. This contract authorizes no repository creation, push, release or submission. A future packet must name an exact approved commit and selected root set and preserve all public provenance.
