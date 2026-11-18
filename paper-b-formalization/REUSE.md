# Existing proofs and reuse boundaries

## What exists

The legacy controller formalization is at `../formalization/`. Its board contains 103 tasks (72 labelled VERIFIED, 3 IN_PROGRESS, 28 TODO), pinned to an older combined-paper scope. Its Paper B inventory has **16 entries**, whereas published v1.0 has **30** and the active v1.1 draft has **32**. These old statuses are historical task contracts, not automatic verification of the published paper.

The existing graph code provides useful semantics and transformations:

- `Controller/Graphs/FailureBatch.lean`: failure reachability, explicit queries and batch size, common deletion, incidence handling and some RAM-related support.
- `Controller/Graphs/DecoderEquivalence.lean`: guarded evaluation/path equivalence, candidate queries, forward/reverse constructions and size/operation counters.
- `Controller/Decoder/Paths.lean`: the small path semantics beneath the equivalence.

The first two files currently have 770 and 3,039 lines respectively. The exact hashes, protected-file identities, import observations and registration pins are in [reuse-audit.json](reuse-audit.json). The current graph code has no implemented residual-kernel/threshold-scheduler proof for the published Theorem 3.2.

## Historical evidence, not a fresh replay

`../formalization/evidence/iteration-001/FailureBatch149-result.json` records a successful Lean 4.33 owner build and selected axiom audit. Its recorded source hashes match the current two graph files. The 182-line audit log reports only the usual `propext`, `Classical.choice`, and `Quot.sound` axioms on its selected declarations; this is not a fresh transitive whole-paper audit.

The nearby `FailureBatch148-result.json` is a failed build with a different `FailureBatch.lean` hash. It is explicitly excluded from successful evidence. Neither the existence of an audit file nor a matching filename counts as a pass.

No Lean build was run during this planning pass. The legacy package/build cache is absent, its environment is Lean 4.33, and its Git tree already contains substantial unrelated changes. Preserve it. The new plan neither resets it nor upgrades it in place.

## What may be extracted

PB8.1 can reuse the small semantic cone for Lemma 2.1 and Proposition 2.2 after porting and literal comparison. Reindex decreasing legacy ranks without reversing edges. Resolve differences between common failure masks, distinct versus listed incidences, empty batches and terminal duplicates.

Some existing `...operations` theorems count logical construction steps. The indexed/array snapshot wrappers explicitly do not assign a RAM construction cost. Reuse the semantic identity, then prove the missing implementation/refinement bridge where the published claim says linear time. Do not import the entire `Controller.Cost` framework merely because a semantic file currently imports it.

Do not port every old task or count every old theorem. Copy or import only a checked prerequisite of an approved consumer. New graph-only roots should not depend on physical controllers or unrelated Paper A reductions.

## Published Paper A registrations

The live records retrieved for this plan identify separate immutable source commits in `shaikidris/priority-controller-phase1`:

- [PALOMAR-2026-10-19-000010 v1](https://data.palomar-registry.org/entries/PALOMAR-2026-10-19-000010-v1.json): physical image/detection roots at `f4c18653ccc2590ff6d2fe7ca2ff1d904d62681d`.
- [PALOMAR-2026-10-19-000014 v1](https://data.palomar-registry.org/entries/PALOMAR-2026-10-19-000014-v1.json): guarded detector/cold execution and extension roots at `fc703dd3415e3a892536c0b624bf65b1ade2871d`.
- [PALOMAR-2026-10-20-000015 v1](https://data.palomar-registry.org/entries/PALOMAR-2026-10-20-000015-v1.json): dual-Horn and graph-cover roots at `4defc1bfee6f82a50c5d48e6ad4fe6e01df73cc0`.

Exact selected declarations are enumerated in the machine-readable audit. These registrations use Lean 4.35.0-rc3 and Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`. The public catalog was loaded, and the records were checked directly. The moving public `main` head could not be verified because the GitHub API returned HTTP 403; no head identity is assumed.

A verified registry record establishes its recorded result and source identity. This pass did not download/rebuild each complete registered source cone. Before literal proof reuse, fetch or inspect that exact source and selected declarations, compare the paper interface, preserve licences, and replay in the chosen supported environment.

Previously registered project code is not an allowed Challenge import. It may be a pinned Solution dependency or an audited substantive port. The first graph-only release needs neither option; the controller application is a later task.
