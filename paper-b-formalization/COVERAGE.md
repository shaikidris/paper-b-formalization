# Paper B draft coverage

Pinned active source: v1.1 draft, not published. The preserved public base is v1.0, DOI 10.5281/zenodo.24142496. These are proof obligations, not formal-verification claims. REUSE_CANDIDATE identifies relevant earlier code, not whole-statement certification.

| Item | Statement | Formal status | Work packages | Claim facets |
|---|---|---|---|---|
| 2.1 | a positive terminal and its forbidden vertices ([source line 326](sources/paper-b-v1.1-draft.md#L326)) | REUSE_CANDIDATE | PB8.1 | semantic |
| 2.2 | offline sensitivity reachability ([source line 350](sources/paper-b-v1.1-draft.md#L350)) | REUSE_CANDIDATE | PB8.1, PB4.1 | semantic, operational, resources |
| 3.1 | recognized common-anchor batches ([source line 430](sources/paper-b-v1.1-draft.md#L430)) | NOT_YET_CERTIFIED | PB6.1, PB2.7 | semantic, operational, resources |
| 3.2 | threshold tradeoff for all-query batches ([source line 620](sources/paper-b-v1.1-draft.md#L620)) | NOT_YET_CERTIFIED | PB4.5, PB4.6, PB9.1, PB9.2 | semantic, operational, resources |
| 3.3 | exact sharing of historical query sets ([source line 813](sources/paper-b-v1.1-draft.md#L813)) | NOT_YET_CERTIFIED | PB5.3 | semantic, operational, resources |
| 4.1 | one guard occurrence per label ([source line 863](sources/paper-b-v1.1-draft.md#L863)) | NOT_YET_CERTIFIED | PB6.2 | semantic, operational, resources |
| 4.2 | localization after one deletion ([source line 924](sources/paper-b-v1.1-draft.md#L924)) | NOT_YET_CERTIFIED | PB6.3 | semantic |
| 4.3 | two-failure batch bound ([source line 965](sources/paper-b-v1.1-draft.md#L965)) | NOT_YET_CERTIFIED | PB6.4 | semantic, operational, resources |
| 4.4 | quadratic explicit updates on an easy batch ([source line 1150](sources/paper-b-v1.1-draft.md#L1150)) | NOT_YET_CERTIFIED | PB6.5 | semantic, operational, resources |
| 4.5 | streamed two-failure batches ([source line 1226](sources/paper-b-v1.1-draft.md#L1226)) | NOT_YET_CERTIFIED | PB6.7 | semantic, operational, resources |
| 4.6 | Hamiltonian DAGs ([source line 1405](sources/paper-b-v1.1-draft.md#L1405)) | NOT_YET_CERTIFIED | PB6.5 | semantic, operational, resources |
| 4.7 | constructed width bound ([source line 1464](sources/paper-b-v1.1-draft.md#L1464)) | NOT_YET_CERTIFIED | PB6.8, PB6.9 | semantic, operational, resources |
| 4.8 | weighted deletion-cover selection ([source line 1519](sources/paper-b-v1.1-draft.md#L1519)) | NOT_YET_CERTIFIED | PB6.10, PB6.11 | semantic, operational, resources |
| 5.1 | single-output triangle reduction ([source line 1593](sources/paper-b-v1.1-draft.md#L1593)) | NOT_YET_CERTIFIED | PB7.1, PB7.5 | semantic, operational, resources |
| 5.2 | triangle-only bound when `n <= G <= n^2` ([source line 1703](sources/paper-b-v1.1-draft.md#L1703)) | NOT_YET_CERTIFIED | PB7.1, PB7.5 | semantic, operational, resources, conditional_model_transfer |
| 5.3 | fixed polynomial regimes ([source line 1742](sources/paper-b-v1.1-draft.md#L1742)) | NOT_YET_CERTIFIED | PB7.2, PB7.5 | semantic, operational, resources, conditional_model_transfer |
| 5.4 | balanced algebraic transfer ([source line 1866](sources/paper-b-v1.1-draft.md#L1866)) | NOT_YET_CERTIFIED | PB7.6 | semantic, operational, resources, conditional_model_transfer |
| 5.5 | quadratic exponent for general word-RAM algorithms ([source line 1933](sources/paper-b-v1.1-draft.md#L1933)) | NOT_YET_CERTIFIED | PB7.4, PB7.5 | semantic, operational, resources, conditional_model_transfer |
| 5.6 | essentiality on admissible sets ([source line 1997](sources/paper-b-v1.1-draft.md#L1997)) | NOT_YET_CERTIFIED | PB7.4, PB7.5 | semantic, operational, resources, conditional_model_transfer |
| 5.7 | multiplicity–size trade-off ([source line 2055](sources/paper-b-v1.1-draft.md#L2055)) | NOT_YET_CERTIFIED | PB7.3, PB7.5 | semantic, operational, resources |
| 5.8 | exact selector capacity ([source line 2123](sources/paper-b-v1.1-draft.md#L2123)) | NOT_YET_CERTIFIED | PB8.5 | semantic, proved_external_input, finite_size_arithmetic |
| 6.1 | controller and native-encoding transfer ([source line 2206](sources/paper-b-v1.1-draft.md#L2206)) | NOT_YET_CERTIFIED | PB8.8 | semantic, operational, resources, pinned_application_transfer |
| 6.2 | sensitivity-parameterized detection ([source line 2263](sources/paper-b-v1.1-draft.md#L2263)) | OPEN_RESEARCH | open research | open question |
| A.1 | baseline decision and witness ([source line 2374](sources/paper-b-v1.1-draft.md#L2374)) | REUSE_CANDIDATE | PB8.2 | semantic, operational, resources |
| A.2 | bitset supports ([source line 2398](sources/paper-b-v1.1-draft.md#L2398)) | NOT_YET_CERTIFIED | PB8.2 | semantic, operational, resources |
| A.3 | algebraic healthy-zero algorithm ([source line 2438](sources/paper-b-v1.1-draft.md#L2438)) | NOT_YET_CERTIFIED | PB8.3 | semantic, operational, resources |
| B.1 | canonical two-vertex summary ([source line 2558](sources/paper-b-v1.1-draft.md#L2558)) | NOT_YET_CERTIFIED | PB8.4 | semantic, operational, resources |
| B.2 | same-vertex sparsification and a generic batch bound ([source line 2618](sources/paper-b-v1.1-draft.md#L2618)) | NOT_YET_CERTIFIED | PB8.4 | semantic, operational, resources |
| B.3 | listed queries as summary equalities ([source line 2679](sources/paper-b-v1.1-draft.md#L2679)) | NOT_YET_CERTIFIED | PB8.4 | semantic, operational, resources |
| C.1 | Kraft inequality and optimal guard cost ([source line 2731](sources/paper-b-v1.1-draft.md#L2731)) | NOT_YET_CERTIFIED | PB8.5 | semantic, proved_external_input, finite_size_arithmetic |
| D.1 | conditional quadratic exponent ([source line 2820](sources/paper-b-v1.1-draft.md#L2820)) | NOT_YET_CERTIFIED | PB8.6, PB8.7 | semantic, operational, resources, conditional_model_transfer |
| D.2 | joint bounds ([source line 2887](sources/paper-b-v1.1-draft.md#L2887)) | NOT_YET_CERTIFIED | PB8.7 | semantic, operational, resources, conditional_model_transfer |

E.1 and E.2 are representation examples assigned to PB5.4, outside the 32 numbered statements. Their finite instances do not establish a universal Boolean decision lower bound.

## Root obligations

These twelve architecture-level rows are the first-root burn-down. Exact Lean types are not yet frozen.

| Obligation | Paper root | Owner | Status | Consumer |
|---|---|---|---|---|
| O32.1 — Valid explicit input, every original query index and normalization answer preservation | 3.2 | graph | OPEN | Kernel and Scheduler |
| O32.2 — Constructed domination and indexing | 3.2 | graph | OPEN | Kernel proper-cut tests |
| O32.3 — Split network, bounded flow and rank-label construction | 3.2 | kernel | OPEN | Kernel target/cut exports |
| O32.4 — Proper-cut and arbitrary-target residual equivalences with construction cost | 3.2 | kernel | OPEN | Scheduler Resolve |
| O32.5 — Scheduler termination and every-index Boolean correctness | 3.2 | scheduler | OPEN | Solution correctness |
| O32.6 — Actual primitive execution and uniform computation model | 3.2 | resources | OPEN | Amortization and Resources |
| O32.7 — All-kernel retirement, stale YES/NO edge scans and once-per-query original-target charges | 3.2 | resources | OPEN | Solution time |
| O32.8 — Peak live words, answer vector/maps, threshold cap and word-size safety | 3.2 | resources | OPEN | Solution space |
| O32.9 — One fixed vector solver joined on the original input; OR as a derived projection | 3.2 | coordinator | OPEN | Theorem 3.2 three-declaration surface |
| O32.10 — Literal fidelity, trust, clean replay and independent comparison | 3.2 | reviewer | OPEN | Selected-root certification |
| O33.1 — Immutable exact dictionary with charged tuple operations | 3.3 | sharing | OPEN | Interned scheduler |
| O33.2 — Handle simulation and aggregate payload/time/space | 3.3 | sharing | OPEN | Proposition 3.3 surface |

## Structural extension obligations

These later obligations do not enlarge the first threshold release cone.

| Obligation | Paper item | Tasks | Status |
|---|---|---|---|
| O47.1 — Greedy max-uncovered path discovery and assigned chain partition | 4.7 | PB6.8 | OPEN |
| O47.2 — Full width-dependent time and space composition | 4.7 | PB6.9 | OPEN |
| O48.1 — Dual-feasible weighted cover with zero-weight and duplicate-edge cases | 4.8 | PB6.10 | OPEN |
| O48.2 — Fixed-tree region costs and weighted optimum batch bound | 4.8 | PB6.11 | OPEN |
