import PaperB.ForestBuiltQueryToll
import PaperB.StaticDfsLiveSpace
import PaperB.ForestInputPrepStorage
import PaperB.ForestNumericSweepSpace

set_option maxHeartbeats 2000000

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.Storage
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS PaperB.Jumps
open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open AggregateEX24

section Finish
variable {H : LabelledQuotient} {c : Config H}
variable {rank : Vertex H → Nat} {out : State H}
private def actualFinishRows (h : OutputOK c rank out) :=
  StaticGroupedTreeReader.finish_rows (packedInput h) (packedInput_ok h)

private def actualFinishInverse (h : OutputOK c rank out) :=
  StaticGroupedTreeReader.finish_inverse (packedInput h) (packedInput_ok h)

private def measured {a b : Nat} (_ : a = b) : Nat := a

private def proofType {P : Prop} (_ : P) : Prop := P

end Finish

private theorem certificateCover (H : LabelledQuotient) :
    ForestIncomingPrep.Cover H := by
  intro u y
  rfl

private def boundLeft {a b : Nat} (_ : a ≤ b) : Nat := a
private def boundRight {a b : Nat} (_ : a ≤ b) : Nat := b

-- Select the real hand-off charge, including the immutable charge with
-- `other = data.size`. The RHS is immutableUnits H data.size + (5*n + 7*m).
private def prepHandOffCells (H : LabelledQuotient) (other : Nat) : Nat :=
  boundLeft
    (PaperB.EX24.InputPrepCheckpoint.build_receipt
      H (certificateCover H) other).2.2

private def prepHandOffCap (H : LabelledQuotient) (other : Nat) : Nat :=
  boundRight
    (PaperB.EX24.InputPrepCheckpoint.build_receipt
      H (certificateCover H) other).2.2

-- These selectors avoid naming the collection implementation or the sorting
-- trace's namespace. The first selects `(collect p orderedPairCode).length`;
-- the second selects `Calls ... f` from the actual space theorem.
private def dictionaryInputKeys {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) : Nat :=
  boundLeft (ForestDictionary.packedDictionary_construction_space
    p orderedPairCode 1).1

private def frameTraceOf {C D S : Nat → Prop}
    (_ : ∃ f : Nat, C f ∧ D f ∧ S f) (f : Nat) : Prop :=
  C f

private def dictionaryFrameTrace {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (f : Nat) : Prop :=
  frameTraceOf (ForestDictionary.packedDictionary_construction_space
    p orderedPairCode 1).2.2.2.2.2.2.2.2.2 f

-- Collected list, setup array, zero array, shared bank, return slice,
-- and one logical cell per live sorting frame. The initial and outgoing
-- bank states are not counted as two separate logical banks.
private def dictionarySortCells {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (f : Nat) : Nat :=
  let k := dictionaryInputKeys p
  k + k + k + 2 * k +
    (ForestDictionary.packedDictionary p orderedPairCode).size + f

-- The two occurrence charges are kept separate: one supplied occurrence
-- charge and one actual dedup visit. Neither is a count of all EX51 work.
private def buildOperationSites
    (reads compares supplied visits residual dictionary finish : Nat) : Nat :=
  (((reads + compares + supplied + visits) + residual) + dictionary) + finish

-- Only the row/child scan slots and inverse list cells selected below.
-- In particular this is NOT the grouped finish workspace. The exact DFS,
-- row, and inverse contracts are carried separately in the certificate.
private def finishSelectedCells
    {H : LabelledQuotient} {cfg : Config H}
    {rank : Vertex H → Nat} {out : State H}
    (h : OutputOK cfg rank out) : Nat :=
  let hr := actualFinishRows h
  let hi := actualFinishInverse h
  measured hr.1 + measured hr.2.1 + measured hr.2.2.1 +
    measured hi.2.2.1

section FinishResourceGap

variable {H : LabelledQuotient} {cfg : Config H}
variable {rank : Vertex H → Nat} {out : State H}

private theorem finishSelectedCells_le_occupied
    (h : OutputOK cfg rank out) :
    finishSelectedCells h ≤ 4 * nodeCount cfg out := by
  let hr := actualFinishRows h
  let hi := actualFinishInverse h
  have hrows : measured hr.1 = nodeCount cfg out := hr.1
  have hchildren : measured hr.2.1 = nodeCount cfg out - 1 := hr.2.1
  have hranges : measured hr.2.2.1 = nodeCount cfg out := hr.2.2.1
  have hlist : measured hi.2.2.1 = nodeCount cfg out := hi.2.2.1
  change measured hr.1 + measured hr.2.1 + measured hr.2.2.1 +
      measured hi.2.2.1 ≤ 4 * nodeCount cfg out
  simp only [hrows, hchildren, hranges, hlist]
  omega

private theorem finishSelectedCells_le
    (h : OutputOK cfg rank out) :
    finishSelectedCells h ≤ 4 * (H.vertexCount + 1) := by
  have hf := finishSelectedCells_le_occupied h
  have hn := nodeCount_le h
  omega

end FinishResourceGap

namespace StaticGroupedTreeReader

open ForestLayout ForestHeavyPath LabelledQuotient StaticHeadSweep
open ForestLayout.LiveCells

private def finishScatterField : GroupedChildWork → Nat
  | ⟨_, ⟨_, k, _, _, _⟩⟩ => k

/-- One toll unit per recorded scatter in the deployed stable grouping.
This does not charge enumeration, initialization, or row finalization. -/
def finishChildScatterSites {N : Nat} (x : PackedStaticLayout.Input N) : Nat :=
  finishScatterField (groupedChildLists x.root x.parent.read).2

private theorem finishChildScatterSites_eq {N : Nat}
    (x : PackedStaticLayout.Input N) :
    finishChildScatterSites x = N - 1 := by
  have h := congrArg finishScatterField
    (groupedChildLists_work x.root x.parent.read)
  change finishScatterField (groupedChildLists x.root x.parent.read).2 = N - 1
  exact h

/-- Selected phase resources for the deployed grouped finish. The bucket
equality specifies stable row order; it does not execute the reference build.

The grouping cell bound is for the materialized table at DFS handoff.
`PrefixLive` keeps its existing DFS cell model. The inverse cell bound
reserves both the array and its list conversion; its toll charges one entry
read and one inverse write per scatter, excluding fill.

These are phase-local bounds, not a whole-finish peak. They do not reserve
transient grouping workspace, packed-input extraction or retained input/word
storage, or the other reader roots across phases (endpoints outside the DFS
charge, size/heavy tables, sweep/head state, and completed range rows).
Allocation and copying overhead are not counted. -/
theorem finish_grouped_phase_resources {N : Nat}
    (x : PackedStaticLayout.Input N) (ht : PackedStaticLayout.InputOK x)
    (tree : ValidDepthTree x.root x.parent.read x.depth.read) :
    let b := (build x ht).layout
    let g := b.buckets
    let m := childScanLength g
    let hi := finish_inverse x ht
    let writes := measured hi.1
    let arrayCells := measured hi.2.1
    let listCells := measured hi.2.2.1
    g = bucketChildLists x.root x.parent.read ∧
    finishChildScatterSites x = N - 1 ∧
    finishChildScatterSites x ≤ N ∧
    g.rows.size + m ≤ 2 * N ∧
    boundaryCells g m (initial x.root) ≤ 4 * N + 1 ∧
    (let s := layout g x.root (2 * N)
     s.stack = [] ∧ s.processed = 2 * N ∧
       b.endpoints.entry.data = s.entries ∧
       b.endpoints.stop.data = s.ends) ∧
    b.endpoints.entry.data.size + b.endpoints.stop.data.size = 2 * N ∧
    (∀ k : Nat, k ≤ 2 * N → PrefixLive g x.root m k) ∧
    (arrayCells = N ∧ listCells = N ∧ arrayCells + listCells = 2 * N) ∧
    (writes = N ∧ writes + writes = 2 * N) := by
  dsimp only
  have hg : (build x ht).layout.buckets =
      bucketChildLists x.root x.parent.read := by
    change (groupedChildLists x.root x.parent.read).1 =
      bucketChildLists x.root x.parent.read
    rw [groupedChildLists_eq_bucketChildLists]
  have hs := finishChildScatterSites_eq x
  have hs_le : finishChildScatterSites x ≤ N := by omega
  obtain ⟨_, _, hgroup, hinit, hdone, hend, hprefix⟩ :=
    finish_dfs_liveCells x ht tree
  let hi := finish_inverse x ht
  have hw : measured hi.1 = N := hi.1
  have ha : measured hi.2.1 = N := hi.2.1
  have hl : measured hi.2.2.1 = N := hi.2.2.1
  refine ⟨hg, hs, hs_le, hgroup, hinit, hdone, hend, hprefix, ?_, ?_⟩
  · refine ⟨ha, hl, ?_⟩
    change measured hi.2.1 + measured hi.2.2.1 = 2 * N
    rw [ha, hl] <;> omega
  · refine ⟨hw, ?_⟩
    change measured hi.1 + measured hi.1 = 2 * N
    rw [hw] <;> omega

end StaticGroupedTreeReader

-- A conservative peak envelope for the selected roots: reserve every term
-- even across phase boundaries. This does not require an early-release or
-- no-aliasing theorem, and may count the same logical data more than once.
private def coveredRootSum
    (prep dictionary sweep finish retained : Nat) : Nat :=
  prep + dictionary + sweep + finish + retained

/--
Certificate for the specified sites and checkpoints of the same `build`.

The large branch identifies the installed reader and its exact grouped
callback. Work witnesses are all for that reader's output and log. Storage
includes prep receipts, the dictionary sort after collection, sweep
checkpoints with a reversal reserve, selected finish slots, and the actual
returned index's retained arrays. The small branch returns no retained index;
it does not assert that the prep let, which precedes the branch, is free.
-/
theorem build_checkpoint_certificate
    {H : LabelledQuotient}
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat)
    [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    let prep := ForestIncomingPrep.build H (certificateCover H)
    let p := prep.tests
    let b := ForestPreparedBuild.build
      data size_data rank increasing covers rankArc flat
    (∀ (q : CutPair H) (v : Vertex H),
      QuotientMembership.Index.contains b q v = true ↔
        q.fst < q.snd ∧ H.ProperLoss q v) ∧
    QuotientMembership.Index.arraySize b ≤ 9 * H.vertexCount ∧
    proofType (PaperB.EX24.InputPrepCheckpoint.build_receipt
      H (certificateCover H) data.size) ∧
    proofType (PaperB.EX24.InputPrepCheckpoint.dedup_row_boundary_receipt H) ∧
    proofType (PaperB.EX24.InputPrepCheckpoint.dedup_prefix_receipt H) ∧
    (if large : 3 ≤ H.vertexCount then
      let c := orderedConfig p large
      let rows := orderedRows p data size_data
      let s := initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
      let L := OracleContract.L H.vertexCount
      let r := runOrderedReaderFast p data size_data rank large
        increasing covers rankArc flat
      b = some (RetainedProperLoss.ofOrderedReader r) ∧
      r = runOrderedReaderPacked p data size_data rank large
        increasing covers rankArc flat
        (fun {c} {out} h => buildGrouped (c := c) (out := out) h)
        (fun {c} {out} h => buildGrouped_eq (c := c) (out := out) h) ∧
      (∀ {todo : List (Row H)} {t : State H} {rev : Log H} {k : Nat},
        Visit c rank rows s [] todo t rev k →
        checkpointCells c data rows t rev ≤
          10 * H.vertexCount + H.arcCount + 5 ∧
        checkpointCells c data rows t rev + H.vertexCount ≤
          11 * H.vertexCount + H.arcCount + 5) ∧
      proofType (ForestDictionary.packedDictionary_construction_space
        p orderedPairCode 1) ∧
      ∃ (q : Nat) (cnt : Count) (w : AggregateEX24.Work) (qs : List (CutPair H))
          (a d sortCost total frames : Nat),
        runOrdered p data size_data rank large = some (r.out, r.log) ∧
        PackedReads.packedReadSum c rank s rows = some q ∧
        CountedTrace c rank s rows r.out r.log cnt ∧
        WorkTrace c rank s rows r.out r.log cnt w ∧
        AggregateEX24.Bounds L rows cnt w ∧
        PairLookupTrace c rank s rows r.out r.log cnt w qs ∧
        qs.length = w.requests ∧
        prep.visits = H.arcCount ∧
        ResidualUnit.AppendTrace c rank s rows r.out r.log cnt a d ∧
        d = cnt.allocations ∧ a ≤ 14 * d ∧
        ForestDictionary.PackedDictionaryConstructionTrace p orderedPairCode
          (packedOrderedConfig p large).dict sortCost total ∧
        total ≤ 34 * H.vertexCount * (L + 1) ∧
        dictionaryFrameTrace p frames ∧
        frames ≤ ceilBinaryLog (dictionaryInputKeys p) + 1 ∧
        dictionarySortCells p frames ≤ 7 * (H.vertexCount + 1) ∧
        (∀ {cfg : Config H} {out : State H} (h : OutputOK cfg rank out),
          ChargedGroupedFinishFacts h ∧
          buildOperationSites q (pairLookupComparisons c qs)
            H.arcCount prep.visits (ResidualUnit.toll L cnt w a)
            total (chargedGroupedFinish h) ≤
            (90 * (H.vertexCount + H.arcCount) * L ^ 2 +
              34 * H.vertexCount * (L + 1)) + 11 * (H.vertexCount + 1) ∧
          (∀ {todo : List (Row H)} {t : State H} {rev : Log H} {k : Nat},
            Visit c rank rows s [] todo t rev k →
            coveredRootSum
              (prepHandOffCells H data.size)
              (dictionarySortCells p frames)
              (checkpointCells c data rows t rev + H.vertexCount)
              (finishSelectedCells h)
              (QuotientMembership.Index.arraySize b) ≤
            coveredRootSum
              (prepHandOffCap H data.size)
              (7 * (H.vertexCount + 1))
              (11 * H.vertexCount + H.arcCount + 5)
              (finishSelectedCells h)
              (9 * H.vertexCount)))
    else
      b = none ∧ QuotientMembership.Index.arraySize b = 0) := by
  intro prep p b
  have hquery := ForestPreparedBuild.query_iff
    data size_data rank increasing covers rankArc flat
  have hret : QuotientMembership.Index.arraySize b ≤ 9 * H.vertexCount :=
    ForestPreparedBuild.arraySize_le data size_data rank
      increasing covers rankArc flat
  have hprep := PaperB.EX24.InputPrepCheckpoint.build_receipt
    H (certificateCover H) data.size
  refine ⟨hquery, hret, hprep,
    PaperB.EX24.InputPrepCheckpoint.dedup_row_boundary_receipt H,
    PaperB.EX24.InputPrepCheckpoint.dedup_prefix_receipt H, ?_⟩
  by_cases large : 3 ≤ H.vertexCount
  · rw [dite_eq_left large]
    intro c rows s L r
    have hb : b = some (RetainedProperLoss.ofOrderedReader r) := by
      change ForestPreparedBuild.build
        data size_data rank increasing covers rankArc flat = _
      rw [ForestPreparedBuild.build, dite_eq_left large]
    -- The cover arguments are proofs of the same Prop. Consequently the
    -- prep in these reader theorems and the prep in hb are definitionally
    -- equal; no replacement of the rows or re-running on another H is used.
    have hprefix := @runOrderedReaderFast_prepared_prefix_storage
      H data size_data rank large _ increasing covers
    obtain ⟨hr, q, cnt, w, qs, a, d, sortCost, total,
        hrun, hread, hcnt, hwork, hbounds, hlookup, hlen, hvisits,
        happend, hd, ha, hdict, htotal, _, hfinish⟩ :=
      runOrderedReaderFast_prepared_chargedSites
        data size_data rank large increasing covers rankArc flat
    have hspace := ForestDictionary.packedDictionary_construction_space
      p orderedPairCode 1
    have hspaceCopy := hspace
    obtain ⟨_, hbank0, hzeros, _, hbank, _, _, _, _,
        frames, hframes, hdepth, hspaceBound⟩ := hspaceCopy
    have hsortCells : dictionarySortCells p frames ≤
        7 * (H.vertexCount + 1) := by
      unfold dictionarySortCells dictionaryInputKeys boundLeft
      simpa only [hbank0, hzeros, hbank, Nat.one_mul, Array.size_replicate, show 6 + 1 = 7 by rfl] using hspaceBound
    refine ⟨hb, hr, hprefix, hspace,
      q, cnt, w, qs, a, d, sortCost, total, frames,
      hrun, hread, hcnt, hwork, hbounds, hlookup, hlen, hvisits,
      happend, hd, ha, hdict, htotal, hframes, hdepth, hsortCells, ?_⟩
    intro cfg out h
    obtain ⟨hfinishFacts, hsites⟩ := hfinish h
    have hv : prep.visits = H.arcCount := hvisits
    refine ⟨hfinishFacts, ?_, ?_⟩
    · simpa only [buildOperationSites, hv] using hsites
    · intro todo t rev k hvisit
      have hsweep : checkpointCells c data rows t rev + H.vertexCount ≤
          11 * H.vertexCount + H.arcCount + 5 :=
        (hprefix hvisit).2
      have hp : prepHandOffCells H data.size ≤ prepHandOffCap H data.size :=
        hprep.2.2
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hp hsortCells) hsweep)
          (Nat.le_refl (finishSelectedCells h)))
        hret
  · rw [dite_eq_right large]
    have small : H.vertexCount < 3 := by omega
    have hb : b = none :=
      ForestPreparedBuild.build_of_small
        data size_data rank increasing covers rankArc flat small
    exact ⟨hb, by rw [hb]; rfl⟩

/-
Unclosed obligations; none is hidden in coveredRootSum.

* Input prep: build_receipt identifies p.row with the dedup rows at hand-off
  and gives the actual visits. The prefix receipt still has its own premises:
  y ∉ done and seen ++ todo = sources.read y. To claim a phase-wide bound,
  instantiate those premises on every reached cursor of the actual run and
  bound the work arrays and live list roots of the preceding EX51 scatter.
  A hand-off receipt alone does not establish either of those claims.

* Dictionary: the operation trace names the installed dict. The space trace
  names packedDictionary p orderedPairCode and starts at its collected list.
  To transport the return-slice charge to the installed array, expose
      (packedOrderedConfig p large).dict =
        ForestDictionary.packedDictionary p orderedPairCode
  or the corresponding equality of backing arrays if the field is wrapped.
  To include collection from p.ordered, supply a reached-prefix invariant
  for its actual collector: identify the consumed prefix and remaining suffix,
  bound the accumulator by the consumed prefix, and count simultaneous input,
  accumulator, and output roots at the hand-off. The sorting theorem does
  not bound that workspace.

* Grouped finish: the certificate names the actual callback, and its finish
  contracts apply on that callback's own packedInput h and packedInput_ok h.
  It does not assert that the selected scan slots are the DFS workspace.
  The missing connection is the public prefix-space contract on
      x := packedInput h
      ht := packedInput_ok h
      g := (StaticGroupedTreeReader.build x ht).layout.buckets
  with the actual childMass of buildLayout_childScanLength x. In particular,
  for each k ≤ 2*N it must give PrefixLive g x.root childMass k on the
  actual layout cursor, and expose the inequality on boundaryCells at that
  cursor. The trailing proof shows how validTree_prefix is used, but does
  not give the theorem header or the fields of PrefixLive. Even that DFS
  bound would not by itself bound the preceding bucket scatter or inverse
  construction: those need bounds on their actual work roots during the
  writes, not just the final sizes and scan lengths. Inverse fill is also
  outside chargedGroupedFinish.

* Query: query_iff here is for the exported Index.contains on the actual
  returned b. No Index.query wrapper is shown. A cost theorem for a lookup
  given a known node/key is not a cost theorem for this call: it needs a
  trace identifying the actual retained-array lookup with that primitive,
  and charges for finding the node/key or handling a miss. No supplied
  estimate is used as a substitute for that trace.
-/

end PaperB

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.Storage
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS PaperB.Jumps
open PaperB.PairLookup PaperB.PairLookup.KeyMerge AggregateEX24

namespace ForestSourceExecution

open _root_.EX51 _root_.EX51.Storage ForestLayout ForestHeavyPath StaticHeadSweep
open StaticGroupedTreeReader (childScanLength)
open ForestLayout.LiveCells

/-- A valid-index array read has one source probe. Finding the index is
not part of this operation. -/
def readKnown {α : Type _} (a : Array α) (i : Fin a.size) : α × Nat :=
  (a[i.val]'i.isLt, 1)

/-- Logical roots at the indicated call boundaries of stable child grouping.
The active row reversal is charged in addition to the old table. -/
inductive GroupingCellsAt {n : Nat} (root : Fin n) (parent : Fin n → Fin n) :
    Nat → Prop where
  | enumerate : GroupingCellsAt root parent
      (boundLeft (groupedChildLists_enumeration_space (N := n) 0).2)
  | filter {unread acc : List (Fin n)} {k : Nat} :
      SelectNonRootAt root unread acc k →
      GroupingCellsAt root parent (unread.length + acc.length)
  | scatter {unread : List (Fin n)} {s : Rows n (Fin n)} {r w : Nat} :
      ScatterAt parent id (groupedChildInput root) unread s r w →
      GroupingCellsAt root parent
        (s.cells.size + rowMass s + (groupedChildInput root).length)
  | finish {s : Rows n (Fin n)} {t c : Nat} {ht : t ≤ n} :
      FinishAt (scatterRows parent id (groupedChildInput root)) t ht s c →
      GroupingCellsAt root parent
        (s.cells.size + rowMass s + (groupedChildInput root).length)
  | reverseRow {s : Rows n (Fin n)} {t c charge : Nat} {ht : t + 1 ≤ n}
      {unread acc : List (Fin n)} :
      FinishAt (scatterRows parent id (groupedChildInput root)) (t + 1) ht s c →
      ReverseAt (s.row ⟨t, ht⟩) c unread acc charge →
      GroupingCellsAt root parent
        (s.cells.size + rowMass s + (groupedChildInput root).length +
          (acc.length + unread.length))

private theorem groupingCellsAt_le {n : Nat} {root : Fin n}
    {parent : Fin n → Fin n} {cells : Nat}
    (atCall : GroupingCellsAt root parent cells) :
    cells ≤ groupedChildListsPeak n 0 := by
  cases atCall with
  | enumerate => exact (groupedChildLists_enumeration_space (N := n) 0).2
  | filter h =>
      simpa only [Nat.zero_add] using (groupedChildLists_filter_space h 0).2.2
  | scatter h =>
      simpa only [Nat.zero_add] using
        (groupedChildLists_scatter_space root parent h 0).2.2.2
  | finish h =>
      simpa only [Nat.zero_add] using
        (groupedChildLists_finish_space root parent h 0).2.2.2
  | reverseRow h₁ h₂ =>
      simpa only [Nat.zero_add] using
        (groupedChildLists_reversal_space root parent h₁ h₂ 0).2.2

private def buckets {n : Nat} (x : PackedStaticLayout.Input n)
    (ht : PackedStaticLayout.InputOK x) :=
  (StaticGroupedTreeReader.build x ht).layout.buckets

/-- Phase-local charges for the installed grouped reader, not for the
reference bucket build. The inverse case reserves both output forms. -/
inductive FinishCellsAt {n : Nat} (x : PackedStaticLayout.Input n)
    (ht : PackedStaticLayout.InputOK x) : Nat → Prop where
  | grouping {cells : Nat} :
      GroupingCellsAt x.root x.parent.read cells → FinishCellsAt x ht cells
  | handoff : FinishCellsAt x ht
      ((buckets x ht).rows.size + childScanLength (buckets x ht))
  | dfs (k : Nat) : k ≤ 2 * n → FinishCellsAt x ht
      (boundaryCells (buckets x ht) (childScanLength (buckets x ht))
        (layout (buckets x ht) x.root k))
  | endpoints : FinishCellsAt x ht
      ((StaticGroupedTreeReader.build x ht).layout.endpoints.entry.data.size +
       (StaticGroupedTreeReader.build x ht).layout.endpoints.stop.data.size)
  | inverse : FinishCellsAt x ht
      (let hi := StaticGroupedTreeReader.finish_inverse x ht
       measured hi.2.1 + measured hi.2.2.1)

section Finish

variable {H : LabelledQuotient} {cfg : Config H}
variable {rank : Vertex H → Nat} {out : State H}

private theorem finishTree (h : OutputOK cfg rank out) :
    let x := packedInput h
    ValidDepthTree x.root x.parent.read x.depth.read := by
  dsimp only
  have ht := packedInput_ok h
  first
  | exact ht
  | exact ht.tree
  | exact ht.validTree
  | exact ht.1
  | exact ht.2
  | exact?
  | (cases ht <;> solve_by_elim)
  | (unfold PackedStaticLayout.InputOK at ht; grind)

private def phaseReceipt (h : OutputOK cfg rank out) :=
  StaticGroupedTreeReader.finish_grouped_phase_resources
    (packedInput h) (packedInput_ok h) (finishTree h)

/-- A separate allowance for grouping scatters, completed DFS events, and
the entry read and inverse write at each inverse scatter. This allowance
may overlap sites already in `chargedGroupedFinish`. -/
def finishPhaseSites (h : OutputOK cfg rank out) : Nat :=
  let x := packedInput h
  let g := buckets x (packedInput_ok h)
  let writes := measured (actualFinishInverse h).1
  StaticGroupedTreeReader.finishChildScatterSites x +
    (layout g x.root (2 * nodeCount cfg out)).processed + (writes + writes)

private theorem finishPhaseSites_le (h : OutputOK cfg rank out) :
    finishPhaseSites h ≤ 5 * (H.vertexCount + 1) := by
  have hp := phaseReceipt h
  dsimp only at hp
  obtain ⟨_, _, hscatter, _, _, hdfs, _, _, _, hinv⟩ := hp
  have hd := hdfs.2.1
  have hi := hinv.2
  have hn := nodeCount_le h
  unfold finishPhaseSites buckets
  dsimp only
  omega

private theorem finishCellsAt_le (h : OutputOK cfg rank out) {cells : Nat}
    (atCall : FinishCellsAt (packedInput h) (packedInput_ok h) cells) :
    cells ≤ 32 * nodeCount cfg out + 8 := by
  have hp := phaseReceipt h
  dsimp only at hp
  obtain ⟨_, _, _, htable, _, _, hend, hprefix, hinv, _⟩ := hp
  cases atCall with
  | grouping hg =>
      have hb := groupingCellsAt_le hg
      unfold groupedChildListsPeak at hb
      omega
  | handoff =>
      unfold buckets
      omega
  | dfs k hk =>
      have hb := hprefix k hk
      unfold buckets
      first
      | (unfold PrefixLive at hb; dsimp only at hb; grind)
      | (cases hb; dsimp only at *; omega)
      | (cases hb; grind [boundaryCells])
      | (unfold PrefixLive at hb; dsimp only at hb; grind [boundaryCells])
  | endpoints => omega
  | inverse =>
      have hi := hinv.2.2
      dsimp only
      omega

end Finish

private theorem prepCells_le {H : LabelledQuotient}
    (data : Array (Vertex H)) (hs : data.size = H.vertexCount) :
    prepHandOffCells H data.size ≤ 64 * (H.vertexCount + H.arcCount) := by
  apply Nat.le_trans
    (PaperB.EX24.InputPrepCheckpoint.build_receipt
      H (certificateCover H) data.size).2.2
  rw [hs]
  unfold PaperB.EX24.InputPrepCheckpoint.immutableUnits
  rw [H.adj_size]
  omega

private theorem one_le_log (n : Nat) : 1 ≤ OracleContract.L n := by
  exact OracleContract.one_le_L n

private theorem uniformSites {n e l : Nat} (hn : 1 ≤ n) (hl : 1 ≤ l) :
    (90 * (n + e) * l ^ 2 + 34 * n * (l + 1)) + 11 * (n + 1) +
      5 * (n + 1) ≤ 200 * (n + e) * l ^ 2 := by
  have hl₂ : l ≤ l ^ 2 := by
    simpa only [Nat.mul_one, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using Nat.mul_le_mul_left l hl
  have hbase : n + e ≤ (n + e) * l ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n + e) (Nat.le_trans hl hl₂)
  have hdict : n * (l + 1) ≤ 2 * ((n + e) * l ^ 2) := calc
    _ ≤ (n + e) * (2 * l ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ = _ := Nat.mul_left_comm _ _ _
  simp only [Nat.mul_assoc]
  omega

/--
Source-site and logical-cell certificate for the exported build. The prep
visit and handoff charges apply also when the result is `none`; the theorem
does not require the compiler to preserve or eliminate that prep evaluation.

The build-site sum counts the packed reads, pair comparisons, supplied
occurrences, dedup visits, residual toll, dictionary construction trace,
grouped finish toll, and the explicit finish phase allowance. No build
operations outside those selectors are charged: in particular this is not
an EX51 prep-scatter toll, an inverse-fill toll, or a toll for allocation,
copying, arbitrary rank evaluation, or scalar and control operations.
The counted query is the exported probe trace; the known-slot read does not
charge slot discovery.

The live inequality reserves the indicated roots even across phases.
It covers prep handoff (including its immutable charge), not the preceding
EX51 scatter or an all-reached-cursors prep peak. The dedup receipts retain
their premises. The dictionary space charge starts at the collected list.
The finish charge covers the enumerator, filter, scatter, row finalization
and active row reversal boundaries, DFS boundaries, and the indicated
outputs. It does not reserve a separate selector-output reversal workspace,
packed-input extraction or retained input/word storage, size/heavy or
head-sweep roots, or other simultaneous reader roots not in the selected
sum. The inverse charge is a reserve for the array and list outputs, not a
trace of fill or conversion prefixes. No allocator, copying, or fixed-VM
peak is asserted.
-/
theorem build_certificate
    {H : LabelledQuotient}
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat)
    [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    let N := H.vertexCount
    let E := H.arcCount
    let L := OracleContract.L N
    let prep := ForestIncomingPrep.build H (certificateCover H)
    let p := prep.tests
    let b := ForestPreparedBuild.build
      data size_data rank increasing covers rankArc flat
    (∀ (q : CutPair H) (v : Vertex H),
      let z := QuotientMembership.Index.containsCounted b q v
      z.1 = QuotientMembership.Index.contains b q v ∧
      (z.1 = true ↔ q.fst < q.snd ∧ H.ProperLoss q v) ∧
      z.2 ≤ 10 * L) ∧
    QuotientMembership.Index.arraySize b ≤ 9 * N ∧
    (∀ (s : RetainedProperLoss.Columns H), b = some s →
      ∀ i : Fin s.dict.size,
        (readKnown s.dict i).1 = s.dict[i.val]'i.isLt ∧
        (readKnown s.dict i).2 = 1) ∧
    prep.visits = E ∧ E + prep.visits ≤ 200 * (N + E) * L ^ 2 ∧
    prepHandOffCells H data.size ≤ 64 * (N + E) ∧
    proofType (PaperB.EX24.InputPrepCheckpoint.dedup_row_boundary_receipt H) ∧
    proofType (PaperB.EX24.InputPrepCheckpoint.dedup_prefix_receipt H) ∧
    (if large : 3 ≤ N then
      let c := orderedConfig p large
      let rows := orderedRows p data size_data
      let s := initial c (ConcreteInit.initImage N).1 N
      let r := runOrderedReaderFast p data size_data rank large
        increasing covers rankArc flat
      b = some (RetainedProperLoss.ofOrderedReader r) ∧
      r = runOrderedReaderPacked p data size_data rank large
        increasing covers rankArc flat
        (fun {c} {out} h => buildGrouped (c := c) (out := out) h)
        (fun {c} {out} h => buildGrouped_eq (c := c) (out := out) h) ∧
      ∃ (q : Nat) (cnt : Count) (w : AggregateEX24.Work) (qs : List (CutPair H))
          (a d sortCost total frames : Nat),
        runOrdered p data size_data rank large = some (r.out, r.log) ∧
        PackedReads.packedReadSum c rank s rows = some q ∧
        CountedTrace c rank s rows r.out r.log cnt ∧
        WorkTrace c rank s rows r.out r.log cnt w ∧
        PairLookupTrace c rank s rows r.out r.log cnt w qs ∧
        ResidualUnit.AppendTrace c rank s rows r.out r.log cnt a d ∧
        (packedOrderedConfig p large).dict =
          ForestDictionary.packedDictionary p orderedPairCode ∧
        ForestDictionary.PackedDictionaryConstructionTrace p orderedPairCode
          (packedOrderedConfig p large).dict sortCost total ∧
        dictionaryFrameTrace p frames ∧
        (∀ {cfg : Config H} {out : State H} (h : OutputOK cfg rank out),
          ChargedGroupedFinishFacts h ∧
          proofType (actualFinishRows h) ∧ proofType (actualFinishInverse h) ∧
          proofType (phaseReceipt h) ∧
          buildOperationSites q (pairLookupComparisons c qs)
            E prep.visits (ResidualUnit.toll L cnt w a) total
            (chargedGroupedFinish h) + finishPhaseSites h ≤
              200 * (N + E) * L ^ 2 ∧
          (∀ {todo : List (Row H)} {t : State H} {rev : Log H} {k cells : Nat},
            Visit c rank rows s [] todo t rev k →
            FinishCellsAt (packedInput h) (packedInput_ok h) cells →
            coveredRootSum
              (prepHandOffCells H data.size) (dictionarySortCells p frames)
              (checkpointCells c data rows t rev + N)
              (finishSelectedCells h + cells)
              (QuotientMembership.Index.arraySize b) ≤ 160 * (N + E)))
    else
      b = none ∧ QuotientMembership.Index.arraySize b = 0) := by
  intro N E L prep p b
  obtain ⟨hquery, hret, hprep, hrow, hdedup, hbranch⟩ :=
    build_checkpoint_certificate data size_data rank increasing covers rankArc flat
  have hvis : prep.visits = E := by
    first
    | exact hprep.1
    | exact hprep.2.1
    | exact hprep.1.symm
    | exact hprep.2.1.symm
  have hpc := prepCells_le data size_data
  have hl : 1 ≤ L := one_le_log N
  have hl₂ : L ≤ L ^ 2 := by
    simpa only [Nat.mul_one, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using Nat.mul_le_mul_left L hl
  have hbase : N + E ≤ (N + E) * L ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N + E) (Nat.le_trans hl hl₂)
  refine ⟨?_, hret, ?_, hvis, ?_, hpc, hrow, hdedup, ?_⟩
  · intro q v z
    have hz : z.1 = QuotientMembership.Index.contains b q v := by
      dsimp only [z]
      first
      | rfl
      | exact?
      | (symm; exact?)
    exact ⟨hz, hz ▸ hquery q v,
      ForestPreparedBuild.containsCounted_count_le
        data size_data rank increasing covers rankArc flat q v⟩
  · intro s _ i
    exact ⟨rfl, rfl⟩
  · rw [hvis, Nat.mul_assoc]
    omega
  · by_cases large : 3 ≤ N
    · rw [dite_eq_left large] at hbranch ⊢
      dsimp only at hbranch ⊢
      obtain ⟨hb, hr, hpref, _, q, cnt, w, qs, a, d, sortCost, total, frames,
        hrun, hread, hcnt, hwork, _, hlookup, _, _, happ, _, _, hdict, _,
        hframe, _, hsort, hfinish⟩ := hbranch
      refine ⟨hb, hr, q, cnt, w, qs, a, d, sortCost, total, frames,
        hrun, hread, hcnt, hwork, hlookup, happ, rfl, hdict, hframe, ?_⟩
      intro cfg out h
      obtain ⟨hf, hs, _⟩ := hfinish h
      have hn : 1 ≤ N := by omega
      refine ⟨hf, actualFinishRows h, actualFinishInverse h, phaseReceipt h, ?_, ?_⟩
      · exact Nat.le_trans (Nat.add_le_add hs (finishPhaseSites_le h)) (uniformSites hn hl)
      · intro todo t rev k cells hv hc
        have hsw := (hpref hv).2
        have hsel := finishSelectedCells_le h
        have hfc := finishCellsAt_le h hc
        have hnodes := nodeCount_le h
        unfold coveredRootSum
        dsimp only [p, prep, b, N, E]
        omega
    · rw [dite_eq_right large] at hbranch ⊢
      exact hbranch

end ForestSourceExecution
end PaperB
