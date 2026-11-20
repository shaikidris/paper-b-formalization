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
      ∃ (q : Nat) (cnt : Count) (w : Work) (qs : List (CutPair H))
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
