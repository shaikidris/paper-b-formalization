import PaperB.ForestCompactBuildWork
import PaperB.ForestCompactPeak
import PaperB.ForestScalarCost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PhaseReceipt

structure Phase where
  sites : Nat
  work : Nat
  /-- For simultaneous allocations, this is the sum of their sizes. -/
  liveWords : Nat

def totalSites : List Phase → Nat
  | [] => 0
  | p :: ps => p.sites + totalSites ps

def totalWork : List Phase → Nat
  | [] => 0
  | p :: ps => p.work + totalWork ps

def peak : List Phase → Nat
  | [] => 0
  | p :: ps => max p.liveWords (peak ps)

@[simp] theorem totalSites_nil : totalSites [] = 0 := rfl

@[simp] theorem totalSites_cons (p : Phase) (ps : List Phase) :
    totalSites (p :: ps) = p.sites + totalSites ps := rfl

@[simp] theorem totalWork_nil : totalWork [] = 0 := rfl

@[simp] theorem totalWork_cons (p : Phase) (ps : List Phase) :
    totalWork (p :: ps) = p.work + totalWork ps := rfl

@[simp] theorem peak_nil : peak [] = 0 := rfl

@[simp] theorem peak_cons (p : Phase) (ps : List Phase) :
    peak (p :: ps) = max p.liveWords (peak ps) := rfl

theorem totalWork_le_rate_mul_totalSites (phases : List Phase) (rate : Nat)
    (hwork : ∀ p ∈ phases, p.work ≤ rate * p.sites) :
    totalWork phases ≤ rate * totalSites phases := by
  induction phases with
  | nil => simp
  | cons p ps ih =>
      have hp : p.work ≤ rate * p.sites := hwork p (by simp)
      have hps : ∀ q ∈ ps, q.work ≤ rate * q.sites :=
        fun q hq => hwork q (List.mem_cons_of_mem _ hq)
      simpa only [totalWork_cons, totalSites_cons, Nat.mul_add] using
        (Nat.add_le_add hp (ih hps))

theorem peak_le_cap (phases : List Phase) (cap : Nat)
    (hlive : ∀ p ∈ phases, p.liveWords ≤ cap) :
    peak phases ≤ cap := by
  induction phases with
  | nil => simp
  | cons p ps ih =>
      have hp : p.liveWords ≤ cap := hlive p (by simp)
      have hps : ∀ q ∈ ps, q.liveWords ≤ cap :=
        fun q hq => hlive q (List.mem_cons_of_mem _ hq)
      rw [peak_cons]
      exact Nat.max_le.mpr ⟨hp, ih hps⟩

theorem totalWork_le_rate_mul_siteCap (phases : List Phase) (rate siteCap : Nat)
    (hwork : ∀ p ∈ phases, p.work ≤ rate * p.sites)
    (hsites : totalSites phases ≤ siteCap) :
    totalWork phases ≤ rate * siteCap :=
  Nat.le_trans (totalWork_le_rate_mul_totalSites phases rate hwork)
    (Nat.mul_le_mul_left rate hsites)

end PhaseReceipt

namespace PaperB.ForestHead

open StepCostCertificate

/-- The search kernel's word arithmetic and tests, excluding the probe.
A terminating branch needs at most a fuel test, an increment and a
bound test. A continuing branch additionally charges three midpoint
operations, the fuel decrement, the probe-result branch, and four
counter additions when returning from the selected recursive call. -/
def searchControl (p : Nat → Probe) (fuel lo hi : Nat) : Nat × Nat :=
  meteredBinarySearch (fun i => ((p i).ok, 0)) 3 12 fuel lo hi

theorem searchControl_exact (p : Nat → Probe) (fuel lo hi : Nat) :
    searchControl p fuel lo hi =
      let r := measuredSearch p fuel lo hi
      (r.cut, 3 + r.comparisons * 12) := by
  simpa [searchControl] using (search_scalar_meter p 3 12 0 0 0 fuel lo hi)

theorem searchControl_le (p : Nat → Probe) (fuel lo hi : Nat) :
    (searchControl p fuel lo hi).2 ≤ 3 + fuel * 12 := by
  simpa [searchControl] using
    (meteredBinarySearch_cost_le (fun i => ((p i).ok, 0)) 3 12 0
      (fun _ => Nat.le_refl 0) fuel lo hi)

/-- Charge a list tag test and the predicate-result branch per visited
cell, and reserve two counter additions on that branch. Charge the
terminating tag test only when the scan reaches the empty list. -/
def scanControl {α : Type} (test : α → Bool × Nat) (xs : List α) : Bool × Nat :=
  meteredListAny (fun x => (!(test x).1, 0)) 1 4 xs

theorem scanControl_exact {α : Type} (test : α → Bool × Nat) (xs : List α) :
    scanControl test xs =
      let r := scan test xs
      (!r.ok, (if r.ok then 1 else 0) + r.tests * 4) := by
  simpa [scanControl] using (scan_scalar_meter test 1 4 0 xs)

end PaperB.ForestHead

namespace PaperB.ForestPreparedBuild

open PhaseReceipt
open _root_.EX24 _root_.EX24.PreparedSweep _root_.EX24.PreparedSweep.Storage
open AggregateEX24
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.RetainedProperLoss
open PaperB.Jumps PaperB.KahnDecreasing PaperB.EX24.FinalDFS
open PaperB.ForestLayout PaperB.ForestLayout.LiveCells

/-- Price the named arithmetic and branch sites in the measured inner
kernels. There is one search exit per active head. At most one empty
predecessor-scan exit is possible per midpoint comparison. -/
def scalarControlSites (work : Work) : Nat :=
  3 * work.activeHeads + 13 * work.comparisons + 4 * work.tests

theorem scalarControlSites_le (L : Nat) (count : Count) (work : Work) (a : Nat)
    (active : work.activeHeads ≤ count.heads) :
    scalarControlSites work ≤ 13 * ResidualUnit.toll L count work a := by
  unfold scalarControlSites ResidualUnit.toll
  omega

def constructionPhases (rank input init dict sweep scalar finish pack : Nat) :
    List Phase :=
  [⟨rank, rank, 0⟩, ⟨input, input, 0⟩, ⟨init, init, 0⟩, ⟨dict, dict, 0⟩,
   ⟨sweep, sweep + scalar, 0⟩, ⟨finish, finish, 0⟩, ⟨pack, pack, 0⟩]

/-- The selected source work, including the inner kernels' priced word
arithmetic and branches. Execution in the Lean runtime is outside this
charge: allocations, destructors and unlisted control sites still need
a refinement proof. -/
private theorem constructionPhases_bound (rank input init dict sweep scalar finish pack cap : Nat)
    (sites : rank + input + init + dict + sweep + finish + pack ≤ cap)
    (scalarBound : scalar ≤ 13 * sweep) :
    totalWork (constructionPhases rank input init dict sweep scalar finish pack) ≤ 14 * cap := by
  apply totalWork_le_rate_mul_siteCap _ 14 cap
  · intro p hp
    simp [constructionPhases] at hp
    rcases hp with h | h | h | h | h | h | h <;> subst p <;> dsimp <;> omega
  · simp only [constructionPhases, totalSites_cons, totalSites_nil, Nat.add_zero]
    omega

private theorem activeHeads_le_heads {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {cnt : Count} {work : Work}
    (h : WorkTrace c rank s rows out log cnt work) : work.activeHeads ≤ cnt.heads := by
  induction h with
  | nil => decide
  | @cons s out row rows r log n w hr ht ih =>
    have ha : (headWork rank row r).activeHeads ≤ 1 := by
      unfold headWork
      dsimp only
      generalize planPrepared rank row.head row.tests = plan
      cases plan
      · exact Nat.zero_le 1
      · exact Nat.le_refl 1
    change (headWork rank row r).activeHeads + w.activeHeads ≤ 1 + n.heads
    omega

variable {H : LabelledQuotient} (data : Array (Vertex H))
variable (size_data : data.size = H.vertexCount)
variable (unique : data.toList.Nodup)
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat)

set_option maxHeartbeats 1000000 in
/-- Source-phase work package for the actual dense-order build. The
meter includes the incoming-row construction charges, the measured sweep
sites, and the scalar allowance for the visited search and scan calls. -/
theorem buildWordsFromOrder_selected_work (large : 3 ≤ H.vertexCount) :
    let N := H.vertexCount
    let E := H.arcCount
    let L := OracleContract.L N
    let t := orderRanks data unique
    let rank := readRank t
    let p := (ForestIncomingPrep.build H (by intro u v; rfl)).tests
    let c := packedOrderedConfig p large
    let rows := orderedRows p data size_data
    let mem := (ConcreteInit.initImage N).1
    let s := initial c mem N
    ∃ (out : State H) (log : Log H) (ok : OutputOK c rank out)
      (w : WordColumns (OracleContract.wordBits 5 N 0))
      (reads : Nat) (cnt : Count) (work : Work) (keys : List (CutPair H))
      (appendSites sortSites dictionarySites : Nat),
      fromRoot c rank mem N rows = some (out, log) ∧
      buildWordsFromOrder data size_data unique covers topo flat = some w ∧
      PackedReads.packedReadSum c rank s rows = some reads ∧
      WorkTrace c rank s rows out log cnt work ∧
      PairLookupTrace c rank s rows out log cnt work keys ∧
      (∃ installs, ResidualUnit.AppendTrace c rank s rows out log cnt appendSites installs) ∧
      ForestDictionary.PackedDictionaryConstructionTrace p orderedPairCode
        c.dict sortSites dictionarySites ∧
      let rankSites := t.ranks.size + t.orderReads + t.indexWrites
      let sweepSites := reads + pairLookupComparisons c keys +
        ResidualUnit.toll L cnt work appendSites
      totalWork (constructionPhases rankSites (incomingSites H) (initialSites c)
        dictionarySites sweepSites (scalarControlSites work)
        (StaticGroupedTreeReader.endpointSites (packedInput ok)) w.wordCount)
          ≤ 3584 * (N + E) * L ^ 2 := by
  intro N E L t rank p c rows mem s
  obtain ⟨out, log, ok, w, reads, cnt, work, keys, a, installed, sw, dw,
    hrun, hpack, hread, _, hwork, hlookup, happend, hdict, _, hsites⟩ :=
    buildWordsFromOrder_phase_sites data size_data unique covers topo flat large
  refine ⟨out, log, ok, w, reads, cnt, work, keys, a, sw, dw,
    hrun, hpack, hread, hwork, hlookup, ⟨installed, happend⟩, hdict, ?_⟩
  have hscalar := scalarControlSites_le L cnt work a (activeHeads_le_heads hwork)
  have hdom :
      scalarControlSites work ≤
        13 * (reads + pairLookupComparisons c keys + ResidualUnit.toll L cnt work a) :=
    Nat.le_trans hscalar (Nat.mul_le_mul_left 13 (by omega))
  dsimp only
  have h := constructionPhases_bound _ _ _ _ _ _ _ _ _ hsites hdom
  simpa only [← Nat.mul_assoc] using h

/-- A peak over simultaneous source-cell charges. Preparation roots stay
charged through the sweep and finish, including the storage occupied by
the packed result at the finish handoff. -/
def chargedBoundaryPeak (preparation sweep finish : Nat) : Nat :=
  peak [⟨0, 0, preparation⟩, ⟨0, 0, preparation + sweep⟩,
    ⟨0, 0, preparation + finish⟩]

theorem buildWordsFromOrder_boundary_peak (large : 3 ≤ H.vertexCount) :
    let N := H.vertexCount
    let rank := readRank (orderRanks data unique)
    let p := (ForestIncomingPrep.build H (by intro u v; rfl)).tests
    let c := packedOrderedConfig p large
    let rows := orderedRows p data size_data
    let mem := (ConcreteInit.initImage N).1
    let s := initial c mem N
    ∃ (out : State H) (log rev : Log H) (ok : OutputOK c rank out)
      (w : WordColumns (OracleContract.wordBits 5 N 0)),
      fromRoot c rank mem N rows = some (out, log) ∧
      Visit c rank rows s [] [] out rev rows.length ∧
      buildWordsFromOrder data size_data unique covers topo flat = some w ∧
      let x := packedInput ok
      let T := nodeCount c out
      let base := checkpointCells c data rows out rev + N + log.length
      let extracted := x.parent.data.size + x.depth.data.size
      let grouping := groupedChildListsPeak T T
      let oldColumns := c.dict.size + out.tables.slots.size + out.tables.back.size +
        out.labels.size + (StaticGroupedTreeReader.endpointsOnly x).entry.data.size +
        (StaticGroupedTreeReader.endpointsOnly x).stop.data.size
      let finish := base + extracted + grouping + 9 * T + 3 * oldColumns + w.wordCount
      ∀ {todo : List (Row H)} {t : State H} {acc : Log H} {j : Nat},
        Visit c rank rows s [] todo t acc j →
        chargedBoundaryPeak (preparationReserve H) (checkpointCells c data rows t acc + N)
          finish ≤ 128 * (N + H.arcCount) := by
  intro N rank p c rows mem s
  obtain ⟨out, log, rev, ok, w, hrun, hvis, _, hpack, hboundary, _, hfinish⟩ :=
    buildWordsFromOrder_peak_receipts data size_data unique covers topo flat large
  refine ⟨out, log, rev, ok, w, hrun, hvis, hpack, ?_⟩
  intro x T base extracted grouping oldColumns finish todo t acc j hvisit
  have hs : preparationReserve H + (checkpointCells c data rows t acc + N) ≤
      128 * (N + H.arcCount) := by
    rw [← Nat.add_assoc]
    exact hboundary hvisit
  have hf : preparationReserve H + finish ≤ 128 * (N + H.arcCount) := hfinish
  unfold chargedBoundaryPeak
  apply peak_le_cap
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq <;> subst q
  · exact Nat.le_trans (Nat.le_add_right _ _) hs
  · exact hs
  · exact hf

end PaperB.ForestPreparedBuild
