import PaperB.ExitPhysicalSchedule
import PaperB.ExitLinearSchedule
import PaperB.ExitPhysicalKeys

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB.OrderedFreshHeads

structure ExitTransferDriver (H : LabelledQuotient) where
  address : Nat
  child : CutPair H
  parent : CutPair H

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : _root_.PaperB.OrderedReaderResult p data size_data rank large)

private def transferSlot? (lookup : Vertex H → Option (Event H))
    (y : Vertex H) : Option (Fin r.out.tables.next) :=
  match lookup y with
  | none => none
  | some e =>
    if h : e.node < r.out.tables.next then some ⟨e.node, h⟩ else none

private theorem transferSlot?_eq_actualSlot (y : Vertex H) :
    transferSlot? r (headLookup r) y = actualSlot r y :=
  rfl

private def transferAt? (i : Fin r.out.tables.next) :
    Option (ExitTransferDriver H) :=
  match exitBackKey? r i.val with
  | none => none
  | some child =>
    match exitBackKey? r (actualPhysicalParent r i.val) with
    | none => none
    | some parent => some ⟨i.val, child, parent⟩

/-- Collect successful reads in actual sweep order, sharing one head lookup. -/
def exitTransferDrivers : Array (ExitTransferDriver H) :=
  let lookup : Vertex H → Option (Event H) := headLookup r
  let order := (actualP r).orderAt
  ((List.finRange H.vertexCount).filterMap fun j =>
    (transferSlot? r lookup (order j)).bind (transferAt? r)).toArray

private theorem transferRead?_eq_some_iff (y : Vertex H)
    (d : ExitTransferDriver H) :
    (transferSlot? r (headLookup r) y).bind (transferAt? r) = some d ↔
      ∃ i : Fin r.out.tables.next,
        actualSlot r y = some i ∧ i.val = d.address ∧
          exitHeadKeys? r y = some (d.child, d.parent) := by
  rw [transferSlot?_eq_actualSlot]
  rcases d with ⟨address, child, parent⟩
  cases hs : actualSlot r y with
  | none => simp [Option.bind, hs]
  | some i =>
    cases hc : exitBackKey? r i.val with
    | none => simp [Option.bind, transferAt?, exitHeadKeys?, hs, hc]
    | some c =>
      cases hp : exitBackKey? r (actualPhysicalParent r i.val) <;>
        simp [Option.bind, transferAt?, exitHeadKeys?, hs, hc, hp]

theorem mem_exitTransferDrivers_iff_order (d : ExitTransferDriver H) :
    d ∈ exitTransferDrivers r ↔
      ∃ (j : Fin H.vertexCount) (i : Fin r.out.tables.next),
        actualSlot r ((actualP r).orderAt j) = some i ∧
          i.val = d.address ∧
          exitHeadKeys? r ((actualP r).orderAt j) = some (d.child, d.parent) := by
  simp [exitTransferDrivers, List.mem_filterMap, List.mem_finRange,
    transferRead?_eq_some_iff]

theorem mem_exitTransferDrivers_iff
    (covers : ∀ y : Vertex H, ∃ j : Fin H.vertexCount,
      (actualP r).orderAt j = y)
    (d : ExitTransferDriver H) :
    d ∈ exitTransferDrivers r ↔
      ∃ (y : Vertex H) (i : Fin r.out.tables.next),
        actualSlot r y = some i ∧ i.val = d.address ∧
          exitHeadKeys? r y = some (d.child, d.parent) := by
  rw [mem_exitTransferDrivers_iff_order r d]
  constructor
  · rintro ⟨j, i, hit, hi, keys⟩
    exact ⟨(actualP r).orderAt j, i, hit, hi, keys⟩
  · rintro ⟨y, i, hit, hi, keys⟩
    obtain ⟨j, hj⟩ := covers y
    exact ⟨j, i, by simpa only [hj] using hit, hi,
      by simpa only [hj] using keys⟩

/-- At most one driver per occupied head slot encountered in actual order. -/
theorem exitTransferDrivers_size_le_heads :
    (exitTransferDrivers r).size ≤
      ((List.finRange H.vertexCount).filterMap fun j =>
        actualSlot r ((actualP r).orderAt j)).length := by
  let read := fun j : Fin H.vertexCount =>
    transferSlot? r (headLookup r) ((actualP r).orderAt j)
  have h :
      (((List.finRange H.vertexCount).filterMap read).filterMap
        (transferAt? r)).length ≤
      ((List.finRange H.vertexCount).filterMap read).length := by
    apply List.length_filterMap_le
  simpa [exitTransferDrivers, List.filterMap_filterMap, read,
    transferSlot?_eq_actualSlot] using h

theorem exitTransferDrivers_size_le :
    (exitTransferDrivers r).size ≤ H.vertexCount := by
  calc
    _ ≤ ((List.finRange H.vertexCount).filterMap fun j =>
          actualSlot r ((actualP r).orderAt j)).length :=
      exitTransferDrivers_size_le_heads r
    _ ≤ (List.finRange H.vertexCount).length := by
      apply List.length_filterMap_le
    _ = H.vertexCount := by simp

variable {F : JumpForest} {up : Fin F.size → Fin F.size}
variable {g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}

theorem exitTransferDrivers_provenance
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    {d : ExitTransferDriver H} (hd : d ∈ exitTransferDrivers r) :
    ∃ (y : Vertex H) (i : Fin r.out.tables.next) (a : Fin F.size),
      actualSlot r y = some i ∧
      (actualP r).firstAt y i ∧
      i.val = d.address ∧
      a.val = d.address ∧
      actualPhysicalParent r d.address ≠ 0 ∧
      (up a).val = actualPhysicalParent r d.address ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables d.child =
        some d.address ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables d.parent =
        some (actualPhysicalParent r d.address) ∧
      (buildProperLossForest H rank).nodeKey? (E.image a) = some d.child ∧
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent (E.image a)) = some d.parent := by
  obtain ⟨j, i, hit, hi, keys⟩ := (mem_exitTransferDrivers_iff_order r d).mp hd
  let y := (actualP r).orderAt j
  have firstAt : (actualP r).firstAt y i :=
    (actualSlot_exact r full ch y i).mp hit
  obtain ⟨a, child, parent, ha, hp0, hup, _hcb, _hpb, hcs, hps, hck, hpk, hkeys⟩ :=
    actualSlot_exitHeadKeys r G hUp E hit firstAt
  have hk : (child, parent) = (d.child, d.parent) :=
    Option.some.inj (hkeys.symm.trans keys)
  have hc : child = d.child := congrArg Prod.fst hk
  have hp : parent = d.parent := congrArg Prod.snd hk
  subst child
  subst parent
  refine ⟨y, i, a, hit, firstAt, hi, ha.trans hi, ?_⟩
  rw [← hi]
  exact ⟨hp0, hup, hcs, hps, hck, hpk⟩

end PaperB.Exit.OrderedReaderResult
