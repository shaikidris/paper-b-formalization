import PaperB.ExitCompactDrivers
import PaperB.ForestSlimIndex

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps PaperB.RetainedProperLoss
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB.OrderedFreshHeads

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : _root_.PaperB.OrderedReaderResult p data size_data rank large)

variable {F : JumpForest} {up : Fin F.size → Fin F.size}
variable {g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}

private theorem compact_realNode_has_image
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    {k : CanonNode H rank} {q : CutPair H}
    (hk : (buildProperLossForest H rank).nodeKey? k = some q) :
    ∃ a : Fin F.size, E.image a = k := by
  obtain ⟨hlt, hloss⟩ :=
    (buildProperLossForest_exists_node_iff rankArc flat q).mp ⟨k, hk⟩
  obtain ⟨addr, _, hit, _⟩ :=
    (exists_properLoss_iff_checkedHit_known r q hlt).mp hloss
  have hread := hit
  simp only [checkedHit, checked_iff_back r q] at hread
  have haddr :
      addr < r.out.tables.next ∧
        r.out.tables.back[addr]? = some (some q) := by
    first
    | grind
    | (constructor <;> exact?)
    | grind [ofOrderedReader, physicalPairSlot?, Option.bind, Option.getD]
    | (cases G <;>
        grind [ofOrderedReader, physicalPairSlot?, Option.bind, Option.getD])
  let a : Fin F.size :=
    ⟨addr, by simpa only [G.size_eq] using haddr.1⟩
  have hb : r.out.tables.back[a.val]? = some (some q) := haddr.2
  have hkey : (buildProperLossForest H rank).nodeKey? (E.image a) = some q :=
    Option.some.inj ((E.back_eq a).symm.trans hb)
  exact ⟨a, buildProperLossForest_nodeKey?_inj H rank (hkey.trans hk.symm)⟩

private theorem compact_pos_of_real_image
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    (a : Fin F.size) {q : CutPair H}
    (hq : (buildProperLossForest H rank).nodeKey? (E.image a) = some q) :
    0 < a.val := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hsize : 0 < F.size := by
    have h := a.isLt
    omega
  have ha : a = (⟨0, hsize⟩ : Fin F.size) := Fin.ext hz
  have hn : (none : Option (CutPair H)) = some q := by
    simpa only [ha, E.root_eq hsize, buildProperLossForest_nodeKey?_root]
      using hq
  cases hn

private theorem compact_order_covers
    (full : FullRows p rank (orderedRows p data size_data)) :
    ∀ y : Vertex H, ∃ j : Fin H.vertexCount, (actualP r).orderAt j = y := by
  intro y
  obtain ⟨row, hr, he⟩ := full.covers y
  let make (j : Fin H.vertexCount) : Row H :=
    ⟨orderedVertexAt data size_data j, p.row (orderedVertexAt data size_data j)⟩
  change row ∈ List.ofFn make at hr
  obtain ⟨j, hj, hh⟩ := List.mem_iff_getElem.mp hr
  let k : Fin H.vertexCount := ⟨j, by simpa only [List.length_ofFn] using hj⟩
  have hk : make k = row := by
    simpa only [List.getElem_ofFn] using hh
  exact ⟨k, (congrArg Row.head hk).trans he⟩

/-- Every canonical edge with real keys at both ends has a driver in
the computed transfer array, at a physical address mapped to its child. -/
theorem exitTransferDrivers_covers_realEdge
    (full : FullRows p rank (orderedRows p data size_data))
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    {k : CanonNode H rank} {child parent : CutPair H}
    (hk : (buildProperLossForest H rank).nodeKey? k = some child)
    (hp : (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent k) = some parent) :
    ∃ (d : ExitTransferDriver H) (a : Fin F.size),
      d ∈ exitTransferDrivers r ∧
        d.child = child ∧ d.parent = parent ∧
        d.address = a.val ∧ E.image a = k := by
  obtain ⟨a, ha⟩ := compact_realNode_has_image r rankArc flat G E hk
  have hcKey :
      (buildProperLossForest H rank).nodeKey? (E.image a) = some child := by
    simpa only [ha] using hk
  have hpKey :
      (buildProperLossForest H rank).nodeKey? (E.image (up a)) =
        some parent := by
    simpa only [E.parent_eq a, ha] using hp
  have hcBack : r.out.tables.back[a.val]? = some (some child) :=
    (E.back_eq a).trans (congrArg some hcKey)
  have hpBack : r.out.tables.back[(up a).val]? = some (some parent) :=
    (E.back_eq (up a)).trans (congrArg some hpKey)
  have haPos := compact_pos_of_real_image r E a hcKey
  have hpPos := compact_pos_of_real_image r E (up a) hpKey
  have haLt : a.val < r.out.tables.next := by
    simpa only [G.size_eq] using a.isLt
  have hpLt : (up a).val < r.out.tables.next := by
    simpa only [G.size_eq] using (up a).isLt
  have hphys : actualPhysicalParent r a.val = (up a).val := by
    unfold actualPhysicalParent
    rw [(readRecordWords_spec G.layout a.isLt).1, hUp a] <;> rfl
  have hphysNe : actualPhysicalParent r a.val ≠ 0 := by
    rw [hphys]
    exact Nat.ne_of_gt hpPos

  obtain ⟨e, he, heLookup⟩ :=
    (slot_exact_physical r full ch (k := a.val)).mpr
      ⟨haPos, haLt, hphysNe⟩
  let i : Fin r.out.tables.next := ⟨a.val, haLt⟩
  have hslot : actualSlot r e.head = some i := by
    change
      (match headLookup r e.head with
       | none => none
       | some ev =>
         if h : ev.node < r.out.tables.next then some ⟨ev.node, h⟩
         else none) = some i
    simp only [heLookup, he, dif_pos haLt, i]

  have hkeys : exitHeadKeys? r e.head = some (child, parent) := by
    simp [exitHeadKeys?, Option.bind, hslot, i, hphys, exitBackKey?,
      hcBack, hpBack, haPos, hpPos, haLt, hpLt,
      Nat.ne_of_gt haPos, Nat.ne_of_gt hpPos]

  let d : ExitTransferDriver H := ⟨a.val, child, parent⟩
  have hd : d ∈ exitTransferDrivers r :=
    (mem_exitTransferDrivers_iff r (compact_order_covers r full) d).mpr
      ⟨e.head, i, hslot, rfl, hkeys⟩
  exact ⟨d, a, hd, rfl, rfl, rfl, ha⟩

end PaperB.Exit.OrderedReaderResult
