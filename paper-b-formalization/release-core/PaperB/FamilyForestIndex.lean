import PaperB.RankedDenseLocal
import PaperB.ForestPreparedBuild

namespace PaperB.RankedDenseLocal

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

theorem Local.complete (L : Local) (v : Vertex L.graph) :
    v ∈ L.data.toList := by
  let a := L.data.toList
  let all := List.ofFn (id : Fin L.graph.vertexCount → Fin L.graph.vertexCount)
  let rest := all.filter (fun x => decide (x ∉ a))
  have ha : a.Nodup := by
    have hs : (a.map L.rank).Pairwise (· < ·) := L.sorted
    rw [List.pairwise_map] at hs
    change a.Pairwise (· ≠ ·)
    exact hs.imp (fun h he => Nat.ne_of_lt h (congrArg L.rank he))
  have hall : ∀ x : Vertex L.graph, x ∈ all := by
    intro x
    exact List.mem_ofFn.mpr ⟨x, rfl⟩
  have hallND : all.Nodup := by
    change List.Pairwise (· ≠ ·)
      (List.ofFn (id : Fin L.graph.vertexCount → Fin L.graph.vertexCount))
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn, id_eq]
    intro he
    have hv := congrArg Fin.val he
    change i = j at hv
    omega
  have hrest (x : Vertex L.graph) : x ∈ rest ↔ x ∉ a := by
    simp [rest, List.mem_filter, hall x]
  have hrestND : rest.Nodup := by
    dsimp only [rest]
    first
    | exact List.Pairwise.filter _ hallND
    | exact hallND.filter _
    | exact List.Pairwise.sublist (List.filter_sublist _) hallND
  have hjoined : (a ++ rest).Nodup := by
    change (a ++ rest).Pairwise (· ≠ ·)
    rw [List.pairwise_append]
    refine ⟨ha, hrestND, ?_⟩
    intro x hx y hy he
    subst y
    exact (hrest x).mp hy hx
  have hp : (a ++ rest).Perm all :=
    (List.perm_ext_iff_of_nodup hjoined hallND).2 (by
      intro x
      constructor
      · intro _
        exact hall x
      · intro _
        by_cases hx : x ∈ a
        · exact List.mem_append.mpr (Or.inl hx)
        · exact List.mem_append.mpr (Or.inr ((hrest x).mpr hx)))
  have haLen : a.length = L.graph.vertexCount := by
    simpa [a] using L.size_data
  have hallLen : all.length = L.graph.vertexCount := by
    simp [all]
  have hlen := hp.length_eq
  rw [List.length_append, haLen, hallLen] at hlen
  have hzero : rest.length = 0 := by omega
  have hnil : rest = [] := by
    cases h : rest with
    | nil => rfl
    | cons x xs => simp [h] at hzero
  change v ∈ a
  by_cases hv : v ∈ a
  · exact hv
  · have hm := (hrest v).mpr hv
    simp [hnil] at hm

theorem Local.orderIncreasing (L : Local)
    (i j : Fin L.graph.vertexCount) (hij : i.val < j.val) :
    L.rank (orderedVertexAt L.data L.size_data i) <
      L.rank (orderedVertexAt L.data L.size_data j) := by
  have hs := L.sorted
  rw [List.pairwise_map, List.pairwise_iff_getElem] at hs
  have hi : i.val < L.data.toList.length := by
    simpa [L.size_data] using i.isLt
  have hj : j.val < L.data.toList.length := by
    simpa [L.size_data] using j.isLt
  simpa only [orderedVertexAt, Array.getElem_toList] using
    hs i.val j.val hi hj hij

theorem Local.orderCovers (L : Local) (v : Vertex L.graph) :
    ∃ i : Fin L.graph.vertexCount, orderedVertexAt L.data L.size_data i = v := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (L.complete v)
  have hi' : i < L.graph.vertexCount := by
    simpa [L.size_data] using hi
  refine ⟨⟨i, hi'⟩, ?_⟩
  simpa only [orderedVertexAt, Array.getElem_toList] using he

theorem Local.rankQuotientArc (L : Local) (u v : Vertex L.graph)
    (h : L.graph.HasQuotientArc u v) : L.rank u < L.rank v := by
  first
  | rcases h with ⟨e, he, rfl⟩
    exact L.arc_lt he
  | rcases h with ⟨e, rfl, he⟩
    exact L.arc_lt he

local instance cutPairDecidableEq (H : LabelledQuotient) :
    DecidableEq (CutPair H) := by
  first
  | infer_instance
  | unfold CutPair
    infer_instance

def Local.buildForest (L : Local) : QuotientMembership.Index L.graph :=
  ForestPreparedBuild.build (H := L.graph)
    L.data L.size_data L.rank L.orderIncreasing L.orderCovers
    L.rankQuotientArc L.flat

structure ForestCell where
  Payload : Type
  value : Payload

private def ForestCell.readAs (c : ForestCell) {T : Type}
    (h : c.Payload = T) : T :=
  cast h c.value

private theorem ForestCell.readAs_eq {c : ForestCell} {T : Type} {x : T}
    (h : c.Payload = T) (hc : c = ⟨T, x⟩) :
    c.readAs h = x := by
  subst c
  rfl

structure ForestIndex {n : Nat} (F : Family n) where
  data : Array ForestCell
  size_data : data.size = n
  type_data : ∀ u : Fin n,
    (data[u.val]'(by simpa only [size_data] using u.isLt)).Payload =
      QuotientMembership.Index (F.get u).graph

namespace ForestIndex

variable {n : Nat} {F : Family n}

def get (R : ForestIndex F) (u : Fin n) :
    QuotientMembership.Index (F.get u).graph :=
  (R.data[u.val]'(by simpa only [R.size_data] using u.isLt)).readAs
    (R.type_data u)

private def buildCell (F : Family n) (u : Fin n) : ForestCell :=
  let L := F.get u
  ⟨QuotientMembership.Index L.graph, L.buildForest⟩

def build (F : Family n) : ForestIndex F :=
  let a := Array.ofFn (buildCell F)
  { data := a
    size_data := by simp [a]
    type_data := by
      intro u
      simp only [a, Array.getElem_ofFn, buildCell] }

@[simp] theorem get_build (F : Family n) (u : Fin n) :
    (build F).get u = (F.get u).buildForest := by
  unfold get
  apply ForestCell.readAs_eq
  simp only [build, Array.getElem_ofFn, buildCell]

def contains (R : ForestIndex F) (u : Fin n)
    (q : CutPair (F.get u).graph) (v : Vertex (F.get u).graph) : Bool :=
  QuotientMembership.Index.contains (R.get u) q v

theorem query_iff (F : Family n) (u : Fin n)
    (q : CutPair (F.get u).graph) (v : Vertex (F.get u).graph) :
    (build F).contains u q v = true ↔
      q.fst < q.snd ∧ (F.get u).graph.ProperLoss q v := by
  rw [contains, get_build]
  let L := F.get u
  exact ForestPreparedBuild.query_iff (H := L.graph)
    L.data L.size_data L.rank L.orderIncreasing L.orderCovers
    L.rankQuotientArc L.flat q v

def arraySize (R : ForestIndex F) : Nat :=
  ((List.ofFn (id : Fin n → Fin n)).map
    (fun u => QuotientMembership.Index.arraySize (R.get u))).sum

end ForestIndex

def Family.totalVertices {n : Nat} (F : Family n) : Nat :=
  ((List.ofFn (id : Fin n → Fin n)).map
    (fun u => (F.get u).graph.vertexCount)).sum

private theorem sum_map_le_nine {α : Type} (xs : List α) (a b : α → Nat)
    (h : ∀ x, a x ≤ 9 * b x) :
    (xs.map a).sum ≤ 9 * (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (h x) ih

theorem ForestIndex.arraySize_build_le {n : Nat} (F : Family n) :
    (ForestIndex.build F).arraySize ≤ 9 * F.totalVertices := by
  unfold ForestIndex.arraySize Family.totalVertices
  apply sum_map_le_nine
  intro u
  rw [ForestIndex.get_build]
  let L := F.get u
  exact ForestPreparedBuild.arraySize_le (H := L.graph)
    L.data L.size_data L.rank L.orderIncreasing L.orderCovers
    L.rankQuotientArc L.flat

end PaperB.RankedDenseLocal
