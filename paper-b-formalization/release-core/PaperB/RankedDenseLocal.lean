import PaperB.DenseLabelledArcIso
import PaperB.DenseQuotientLocalOrder

namespace PaperB.RankedDenseLocal

open Digraph EX16Assembly StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open DenseQuotientRows DenseOriginalQuotient DenseOriginalQuotient.Transport DenseQuotientLocalOrder

structure Local where
  graph : LabelledQuotient
  rank : Fin graph.vertexCount → Nat
  rank_injective : Function.Injective rank
  arc_lt : ∀ {v e}, e ∈ graph.outArcs v → rank v < rank e.head
  flat : graph.IsFlat
  data : Array (Fin graph.vertexCount)
  size_data : data.size = graph.vertexCount
  sorted : (data.toList.map rank).Pairwise (· < ·)

private def reindex {I : Type} {A : I → Type} {u : I}
    (e : Sigma A) (h : e.1 = u) : A u :=
  cast (congrArg A h) e.2

private theorem reindex_eq {I : Type} {A : I → Type} {u : I}
    {e : Sigma A} {a : A u} (h : e.1 = u) (he : e = ⟨u, a⟩) :
    reindex e h = a := by
  subst e
  rfl

private theorem fullSize {n : Nat} (a : Array (Fin n)) (f : Fin n → Nat)
    (hs : (a.toList.map f).Pairwise (· < ·))
    (hc : ∀ i : Fin n, i ∈ a.toList) : a.size = n := by
  have hn : a.toList.Nodup := by
    change a.toList.Pairwise (· ≠ ·)
    rw [List.pairwise_map] at hs
    exact hs.imp (fun h he => (Nat.ne_of_lt h) (congrArg f he))
  have hf : (List.ofFn (id : Fin n → Fin n)).Nodup := by
    change List.Pairwise (· ≠ ·) _
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn, id_eq]
    intro he
    have hv := congrArg Fin.val he
    change i = j at hv
    omega
  have hp := (List.perm_ext_iff_of_nodup hn hf).2
    (fun v => ⟨fun _ => List.mem_ofFn.mpr ⟨v, rfl⟩, fun _ => hc v⟩)
  simpa using hp.length_eq

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r)
variable {buckets : ChildLists q.count} (rows : DenseQuotientRows.Layout buckets)

-- The position certificate is generic: the bridge need not name a private
-- certificate or unfold the implementation of the grouped order.
private theorem slotRank_eq_denseRank (f : Fin g.vertexCount → Nat)
    (u : Fin q.count)
    (ok : ∀ c : Fin q.count,
      c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
    (i : Fin (rows.length u)) :
    slotRank q rows f u i = denseRank f q u ok rows i := by
  change f (q.ids.originals.read (Sum.elim id id (rows.decode u i).val)) =
    f (occurrenceToOriginal q u ok (rows.decode u i)).val
  generalize rows.decode u i = k
  rcases k with ⟨k, hk⟩
  cases k with
  | inl d =>
    change d = u at hk
    subst d
    rfl
  | inr c => rfl

variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
variable (p : KahnLocals q rows childOK)
variable (progress : ∀ x y, g.HasArc x y → p.bound.rankRead x < p.bound.rankRead y)
variable (injective : ∀ ⦃x y⦄, p.bound.rankRead x = p.bound.rankRead y → x = y)
variable (spec : ParentSpec g r q.parent)

/-- Build one dense local quotient and retain its already grouped order array. -/
def ranked
    (em : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hem : em = (StaticOriginalSiblingEmitter.emitAll q).1)
    (u : Fin q.count) : Local :=
  let hd := q.ids.original_reachable u
  let hf := q.ids.slot_of_original u
  have hz : 0 < rows.length u := by
    rw [rows.length_exact]
    omega
  let H := DenseOriginalQuotient.build progress injective q em hem u hd hf
    rows childOK hz
  let e := p.arrays[u.val]'(by
    simpa only [KahnLocals.size q rows childOK p] using u.isLt)
  have hrow := KahnLocals.get_eq q rows childOK p u
  let a : Array (Fin (rows.length u)) := reindex e (congrArg Sigma.fst hrow)
  have ha : a = slotArray q rows childOK p.bound.result.order u :=
    reindex_eq (congrArg Sigma.fst hrow) hrow
  let f := slotRank q rows p.bound.rankRead u
  have hs : (a.toList.map f).Pairwise (· < ·) := by
    have h := KahnLocals.increasing q rows childOK p u
    dsimp only at h
    rw [hrow] at h
    rw [ha]
    exact h
  have hc : ∀ i : Fin (rows.length u), i ∈ a.toList := by
    have h := KahnLocals.covers q rows childOK p u
    dsimp only at h
    rw [hrow] at h
    intro i
    rw [ha]
    obtain ⟨j, hj, he⟩ := h i
    exact List.mem_iff_getElem.mpr
      ⟨j, by simpa using hj, by simpa only [Array.getElem_toList] using he⟩
  { graph := H
    rank := f
    rank_injective := by
      intro v w h
      apply denseRank_injective progress injective q u hd rows childOK spec
      rw [← slotRank_eq_denseRank q rows _ u _ v,
        ← slotRank_eq_denseRank q rows _ u _ w]
      exact h
    arc_lt := by
      intro v e he
      have h := denseRank_lt_of_mem_outArcs_build progress injective q em hem
        u hd hf rows childOK hz spec (v := v) (e := e) he
      rw [← slotRank_eq_denseRank q rows _ u _ v,
        ← slotRank_eq_denseRank q rows _ u _ e.head] at h
      exact h
    flat := build_isFlat progress injective q em hem u hd hf rows childOK hz spec
    data := a
    size_data := fullSize a f hs hc
    sorted := hs }

structure Family (n : Nat) where
  data : Array Local
  size_data : data.size = n

def Family.get {n : Nat} (F : Family n) (u : Fin n) : Local :=
  F.data[u.val]'(by simpa only [F.size_data] using u.isLt)

/-- The reader's decision lookup selects a stored quotient, not a new build. -/
def Family.find (F : Family q.count) (v : Fin g.vertexCount) : Option Local :=
  (q.ids.find v).map F.get

@[simp] theorem Family.find_held (F : Family q.count) (u : Fin q.count) :
    Family.find q F (q.ids.originals.read u) = some (F.get u) := by
  simp [Family.find, q.ids.slot_of_original u]

/-- Share one emission table across the materialized dense quotient family. -/
def ofPrepared : Family q.count :=
  let em := (StaticOriginalSiblingEmitter.emitAll q).1
  let a := Array.ofFn (ranked q rows childOK p progress injective spec em rfl)
  ⟨a, by simp [a]⟩

@[simp] theorem get_ofPrepared (u : Fin q.count) :
    (ofPrepared q rows childOK p progress injective spec).get u =
      ranked q rows childOK p progress injective spec
        (StaticOriginalSiblingEmitter.emitAll q).1 rfl u := by
  simp [Family.get, ofPrepared, Array.getElem_ofFn]

/-- Prepare the grouped orders once for an existing grouped child layout. -/
def prepare (b : BoundKahnOrder g)
    (step : ∀ x y, g.HasArc x y → b.rankRead x < b.rankRead y)
    (inj : ∀ ⦃x y⦄, b.rankRead x = b.rankRead y → x = y)
    (parentSpec : ParentSpec g r q.parent) : Family q.count :=
  let locals := KahnLocals.prepare q rows childOK b
  ofPrepared q rows childOK locals step inj parentSpec

end PaperB.RankedDenseLocal
