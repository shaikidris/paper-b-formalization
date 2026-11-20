import PaperB.PhysicalArcRowMass
import PaperB.FamilyForestIndex

namespace PaperB.RankedDenseLocal

open Digraph EX16Assembly StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open DenseQuotientRows DenseQuotientLocalOrder

/-- The ordered bucket equality required by the flat layout. -/
abbrev HasCanonicalBuckets {N : Nat} {buckets : ChildLists N}
    (_rows : DenseQuotientRows.Layout buckets)
    (root : Fin N) (parent : Fin N → Fin N) : Prop :=
  ∀ u, buckets.get u = bucketChildren root parent u

private theorem finElems_eq_ofFn (n : Nat) :
    finElems n = List.ofFn (id : Fin n → Fin n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [finElems, List.ofFn_succ, ih, Function.comp_def]
    all_goals
      apply congrArg (fun f : Fin n → Fin (n + 1) => List.ofFn f)
      funext i
      apply Fin.ext
      rfl

section Prepared

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r)
variable {buckets : ChildLists q.count} (rows : DenseQuotientRows.Layout buckets)
variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
variable (p : KahnLocals q rows childOK)
variable (progress : ∀ x y : Fin g.vertexCount,
  g.HasArc x y → p.bound.rankRead x < p.bound.rankRead y)
variable (injective : ∀ ⦃x y : Fin g.vertexCount⦄,
  p.bound.rankRead x = p.bound.rankRead y → x = y)
variable (spec : ParentSpec g r q.parent)

theorem get_ofPrepared_vertexCount (u : Fin q.count) :
    ((ofPrepared q rows childOK p progress injective spec).get u).graph.vertexCount =
      rows.length u := by
  rw [get_ofPrepared] <;> rfl

theorem totalVertices_ofPrepared_exact
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read) :
    (ofPrepared q rows childOK p progress injective spec).totalVertices =
      q.count + (q.count - 1) := by
  unfold Family.totalVertices
  simp only [get_ofPrepared_vertexCount, ← finElems_eq_ofFn]
  exact DenseQuotientRows.Layout.sum_lengths_exact rows
    q.input.root q.input.parent.read hg

theorem totalVertices_ofPrepared_le
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read) :
    (ofPrepared q rows childOK p progress injective spec).totalVertices ≤
      2 * q.count := by
  rw [totalVertices_ofPrepared_exact q rows childOK p progress injective spec hg]
  omega

private theorem prepared_nodup_ofFn {α : Type _} {n : Nat}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
        simp only [List.getElem_ofFn, Function.comp_apply] at he
        have hv := congrArg Fin.val (hf he)
        change i + 1 = 0 at hv
        omega
      · apply ih
        intro i j hij
        apply Fin.ext
        have hv := congrArg Fin.val (hf hij)
        change i.val + 1 = j.val + 1 at hv
        omega

theorem get_ofPrepared_arcCount (u : Fin q.count) :
    ((ofPrepared q rows childOK p progress injective spec).get u).graph.arcCount =
      (((StaticOriginalSiblingEmitter.emitAll q).1).row
        (q.ids.originals.read u)).length := by
  have hz : 0 < rows.length u := by
    rw [rows.length_exact]
    omega
  rw [get_ofPrepared]
  exact DenseOriginalQuotient.arcCount_build_eq_emitAll_row_length
    progress injective q (StaticOriginalSiblingEmitter.emitAll q).1 rfl
    u (q.ids.original_reachable u) (q.ids.slot_of_original u)
    rows childOK hz

theorem totalArcs_ofPrepared_le :
    (List.ofFn (fun u : Fin q.count =>
      ((ofPrepared q rows childOK p progress injective spec).get u).graph.arcCount
    )).sum ≤ g.arcCount := by
  let owners := List.ofFn (fun u : Fin q.count => q.ids.originals.read u)
  have hn : owners.Nodup := by
    apply prepared_nodup_ofFn
    intro i j hij
    have h := congrArg (fun v => q.ids.find v) hij
    rw [q.ids.slot_of_original i, q.ids.slot_of_original j] at h
    exact Option.some.inj h
  have hm :
      (owners.map (fun d =>
        (((StaticOriginalSiblingEmitter.emitAll q).1).row d).length)).sum ≤
        g.arcCount := by
    have physical (T : Digraph.GlobalSibling.Getters g (2 * q.count)) :
        (owners.map (fun d =>
          (((Digraph.GlobalSibling.emitAll T).1).row d).length)).sum ≤
          g.arcCount :=
      (Digraph.GlobalSibling.emitAll_sum_nodup_row_lengths T owners hn).1
    unfold StaticOriginalSiblingEmitter.emitAll
    apply physical
  simp only [get_ofPrepared_arcCount]
  simpa only [owners, List.map_ofFn, Function.comp_def] using hm

theorem totalVertices_add_totalArcs_ofPrepared_le
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read) :
    (ofPrepared q rows childOK p progress injective spec).totalVertices +
      (List.ofFn (fun u : Fin q.count =>
        ((ofPrepared q rows childOK p progress injective spec).get u).graph.arcCount
      )).sum ≤ 2 * q.count + g.arcCount :=
  Nat.add_le_add
    (totalVertices_ofPrepared_le q rows childOK p progress injective spec hg)
    (totalArcs_ofPrepared_le q rows childOK p progress injective spec)

/-- The retained index has at most nine array entries per stored local vertex. -/
theorem ForestIndex.arraySize_build_ofPrepared_le
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read) :
    (ForestIndex.build (ofPrepared q rows childOK p progress injective spec)).arraySize ≤
      18 * q.count := by
  refine Nat.le_trans
    (ForestIndex.arraySize_build_le (ofPrepared q rows childOK p progress injective spec))
    ?_
  simpa only [← Nat.mul_assoc] using
    (Nat.mul_le_mul_left 9
      (totalVertices_ofPrepared_le q rows childOK p progress injective spec hg))

end Prepared

section Grouped

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r)

abbrev emittedChildBuckets : ChildLists q.count :=
  (groupedChildLists q.input.root q.input.parent.read).1

/-- Build the layout from the emitted buckets in their existing list order. -/
def emittedChildLayout : DenseQuotientRows.Layout (emittedChildBuckets q) :=
  DenseQuotientRows.ofBuckets q.input.root q.input.parent.read
    (emittedChildBuckets q)
    (groupedChildLists_get q.input.root q.input.parent.read)

private theorem emittedChildOK (d c : Fin q.count) :
    c ∈ (emittedChildBuckets q).get d ↔
      c ≠ q.input.root ∧ q.input.parent.read c = d :=
  mem_groupedChildLists_iff q.input.root q.input.parent.read d c

private theorem emittedChildLayout_hasCanonicalBuckets :
    HasCanonicalBuckets (emittedChildLayout q) q.input.root q.input.parent.read :=
  groupedChildLists_get q.input.root q.input.parent.read

variable (b : BoundKahnOrder g)
variable (progress : ∀ x y : Fin g.vertexCount,
  g.HasArc x y → b.rankRead x < b.rankRead y)
variable (injective : ∀ ⦃x y : Fin g.vertexCount⦄,
  b.rankRead x = b.rankRead y → x = y)
variable (spec : ParentSpec g r q.parent)

def ofGroupedChildLists : Family q.count :=
  prepare q (emittedChildLayout q) (emittedChildOK q) b progress injective spec

theorem totalVertices_ofGroupedChildLists_exact :
    (ofGroupedChildLists q b progress injective spec).totalVertices =
      q.count + (q.count - 1) := by
  unfold ofGroupedChildLists prepare
  apply totalVertices_ofPrepared_exact
  exact emittedChildLayout_hasCanonicalBuckets q

theorem totalVertices_ofGroupedChildLists_le :
    (ofGroupedChildLists q b progress injective spec).totalVertices ≤
      2 * q.count := by
  unfold ofGroupedChildLists prepare
  apply totalVertices_ofPrepared_le
  exact emittedChildLayout_hasCanonicalBuckets q

theorem ForestIndex.arraySize_build_ofGroupedChildLists_le :
    (ForestIndex.build (ofGroupedChildLists q b progress injective spec)).arraySize ≤
      18 * q.count := by
  unfold ofGroupedChildLists prepare
  apply ForestIndex.arraySize_build_ofPrepared_le
  exact emittedChildLayout_hasCanonicalBuckets q

end Grouped

end PaperB.RankedDenseLocal
