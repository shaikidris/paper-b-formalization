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

/-- The retained index columns use at most nine words per stored local vertex. -/
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
