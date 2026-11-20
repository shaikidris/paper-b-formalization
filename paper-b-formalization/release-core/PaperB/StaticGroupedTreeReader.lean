import PaperB.FastOriginalChildBuckets
import PaperB.StaticTreeReader

namespace PaperB.StaticGroupedTreeReader

open ForestLayout ForestHeavyPath LabelledQuotient StaticHeadSweep
open PackedStaticLayout (Input InputOK Built Endpoints tabulate read_tabulate)

set_option maxHeartbeats 1000000

variable {N : Nat}

private theorem childLists_ext {g h : ChildLists N}
    (rowsEq : ∀ u, g.get u = h.get u) : g = h := by
  have e : g.rows = h.rows := by
    apply Array.ext
    · rw [g.rows_size, h.rows_size]
    · intro i hi _
      have hN : i < N := by simpa only [g.rows_size] using hi
      exact rowsEq ⟨i, hN⟩
  cases g with
  | mk a ha =>
    cases h with
    | mk b hb =>
      change a = b at e
      subst b
      rfl

private def layoutOn (x : Input N) (g : ChildLists N) : Built N :=
  let s := layout g x.root (2 * N)
  let e : Endpoints N :=
    { entry := ⟨s.entries, s.entries_size⟩
      stop := ⟨s.ends, s.ends_size⟩ }
  let sizes := tabulate fun v => e.stop.read v - e.entry.read v
  let heavy := tabulate fun u =>
    (ForestHeavyPath.scan sizes.read (g.get u)).best.map (fun w => w.node)
  { packed :=
      { root := x.root
        parent := x.parent
        depth := x.depth
        heavy := heavy
        size := sizes }
    endpoints := e
    buckets := g }

def buildLayout (x : Input N) : Built N :=
  layoutOn x (groupedChildLists x.root x.parent.read).1

theorem buildLayout_eq (x : Input N) :
    buildLayout x = PackedStaticLayout.build x := by
  have hg : (groupedChildLists x.root x.parent.read).1 =
      bucketChildLists x.root x.parent.read :=
    childLists_ext (groupedChildLists_get_eq_bucketChildLists
      x.root x.parent.read)
  unfold buildLayout
  rw [hg] <;> rfl

open StaticLinearHead

private def completedRowOn (b : Built N) (u : Fin N) :
    Array (StaticChildLookup.Child (Fin N)) :=
  ExactOrderedChildIntervals.fromCompleted b.buckets
    b.endpoints.entry.data b.endpoints.stop.data
    b.endpoints.entry.len b.endpoints.stop.len u

private def readerOn (x : Input N) (ht : InputOK x) (b : Built N)
    (hb : b = PackedStaticLayout.build x) : StaticTreeReader.Reader x :=
  let s := sweepEntries b.packed b.endpoints.entry (by
    subst b
    exact entry_lt x ht)
  let rows := tabulate (completedRowOn b)
  { layout := b
    tables :=
      { root := b.packed.root
        parent := b.packed.parent.read
        depth := b.packed.depth.read
        heavy := b.packed.heavy.read
        head := s.heads.read
        size := b.packed.size.read }
    ranges := rows
    input_ok := ht
    layout_exact := hb
    tables_exact := by
      have hs : s = StaticHeadSweep.build b.packed := by
        subst b
        exact sweepEntries_eq x ht
      rw [hs] <;> rfl
    ranges_exact := read_tabulate (completedRowOn b) }

private theorem readerOn_eq (x : Input N) (ht : InputOK x) (b : Built N)
    (hb : b = PackedStaticLayout.build x) :
    readerOn x ht b hb = StaticTreeReader.build x ht := by
  subst b
  rfl

def build (x : Input N) (ht : InputOK x) : StaticTreeReader.Reader x :=
  readerOn x ht (buildLayout x) (buildLayout_eq x)

theorem build_eq (x : Input N) (ht : InputOK x) :
    build x ht = StaticTreeReader.build x ht :=
  readerOn_eq x ht (buildLayout x) (buildLayout_eq x)

end PaperB.StaticGroupedTreeReader
