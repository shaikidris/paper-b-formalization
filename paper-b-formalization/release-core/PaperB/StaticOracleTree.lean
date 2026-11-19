import PaperB.DomFromOriginal
import PaperB.StaticFromDominators
import PaperB.StaticTreeReader

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB.EX16Assembly

open EX15 EX15.WholeScan EX15.WholeScan.PackedInput
open JumpForestCommonAncestor
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath

universe u

-- Only the root and parent fields are used by EX16.Anc.
private def bridgeTables {N : Nat} (x : PackedStaticLayout.Input N) :
    EX16.Tables (Fin N) :=
  { root := x.root
    parent := x.parent.read
    depth := x.depth.read
    heavy := fun _ => none
    head := id
    size := fun _ => 0 }

/-- Iteration may take extra steps at the root; an EX16 path omits them. -/
theorem parentIter_iff_readerAncestor {N : Nat}
    (x : PackedStaticLayout.Input N)
    (hroot : x.parent.read x.root = x.root) (a v : Fin N) :
    EX15.WholeScan.PackedInput.SemanticAncestor x a v ↔
      StaticTreeReader.SemanticAncestor x a v := by
  change (∃ k, parentIter x k v = a) ↔ EX16.Anc (bridgeTables x) a v
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing v with
    | zero =>
        change v = a at hk
        subst v
        exact EX16.Path.refl
    | succ k ih =>
        change parentIter x k (x.parent.read v) = a at hk
        by_cases hn : v = x.root
        · subst v
          rw [hroot] at hk
          exact ih x.root hk
        · exact EX16.Path.step (b := v) hn True.intro
            (ih (x.parent.read v) hk)
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @step b _ _ _ ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨k + 1, ?_⟩
        change parentIter x k (x.parent.read b) = a
        exact hk

section Scan

variable {α : Type u} {g : Digraph} {R : JumpWordRegion}
variable {r : Fin g.vertexCount} {s : ScanState}

private theorem scanRoot_fixed {S : Fin g.vertexCount → Prop}
    (C : Certified α R r S s) :
    (scanInput C).parent.read (scanInput C).root = (scanInput C).root := by
  have C' := C
  obtain ⟨F, I⟩ := C'
  have hLayout : JumpWordLayout R F s.words := I.layout
  have hExists : ∃ J, JumpWordLayout R J s.words := ⟨F, hLayout⟩
  have hp :
      ((scanInput C).parent.read (scanInput C).root).val =
        F.parentOf (scanInput C).root.val :=
    ofWords_parent hLayout hExists (scanInput C).root
  have hz : (scanInput C).root.val = 0 := rfl
  obtain ⟨_, inv⟩ := hLayout.valid.exists_forestInvariant
  apply Fin.ext
  simpa only [hp, hz] using inv.root_parent

/-- The scan's original-vertex map supplies the two indices into the reader. -/
theorem scan_dominates_iff_interval {S : Fin g.vertexCount → Prop}
    (C : Certified α R r S s) (q : StaticTreeReader.Reader (scanInput C))
    {a v : Fin g.vertexCount} (ha : S a) (hv : S v) :
    g.Dominates r a v ↔
      q.entry (scanSlot C a ha) ≤ q.entry (scanSlot C v hv) ∧
      q.entry (scanSlot C v hv) < q.stop (scanSlot C a ha) :=
  (dominates_iff_semanticAncestor C ha hv).trans
    ((parentIter_iff_readerAncestor (scanInput C) (scanRoot_fixed C)
      (scanSlot C a ha) (scanSlot C v hv)).trans
      (q.ancestor_iff_interval (scanSlot C a ha) (scanSlot C v hv)))

end Scan

structure OriginalReader (g : Digraph) (r : Fin g.vertexCount) where
  count : Nat
  input : PackedStaticLayout.Input count
  reader : StaticTreeReader.Reader input
  slot : (v : Fin g.vertexCount) → g.InitiallyReachable r v → Fin count
  dominates_iff_interval :
    ∀ (a v : Fin g.vertexCount)
      (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v),
      g.Dominates r a v ↔
        reader.entry (slot a ha) ≤ reader.entry (slot v hv) ∧
        reader.entry (slot v hv) < reader.stop (slot a ha)

private def ofScan {α : Type u} {g : Digraph} {R : JumpWordRegion}
    {r : Fin g.vertexCount} {s : ScanState}
    (C : Certified α R r (g.InitiallyReachable r) s) : OriginalReader g r :=
  let x := scanInput C
  let q := PaperB.StaticTreeReader.build x (scanInput_ok C)
  { count := occupied R s.words
    input := x
    reader := q
    slot := scanSlot C
    dominates_iff_interval := fun _ _ ha hv =>
      scan_dominates_iff_interval C q ha hv }

/-- Run the original DAG scan once and build one reader from its word image.
The scan specification supplies only an erased certificate. -/
def fromOriginal (g : Digraph) (r : Fin g.vertexCount)
    (hacyc : EX15.GraphAcyclic g) {L : Nat} (hL : g.vertexCount + 2 ≤ 2 ^ L)
    (rootReach : g.InitiallyReachable r r)
    (rootDom : ∀ d, g.Dominates r d r ↔ d = r) : OriginalReader g r :=
  let out := EX15.runGraph g r hacyc
  let C := certifiedOfSpec
    (α := EX15.OriginalOccurrence g) (g := g) (r := r)
    (S := g.InitiallyReachable r) (s := out.state)
    (EX15.runGraph_spec g r hacyc hL rootReach rootDom)
  ofScan C

theorem fromOriginal_dominates_iff_interval
    (g : Digraph) (r : Fin g.vertexCount)
    (hacyc : EX15.GraphAcyclic g) {L : Nat} (hL : g.vertexCount + 2 ≤ 2 ^ L)
    (rootReach : g.InitiallyReachable r r)
    (rootDom : ∀ d, g.Dominates r d r ↔ d = r)
    {a v : Fin g.vertexCount}
    (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v) :
    let q := fromOriginal g r hacyc hL rootReach rootDom
    g.Dominates r a v ↔
      q.reader.entry (q.slot a ha) ≤ q.reader.entry (q.slot v hv) ∧
      q.reader.entry (q.slot v hv) < q.reader.stop (q.slot a ha) :=
  (fromOriginal g r hacyc hL rootReach rootDom).dominates_iff_interval a v ha hv

namespace OriginalReader

variable {g : Digraph} {r : Fin g.vertexCount}

/-- Query the stored reader directly on the two translated original IDs. -/
def dominates (q : OriginalReader g r) (a v : Fin g.vertexCount)
    (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v) : Bool :=
  q.reader.isAncestor (q.slot a ha) (q.slot v hv)

theorem dominates_exact (q : OriginalReader g r) (a v : Fin g.vertexCount)
    (ha : g.InitiallyReachable r a) (hv : g.InitiallyReachable r v) :
    g.Dominates r a v ↔ q.dominates a v ha hv = true :=
  (q.dominates_iff_interval a v ha hv).trans
    ((q.reader.ancestor_iff_interval (q.slot a ha) (q.slot v hv)).symm.trans
      (q.reader.isAncestor_exact (q.slot a ha) (q.slot v hv)).symm)

end OriginalReader
end PaperB.EX16Assembly
