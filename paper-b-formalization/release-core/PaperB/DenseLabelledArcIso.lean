import PaperB.DenseRuntimeGraph
import PaperB.DensePackingCode

namespace PaperB.DenseOriginalQuotient

open Digraph PaperB.EX16Assembly
open PackedStaticLayout StaticOriginalSiblingEmitter
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open PaperB.DenseQuotientRows PaperB.DenseArcRecode PaperB.Digraph.GlobalSibling

variable {g : Digraph} {r : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (q : OriginalReader g r) (u : Fin q.count)
variable {buckets : ChildLists q.count}
variable (rows : DenseQuotientRows.Layout buckets)
variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)

private theorem positionChildOK
    (h : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (c : Fin q.count) :
    c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u := by
  constructor
  · intro hc
    obtain ⟨hnonroot, hparent⟩ := (h u c).mp hc
    refine ⟨hparent, ?_⟩
    intro hcu
    have hself : q.input.parent.read c = c := hparent.trans hcu.symm
    have hdepth := q.reader.input_ok.depth_step c hnonroot
    first
    | rw [hself] at hdepth <;> omega
    | erw [hself] at hdepth <;> omega
  · rintro ⟨hparent, hne⟩
    refine (h u c).mpr ⟨?_, hparent⟩
    intro hc
    apply hne
    subst c
    have hroot : q.input.parent.read q.input.root = q.input.root :=
      q.reader.input_ok.parent_root
    exact hroot.symm.trans hparent

private def canonicalEntry (a : Arc g)
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (tail : Fin g.vertexCount) : Digraph.GlobalSibling.Entry g (2 * q.count) :=
  ⟨{ source := StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) src
     destination := StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) dst
     tail := tail }, a⟩

/-- The shared emitter row in its original order, with all occurrences retained. -/
private theorem emitted_eq_canonical
    (originalRows : EX51.Rows g.vertexCount
      (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (hd : g.InitiallyReachable r (q.ids.originals.read u))
    (hFind : q.ids.find (q.ids.originals.read u) = some u)
    (spec : _) :
    emitted q originalRows u =
      g.originalArcOccurrences.filterMap (fun a =>
        (siblingEmission? (d := q.ids.originals.read u)
          progress injective spec a).map (fun s =>
            canonicalEntry q u a s.source s.destination s.tail)) := by
  unfold emitted
  rw [hRows]
  unfold canonicalEntry
  exact Digraph.GlobalSibling.emitAll_row progress injective spec
    (getters q) (packing q) (checked progress injective q)
    (q.ids.originals.read u)

private theorem slots_and_label_iff
    (s t : Fin (2 * q.count))
    (hs : Occurs buckets u ((halves q.count).unpack s))
    (ht : Occurs buckets u ((halves q.count).unpack t))
    (label : Fin g.vertexCount)
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (tail : Fin g.vertexCount)
    (hsrc : s = StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) src)
    (hdst : t = StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) dst)
    (htail : label = tail)
    (v w : Fin (rows.length u)) (l : Fin g.vertexCount) :
    (DenseArcRecode.slot (halves q.count) rows u s hs = v ∧
      DenseArcRecode.slot (halves q.count) rows u t ht = w ∧ label = l) ↔
    (src = positionToOriginal q u (positionChildOK q u childOK) rows v ∧
      dst = positionToOriginal q u (positionChildOK q u childOK) rows w ∧
      tail = l) := by
  subst s
  subst t
  subst label
  have hp := packedEmission_positions (q := q) (u := u)
    (childOK := positionChildOK q u childOK) (rows := rows) src dst hs ht
  have hp₁ := congrArg Prod.fst hp
  have hp₂ := congrArg Prod.snd hp
  dsimp only at hp₁ hp₂
  rw [hp₁, hp₂]
  constructor
  · rintro ⟨hv, hw, hl⟩
    refine ⟨?_, ?_, hl⟩
    · simpa only [positionToOriginal_originalToPosition] using
        congrArg (positionToOriginal q u (positionChildOK q u childOK) rows) hv
    · simpa only [positionToOriginal_originalToPosition] using
        congrArg (positionToOriginal q u (positionChildOK q u childOK) rows) hw
  · rintro ⟨hv, hw, hl⟩
    refine ⟨?_, ?_, hl⟩
    · simpa only [originalToPosition_positionToOriginal] using
        congrArg (originalToPosition q u (positionChildOK q u childOK) rows) hv
    · simpa only [originalToPosition_positionToOriginal] using
        congrArg (originalToPosition q u (positionChildOK q u childOK) rows) hw

private theorem occurrenceAt_canonical_iff
    (xs : List (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (own : PackedLocalArcs.Valid (physical xs) q.input.root q.input.parent.read u)
    (i : Fin (physical xs).size)
    (a : Arc g)
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (tail : Fin g.vertexCount)
    (hi : xs[i.val]'(by simpa [physical] using i.isLt) =
      canonicalEntry q u a src dst tail)
    (v w : Fin (rows.length u)) (l : Fin g.vertexCount) :
    (let o := occurrenceAt (q := q) u rows childOK (physical xs) own i
     o.«from» = v ∧ o.«to» = w ∧ o.origTail = l) ↔
    (src = positionToOriginal q u (positionChildOK q u childOK) rows v ∧
      dst = positionToOriginal q u (positionChildOK q u childOK) rows w ∧
      tail = l) := by
  dsimp only [occurrenceAt, PackedLocalArcs.induced]
  apply slots_and_label_iff (q := q) (u := u) (rows := rows) (childOK := childOK)
  · simpa [physical, canonicalEntry] using
      congrArg (fun x => x.emission.source) hi
  · simpa [physical, canonicalEntry] using
      congrArg (fun x => x.emission.destination) hi
  · simpa [physical, canonicalEntry] using
      congrArg (fun x => x.emission.tail) hi

/-- Exact labeled membership in the fast quotient built from the shared original
rows. The witness uses the original keys decoded at both dense positions and
the unchanged original tail. -/
theorem mem_outArcs_build_iff
    (originalRows : EX51.Rows g.vertexCount
      (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (hd : g.InitiallyReachable r (q.ids.originals.read u))
    (hFind : q.ids.find (q.ids.originals.read u) = some u)
    (hzero : 0 < rows.length u)
    (v : Fin (rows.length u)) (e : QuotientArc g.vertexCount (rows.length u))
    (spec : _) :
    e ∈ (build progress injective q originalRows hRows u hd hFind
      rows childOK hzero).outArcs v ↔
      ∃ a ∈ g.originalArcOccurrences, ∃ s,
        siblingEmission? (d := q.ids.originals.read u) progress injective spec a =
          some s ∧
        s.source = positionToOriginal q u (positionChildOK q u childOK) rows v ∧
        s.destination = positionToOriginal q u (positionChildOK q u childOK) rows e.head ∧
        s.tail = e.origTail := by
  let xs := emitted q originalRows u
  have hrow := emitted_eq_canonical progress injective q u originalRows hRows hd hFind spec
  change xs = _ at hrow
  have own : PackedLocalArcs.Valid (physical xs)
      q.input.root q.input.parent.read u := by
    intro i
    have hi : i.val < xs.length := by simpa [physical] using i.isLt
    have hm : xs[i.val]'hi ∈
        (StaticOriginalSiblingEmitter.emitAll q).1.row (q.ids.originals.read u) := by
      rw [← hRows]
      exact List.getElem_mem hi
    simpa [physical, hFind] using
      (Digraph.GlobalSibling.ActualOwnership.emitAll_row_own
        progress injective q hd hm)
  unfold build
  rw [FastQuotientRows.mem_outArcs_ofOccurrences]
  change (∃ o ∈ List.ofFn (occurrenceAt (q := q) u rows childOK (physical xs) own),
    o.«from» = v ∧ o.«to» = e.head ∧ o.origTail = e.origTail) ↔ _
  constructor
  · rintro ⟨o, ho, h⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
    have hi : i.val < xs.length := by simpa [physical] using i.isLt
    have hm : xs[i.val]'hi ∈ xs := List.getElem_mem hi
    have hm' := Eq.mp (congrArg (fun ys => xs[i.val]'hi ∈ ys) hrow) hm
    obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hm'
    cases hs : siblingEmission? (d := q.ids.originals.read u)
        progress injective spec a with
    | none => simp [hs] at he
    | some s =>
      have hentry : xs[i.val]'hi =
          canonicalEntry q u a s.source s.destination s.tail := by
        symm
        simpa [hs] using he
      exact ⟨a, ha, s, hs,
        (occurrenceAt_canonical_iff q u rows childOK xs own i
          a s.source s.destination s.tail hentry v e.head e.origTail).mp h⟩
  · rintro ⟨a, ha, s, hs, h⟩
    have hm : canonicalEntry q u a s.source s.destination s.tail ∈ xs := by
      rw [hrow]
      exact List.mem_filterMap.mpr ⟨a, ha, by simp [hs]⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
    let i : Fin (physical xs).size := ⟨j, by simpa [physical] using hj⟩
    have hentry : xs[i.val]'(by simpa [physical] using i.isLt) =
        canonicalEntry q u a s.source s.destination s.tail := by
      first | exact hget | exact hget.symm
    exact ⟨occurrenceAt (q := q) u rows childOK (physical xs) own i,
      List.mem_ofFn.mpr ⟨i, rfl⟩,
      (occurrenceAt_canonical_iff q u rows childOK xs own i
        a s.source s.destination s.tail hentry v e.head e.origTail).mpr h⟩

end PaperB.DenseOriginalQuotient
