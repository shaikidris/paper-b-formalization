import PaperB.DenseRuntimeGraph
import PaperB.FiniteSiblingBudget

namespace PaperB.FastQuotientRows

open PaperB.QuotientArrays (ArcOccurrence)
variable {n k : Nat}

private theorem listLengthSum_eq_sum (xs : List (List (QuotientArc n k))) :
    listLengthSum xs = (xs.map List.length).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listLengthSum, List.map_cons, List.sum_cons, ih]

theorem arcCount_ofOccurrences (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) :
    (ofOccurrences root occurrences).arcCount = occurrences.length := by
  let s := (EX51.groupMap (fun a : ArcOccurrence n k => a.«from»)
    ArcOccurrence.toQuotientArc occurrences).1
  calc
    (ofOccurrences root occurrences).arcCount = EX51.Storage.rowMass s := by
      change listLengthSum s.cells.toList = EX51.Storage.rowMass s
      rw [EX51.Storage.rowMass_eq_cells_sum, listLengthSum_eq_sum]
    _ = occurrences.length :=
      EX51.Storage.groupMap_rowMass (fun a : ArcOccurrence n k => a.«from»)
        ArcOccurrence.toQuotientArc occurrences

end PaperB.FastQuotientRows

namespace PaperB.DenseOriginalQuotient

open Digraph PaperB.EX16Assembly
open PackedStaticLayout StaticOriginalSiblingEmitter
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open PaperB.DenseQuotientRows
variable {g : Digraph} {r : Fin g.vertexCount} {rank : Fin g.vertexCount → Nat}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (q : OriginalReader g r)
variable (originalRows : EX51.Rows g.vertexCount
  (Digraph.GlobalSibling.Entry g (2 * q.count)))
variable (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
variable (u : Fin q.count)
variable (hd : g.InitiallyReachable r (q.ids.originals.read u))
variable (hFind : q.ids.find (q.ids.originals.read u) = some u)

variable {buckets : ChildLists q.count}
variable (rows : DenseQuotientRows.Layout buckets)
variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)

theorem arcCount_build (hzero : 0 < rows.length u) :
    (build progress injective q originalRows hRows u hd hFind rows childOK
      hzero).arcCount = (emitted q originalRows u).length := by
  calc
    _ = (occurrences progress injective q originalRows hRows u hd hFind
          rows childOK).length :=
      FastQuotientRows.arcCount_ofOccurrences ⟨0, hzero⟩ _
    _ = _ := by
      simpa only [List.length_map] using
        congrArg List.length
          (occurrence_labels progress injective q originalRows hRows u hd hFind
            rows childOK)

theorem arcCount_build_eq_emitAll_row_length (hzero : 0 < rows.length u) :
    (build progress injective q originalRows hRows u hd hFind rows childOK
      hzero).arcCount =
      (((StaticOriginalSiblingEmitter.emitAll q).1).row
        (q.ids.originals.read u)).length := by
  rw [arcCount_build progress injective q originalRows hRows u hd hFind
    rows childOK hzero]
  unfold emitted
  rw [hRows]


end PaperB.DenseOriginalQuotient
