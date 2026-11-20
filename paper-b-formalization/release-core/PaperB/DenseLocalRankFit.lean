import PaperB.RankedDenseLocal

namespace PaperB.DenseQuotientLocalOrder

open EX51
open PaperB.DenseQuotientRows PaperB.EX16Assembly
open Kahn StaticLinearHead StaticHeadSweep ForestLayout

variable {g : Digraph} {r : Fin g.vertexCount}

theorem slotRank_rankRead_lt_vertexCount
    (q : OriginalReader g r)
    (buckets : ChildLists q.count)
    (rows : DenseQuotientRows.Layout buckets)
    (u : Fin q.count)
    (i : Fin (rows.length u))
    (b : BoundKahnOrder g) :
    slotRank q rows b.rankRead u i < g.vertexCount := by
  unfold slotRank BoundKahnOrder.rankRead
  exact Fin.isLt _

theorem slotRank_rankRead_lt_wordDomain
    (q : OriginalReader g r)
    (buckets : ChildLists q.count)
    (rows : DenseQuotientRows.Layout buckets)
    (u : Fin q.count) (i : Fin (rows.length u))
    (b : BoundKahnOrder g) (bits : Nat)
    (h : g.vertexCount ≤ 2 ^ bits) :
    slotRank q rows b.rankRead u i < 2 ^ bits :=
  Nat.lt_of_lt_of_le (slotRank_rankRead_lt_vertexCount q buckets rows u i b) h

end PaperB.DenseQuotientLocalOrder
