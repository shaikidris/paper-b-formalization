import PaperB.ForestBuildPackedWords
import PaperB.ForestPackedAfterHit

namespace PaperB.ForestPreparedBuild

open _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.RetainedProperLoss

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

/-- The word image produced before a query is named has the same membership
answer as the proven prepared reader when fed the fixed worker's exact hit. -/
theorem buildWords_afterHit_spec (large : 3 ≤ H.vertexCount) (q : CutPair H) (v : Vertex H) :
    let r := readerForWords data size_data rank increasing covers rankArc flat large
    let cap := local_word_columns_fit H.vertexCount
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    let hit := (PairLookup.lookup (ofOrderedReader r).dict (orderedPairCode q)).1
    buildWords data size_data rank increasing covers rankArc flat = some w ∧
      (w.afterHit rep.valid hit (encodeBackPair (some q)) v.val = true ↔
        q.fst < q.snd ∧ H.ProperLoss q v) := by
  intro r cap w rep hit
  refine ⟨buildWords_of_large data size_data rank increasing covers rankArc flat large, ?_⟩
  have same := packWordColumns_afterHit r cap q v.val
  dsimp only at same
  change w.afterHit rep.valid hit (encodeBackPair (some q)) v.val = true ↔ _
  rw [same]
  have spec := query_iff data size_data rank increasing covers rankArc flat q v
  rw [build_of_large_readerForWords data size_data rank increasing covers rankArc flat large] at spec
  exact spec

theorem buildWords_query_domain (q : CutPair H) :
    ∃ w, buildWords data size_data rank increasing covers rankArc flat = some w := by
  have large : 3 ≤ H.vertexCount := by
    by_cases h : 3 ≤ H.vertexCount
    · exact h
    · exact (PaperB.SmallQuotient.cutPair_impossible_of_small (by omega) q).elim
  exact ⟨_, buildWords_of_large data size_data rank increasing covers rankArc flat large⟩

end PaperB.ForestPreparedBuild
