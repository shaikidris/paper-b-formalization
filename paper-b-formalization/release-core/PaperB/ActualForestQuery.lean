import PaperB.ForestLayoutRefine
import PaperB.ForestIntervalQuery
import PaperB.PairLookup

namespace PaperB

open PaperB.ForestLayout

section ProperLossRetainedLookup

open LabelledQuotient PaperB.ForestIntervalQuery

variable {H : LabelledQuotient} {rank : Fin H.vertexCount → Nat}

abbrev properLossRetainedNodeCount
    (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) : Nat :=
  (buildProperLossForest H rank).realNodeCount + 1

/-- Construct the buckets and certify their indexed reads at the same time. -/
private def retainedChildListsOfFn {N : Nat}
    (f : Fin N → List (Fin N)) :
    {g : ChildLists N // ∀ v, g.get v = f v} := by
  have hRead (v : Fin N) :
      (Array.ofFn f)[v.val]'(by simpa using v.isLt) = f v := by
    simp
  first
  | exact ⟨⟨Array.ofFn f, by simp⟩, hRead⟩
  | exact ⟨⟨⟨Array.ofFn f, by simp⟩⟩, hRead⟩
  | exact ⟨⟨f⟩, fun _ => rfl⟩
  | exact ⟨f, fun _ => rfl⟩
  | exact ⟨⟨Array.ofFn f, by simp⟩, by
      intro v
      simpa [ChildLists.get, v.isLt] using hRead v⟩

def properLossRetainedBuckets
    (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    ChildLists (properLossRetainedNodeCount H rank) :=
  let F := buildProperLossForest H rank
  (retainedChildListsOfFn (bucketChildren F.rootNode F.parent)).val

theorem properLossRetainedBuckets_get
    (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (v : Fin (properLossRetainedNodeCount H rank)) :
    (properLossRetainedBuckets H rank).get v =
      (let F := buildProperLossForest H rank
       bucketChildren F.rootNode F.parent v) :=
  let F := buildProperLossForest H rank
  (retainedChildListsOfFn (bucketChildren F.rootNode F.parent)).property v

/-- Retain the two arrays from the executable layout and the computed labels. -/
def properLossRetainedTables
    (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    Tables (properLossRetainedNodeCount H rank) H.vertexCount :=
  let F := buildProperLossForest H rank
  let N := F.realNodeCount + 1
  let g := (retainedChildListsOfFn (bucketChildren F.rootNode F.parent)).val
  let labels := Array.ofFn F.label
  let s := layout g F.rootNode (2 * N)
  { entries := s.entries
    ends := s.ends
    labels := labels
    entries_size := s.entries_size
    ends_size := s.ends_size
    labels_size := by simp [labels] }

theorem properLossRetainedTables_layout
    (rankArc : ∀ u v : Fin H.vertexCount,
      H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    ProperLossLayout H rank (properLossRetainedTables H rank) := by
  let F := buildProperLossForest H rank
  let g := properLossRetainedBuckets H rank
  have hTree := buildProperLossForest_validDepthTree rankArc flat
  have hc := layout_bucket_correct g F.rootNode F.parent F.depth
    hTree (properLossRetainedBuckets_get H rank)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (hc.2.2 a).1
  · intro a
    exact (hc.2.2 a).2
  · intro y
    change (Array.ofFn F.label)[y.val]'(by simpa using y.isLt) = F.label y
    simp

theorem properLossRetainedTables_query
    (rankArc : ∀ u v : Fin H.vertexCount,
      H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {a : Fin (properLossRetainedNodeCount H rank)} {P : CutPair H}
    (ha : (buildProperLossForest H rank).nodeKey? a = some P)
    (y : Fin H.vertexCount) :
    query (properLossRetainedTables H rank) a y = true ↔ H.ProperLoss P y :=
  query_eq_true_iff_properLoss_of_node rankArc distinctRanks flat
    (properLossRetainedTables_layout rankArc flat) ha y

/-- One retained word per array slot, including the synthetic root's slots. -/
theorem properLossRetainedTables_words
    (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    let T := properLossRetainedTables H rank
    T.entries.size + T.ends.size + T.labels.size =
      2 * properLossRetainedNodeCount H rank + H.vertexCount := by
  let T := properLossRetainedTables H rank
  change T.entries.size + T.ends.size + T.labels.size =
    2 * properLossRetainedNodeCount H rank + H.vertexCount
  rw [T.entries_size, T.ends_size, T.labels_size, Nat.two_mul]


/-- Read addresses of `query`, in order. This trace is not retained. -/
inductive ProperLossRead (N V : Nat) where
  | label : Fin V → ProperLossRead N V
  | entry : Fin N → ProperLossRead N V
  | stop : Fin N → ProperLossRead N V

def properLossQueryReads {N V : Nat}
    (T : Tables N V) (a : Fin N) (y : Fin V) : List (ProperLossRead N V) :=
  [.label y, .entry a, .entry (T.readLabel y), .stop a]

theorem properLossQueryReads_exact {N V : Nat}
    (T : Tables N V) (a : Fin N) (y : Fin V) :
    (properLossQueryReads T a y).length = 4 :=
  rfl

/-- On a hit, read the parallel node-ID array once, without rereading the key. -/
def queryFromPairLookupResult {N V M : Nat}
    (T : Tables N V)
    (nodeIDs : Array (Fin N)) (hSize : nodeIDs.size = M)
    (hit : Option (Fin M)) (y : Fin V) : Bool :=
  match hit with
  | none => false
  | some i =>
    query T (nodeIDs[i.val]'(by rw [hSize]; exact i.isLt)) y

/-- The supplied dictionary provides the parallel-array certificate and
the hit/miss facts for its lookup result. The forest tables are computed. -/
theorem queryFromPairLookupResult_iff
    (rankArc : ∀ u v : Fin H.vertexCount,
      H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {Key : Type} (encode : CutPair H → Key)
    (keys : Array Key)
    (nodeIDs : Array (Fin (properLossRetainedNodeCount H rank)))
    (hSize : nodeIDs.size = keys.size)
    (hIDs : ∀ (i : Fin keys.size) (P : CutPair H),
      keys[i.val]'(i.isLt) = encode P →
      (buildProperLossForest H rank).nodeKey?
        (nodeIDs[i.val]'(by rw [hSize]; exact i.isLt)) = some P)
    (P : CutPair H)
    (hit : Option (Fin keys.size))
    (hHit : ∀ i, hit = some i → keys[i.val]'(i.isLt) = encode P)
    (hMiss : hit = none → ∀ i : Fin keys.size, keys[i.val]'(i.isLt) ≠ encode P)
    (y : Fin H.vertexCount) :
    queryFromPairLookupResult (properLossRetainedTables H rank)
      nodeIDs hSize hit y = true ↔
      (∃ i : Fin keys.size, keys[i.val]'(i.isLt) = encode P) ∧ H.ProperLoss P y := by
  cases hit with
  | none =>
    constructor
    · intro hf
      change false = true at hf
      cases hf
    · rintro ⟨⟨i, hi⟩, _⟩
      exact (hMiss rfl i hi).elim
  | some i =>
    have hk := hHit i rfl
    have hq := properLossRetainedTables_query
      rankArc distinctRanks flat (hIDs i P hk) y
    constructor
    · intro hs
      exact ⟨⟨i, hk⟩, hq.mp hs⟩
    · intro hs
      exact hq.mpr hs.2

end ProperLossRetainedLookup

end PaperB
