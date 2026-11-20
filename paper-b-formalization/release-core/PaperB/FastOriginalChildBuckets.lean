import PaperB.ArcBuckets
import PaperB.DenseQuotientRows

namespace PaperB.ForestLayout

open PaperB.LabelledQuotient

variable {N : Nat}

/-- Filter and reverse in one pass. The counter advances for every input
vertex, including the discarded root. -/
private def selectNonRootRev (root : Fin N) :
    List (Fin N) → List (Fin N) → Nat → List (Fin N) × Nat
  | [], acc, visits => (acc, visits)
  | u :: us, acc, visits =>
      selectNonRootRev root us (if u = root then acc else u :: acc)
        (visits + 1)

private theorem selectNonRootRev_spec (root : Fin N)
    (xs acc : List (Fin N)) (visits : Nat) :
    selectNonRootRev root xs acc visits =
      ((xs.filter (fun u => decide (u ≠ root))).reverse ++ acc,
        visits + xs.length) := by
  induction xs generalizing acc visits with
  | nil => simp [selectNonRootRev]
  | cons u us ih =>
      rw [selectNonRootRev, ih]
      by_cases hu : u = root
      · simp [hu] <;> omega
      · simp [hu, List.reverse_cons, List.append_assoc] <;> omega

/-- The old cons pass specifies a filtered row in reverse input order. -/
private theorem bucketPassAux_order (root : Fin N)
    (parent : Fin N → Fin N) (q : Fin N) (xs : List (Fin N))
    (acc : Fin N → List (Fin N)) :
    bucketPassAux root parent xs acc q =
      (((xs.filter (fun u => decide (u ≠ root))).reverse).filter
        (fun u => decide (parent u = q))) ++ acc q := by
  induction xs generalizing acc with
  | nil => rfl
  | cons u us ih =>
      rw [bucketPassAux, ih]
      by_cases hu : u = root
      · simp [addChildToBuckets, hu]
      · by_cases hp : parent u = q
        · simp [addChildToBuckets, hu, hp, List.reverse_cons,
            List.filter_append, List.append_assoc]
        · have hq : q ≠ parent u := fun e => hp e.symm
          simp [addChildToBuckets, hu, hp, hq, List.reverse_cons,
            List.filter_append]

/--
Construction charges only. A root-filter visit tests one vertex and conses
at most one retained vertex. There is no separate input-reversal pass.

`grouping` is the work returned by `EX51.groupMap`: initialized cells,
scatter reads and writes, reversed list cells, and finish-row visits.
Each finish-row visit includes a further row read and write, not counted
in the scatter fields. These are source-level charges, not machine costs.
They do not count generating `finElems`, the cost inside key evaluation,
subsequent row lookups, or the dense layout's `ofBuckets` scan.
-/
structure GroupedChildWork where
  rootFilterVisits : Nat
  grouping : EX51.Work
  deriving Repr

/-- Retain the physical array returned by one call to stable `groupMap`.
Feeding it the reversed non-root enumeration preserves the old cons order. -/
def groupedChildLists (root : Fin N) (parent : Fin N → Fin N) :
    ChildLists N × GroupedChildWork :=
  let input := selectNonRootRev root (finElems N) [] 0
  let grouped := EX51.groupMap parent id input.1
  (⟨grouped.1.cells, grouped.1.size_eq⟩, ⟨input.2, grouped.2⟩)

theorem groupedChildLists_get (root : Fin N) (parent : Fin N → Fin N)
    (q : Fin N) :
    (groupedChildLists root parent).1.get q = bucketChildren root parent q := by
  change
    (EX51.group parent (selectNonRootRev root (finElems N) [] 0).1).1.row q =
      bucketChildren root parent q
  rw [EX51.group_row, selectNonRootRev_spec]
  simpa [bucketChildren] using
    (bucketPassAux_order root parent q (finElems N) (fun _ => [])).symm

theorem groupedChildLists_get_eq_bucketChildLists (root : Fin N)
    (parent : Fin N → Fin N) (q : Fin N) :
    (groupedChildLists root parent).1.get q =
      (bucketChildLists root parent).get q :=
  (groupedChildLists_get root parent q).trans
    (bucketChildLists_get root parent q).symm

theorem mem_groupedChildLists_iff (root : Fin N) (parent : Fin N → Fin N)
    (q c : Fin N) :
    c ∈ (groupedChildLists root parent).1.get q ↔ c ≠ root ∧ parent c = q := by
  rw [groupedChildLists_get]
  exact mem_bucketChildren_iff root parent q c

private theorem childLists_eq_of_row_array_eq {g h : ChildLists N}
    (e : g.rows = h.rows) : g = h := by
  cases g with
  | mk a ha =>
    cases h with
    | mk b hb =>
      change a = b at e
      subst b
      rfl

theorem groupedChildLists_eq_bucketChildLists (root : Fin N)
    (parent : Fin N → Fin N) :
    (groupedChildLists root parent).1 = bucketChildLists root parent := by
  let g := (groupedChildLists root parent).1
  let h := bucketChildLists root parent
  change g = h
  apply childLists_eq_of_row_array_eq
  apply Array.ext
  · rw [g.rows_size, h.rows_size]
  · intro i hiG hiH
    have hi : i < N := by simpa only [g.rows_size] using hiG
    let q : Fin N := ⟨i, hi⟩
    change g.get q = h.get q
    exact groupedChildLists_get_eq_bucketChildLists root parent q

private theorem filter_nonRoot_of_not_mem (root : Fin N) (xs : List (Fin N))
    (hn : root ∉ xs) :
    xs.filter (fun u => decide (u ≠ root)) = xs := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
      have hu : u ≠ root := fun e =>
        hn (List.mem_cons.mpr (Or.inl e.symm))
      have ht : root ∉ us := fun hm =>
        hn (List.mem_cons.mpr (Or.inr hm))
      rw [List.filter_cons_of_pos (p := fun i : Fin N => decide (i ≠ root)) (a := u) (decide_eq_true hu), ih ht]

private theorem filter_nonRoot_length (root : Fin N) (xs : List (Fin N))
    (hn : xs.Pairwise (· ≠ ·)) (hm : root ∈ xs) :
    (xs.filter (fun u => decide (u ≠ root))).length + 1 = xs.length := by
  induction xs with
  | nil => nomatch hm
  | cons u us ih =>
      obtain ⟨hd, ht⟩ := List.pairwise_cons.mp hn
      by_cases hu : u = root
      · subst u
        have hnot : root ∉ us := fun h => hd root h rfl
        rw [List.filter_cons_of_neg (by simp), filter_nonRoot_of_not_mem root us hnot]
        rfl
      · have hmTail : root ∈ us :=
          (List.mem_cons.mp hm).resolve_left (fun e => hu e.symm)
        have hlen := ih ht hmTail
        simp [hu] <;> omega

/-- Exact returned counters: scan all `N` vertices, scatter and reverse
`N - 1` retained entries, and allocate and finish all `N` rows. -/
theorem groupedChildLists_work (root : Fin N) (parent : Fin N → Fin N) :
    (groupedChildLists root parent).2 =
      ⟨N, ⟨N, N - 1, N - 1, N - 1, N⟩⟩ := by
  have hl : ((finElems N).filter (fun u => decide (u ≠ root))).length = N - 1 := by
    have h := filter_nonRoot_length root (finElems N)
      (nodup_finElems N) (mem_finElems root)
    rw [length_finElems N] at h
    omega
  let input := selectNonRootRev root (finElems N) [] 0
  change GroupedChildWork.mk input.2 (EX51.groupMap parent id input.1).2 = _
  rw [EX51.groupMap_work]
  dsimp only [input]
  rw [selectNonRootRev_spec]
  simpa only [List.length_reverse, List.append_nil, length_finElems, Nat.zero_add, hl]

end PaperB.ForestLayout

namespace PaperB.DenseQuotientRows

open PaperB.ForestLayout PaperB.LabelledQuotient

variable {N : Nat}

/-- The layout is indexed by the physically grouped buckets, not by the
old bucket constructor. `bucketWork` accounts for bucketing only. -/
structure GroupedBuild (n : Nat) where
  buckets : ChildLists n
  layout : Layout buckets
  bucketWork : GroupedChildWork

/-- Share the one grouping result between the retained buckets and the
existing layout scan. The reference buckets occur only in proofs. -/
def buildGrouped (x : PackedStaticLayout.Input N) : GroupedBuild N :=
  let b := groupedChildLists x.root x.parent.read
  { buckets := b.1
    layout := ofBuckets x.root x.parent.read b.1
      (groupedChildLists_get x.root x.parent.read)
    bucketWork := b.2 }

theorem buildGrouped_buckets (x : PackedStaticLayout.Input N) :
    (buildGrouped x).buckets = bucketChildLists x.root x.parent.read :=
  groupedChildLists_eq_bucketChildLists x.root x.parent.read

theorem mem_buildGrouped_iff (x : PackedStaticLayout.Input N) (q c : Fin N) :
    c ∈ (buildGrouped x).buckets.get q ↔
      c ≠ x.root ∧ x.parent.read c = q :=
  mem_groupedChildLists_iff x.root x.parent.read q c

theorem buildGrouped_bucketWork (x : PackedStaticLayout.Input N) :
    (buildGrouped x).bucketWork = ⟨N, ⟨N, N - 1, N - 1, N - 1, N⟩⟩ :=
  groupedChildLists_work x.root x.parent.read

/-- Exact record order, including child order and local indices. -/
theorem buildGrouped_cells (x : PackedStaticLayout.Input N) :
    (buildGrouped x).layout.cells.toList = (build x).cells.toList := by
  rw [(buildGrouped x).layout.cells_exact, (build x).cells_exact,
    buildGrouped_buckets x]

theorem buildGrouped_directory (x : PackedStaticLayout.Input N) :
    (buildGrouped x).layout.directory.toList = (build x).directory.toList := by
  rw [(buildGrouped x).layout.directory_exact, (build x).directory_exact,
    buildGrouped_buckets x]

end PaperB.DenseQuotientRows
