import PaperB.CompactPaths
import PaperB.CompactFailures
import PaperB.CompactCounts
import PaperB.Kahn
import PaperB.ReachScan

namespace PaperB.Normalization

open Digraph CompactGraph

/-- The index and the materialized adjacency array used by subsequent queries. -/
structure Retained (g : Digraph) (root : Fin g.vertexCount) where
  marks : Array Bool
  idx : Index g marks
  adj : Array (List (Vertex idx))
  adj_size : adj.size = idx.tables.inverse.size
  adj_eq : adj = (build idx).adj
  mark_iff : ∀ u : Fin g.vertexCount,
    IsMarked idx u ↔ g.InitiallyReachable root u

def Retained.graph {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) : Digraph where
  vertexCount := N.idx.tables.inverse.size
  adj := N.adj
  adj_size := N.adj_size

theorem Retained.graph_eq_build {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) : N.graph = build N.idx := by
  cases N with
  | mk marks idx adj hsize heq hmark =>
    subst adj
    rfl

theorem Retained.outgoingClosed {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) : OutgoingClosed N.idx := by
  intro u v hu huv
  exact (N.mark_iff v).mpr
    (initiallyReachable_extend (g := g) (r := root) ((N.mark_iff u).mp hu) huv)

def reachScan (g : Digraph) (root : Fin g.vertexCount) (acyclic : IsAcyclic g) :=
  g.scanReachability root (Kahn.run g).order.toList
    (Kahn.run_isTopologicalList g acyclic)

private theorem isMarked_iff_get {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (u : Fin g.vertexCount) :
    IsMarked idx u ↔ (marks[u.val]?).getD false = true := by
  have hu : u.val < marks.size := by
    rw [idx.size_eq]
    exact u.isLt
  change CompactIds.marked marks (⟨u.val, hu⟩ : Fin marks.size) = true ↔ _
  simp [CompactIds.marked, getElem?_pos, hu]

def normalize (g : Digraph) (root : Fin g.vertexCount)
    (acyclic : IsAcyclic g) : Retained g root :=
  let scan := reachScan g root acyclic
  let idx := Index.ofMarks g scan.marked
    (g.scanReachability_size root (Kahn.run g).order.toList
      (Kahn.run_isTopologicalList g acyclic))
  let compact := build idx
  { marks := scan.marked
    idx := idx
    adj := compact.adj
    adj_size := compact.adj_size
    adj_eq := rfl
    mark_iff := fun u =>
      (isMarked_iff_get idx u).trans
        (g.scanReachability_iff root (Kahn.run g).order.toList
          (Kahn.run_isTopologicalList g acyclic) u) }

abbrev Query {g : Digraph} {root : Fin g.vertexCount} (N : Retained g root) :=
  Option (Vertex N.idx × Vertex N.idx × FailureSet N.graph.vertexCount)

/-- `none` is an immediate unreachable result. `some` carries a query for the
retained graph, not a claim that a path exists. -/
def lower {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) (F : FailureSet g.vertexCount)
    (source target : Fin g.vertexCount) : Query N :=
  match encode N.idx source with
  | none => none
  | some u =>
    match encode N.idx target with
    | none => none
    | some v => some (u, v, restrictFailures N.idx F)

def PairedPath {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) : Query N → Prop
  | none => False
  | some (u, v, F) => N.graph.SurvivingPath F.Mem u v

theorem lower_eq_none_of_unencoded {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) (F : FailureSet g.vertexCount)
    (s t : Fin g.vertexCount)
    (h : encode N.idx s = none ∨ encode N.idx t = none) :
    lower N F s t = none := by
  rcases h with hs | ht
  · simp [lower, hs]
  · cases hs : encode N.idx s <;> simp [lower, hs, ht]

theorem pairedPath_false_of_unencoded {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) (F : FailureSet g.vertexCount)
    (s t : Fin g.vertexCount)
    (h : encode N.idx s = none ∨ encode N.idx t = none) :
    ¬PairedPath N (lower N F s t) := by
  simp [lower_eq_none_of_unencoded N F s t h, PairedPath]

theorem restrict_repeated_failure {g : Digraph} {marks : Array Bool}
    (idx : Index g marks) (a : Fin g.vertexCount) :
    restrictFailures idx (.two a a) =
      match encode idx a with
      | none => .none
      | some k => .two k k := by
  cases h : encode idx a <;> simp [restrictFailures, h]

private theorem avoidPath_weaken {α : Type} {arc : α → α → Prop}
    {P Q : α → Prop} (h : ∀ x, P x → Q x) {a b : α}
    (p : AvoidPath arc Q a b) : AvoidPath arc P a b := by
  induction p with
  | refl u alive =>
    exact AvoidPath.refl u (fun hu => alive (h u hu))
  | step u v w alive huv _ ih =>
    exact AvoidPath.step u v w (fun hu => alive (h u hu)) huv ih

private theorem reachable_along_survivingPath {g : Digraph}
    {root s t : Fin g.vertexCount} {failed : Fin g.vertexCount → Prop}
    (p : g.SurvivingPath failed s t) :
    g.InitiallyReachable root s → g.InitiallyReachable root t := by
  change AvoidPath g.HasArc failed s t at p
  induction p with
  | refl u _ =>
    exact fun hu => hu
  | step u v w _ huv _ ih =>
    exact fun hu => ih (initiallyReachable_extend (g := g) (r := root) hu huv)

private theorem retained_path_iff_build {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) (failed : Vertex N.idx → Prop) (u v : Vertex N.idx) :
    N.graph.SurvivingPath failed u v ↔
      (build N.idx).SurvivingPath failed u v := by
  cases N with
  | mk marks idx adj hsize heq hmark =>
    subst adj
    rfl

private theorem encoded_paired_iff {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) (F : FailureSet g.vertexCount)
    (s t : Fin g.vertexCount) (u v : Vertex N.idx)
    (hs : encode N.idx s = some u) (ht : encode N.idx t = some v) :
    PairedPath N (some (u, v, restrictFailures N.idx F)) ↔
      g.SurvivingPath F.Mem s t := by
  have hf (k : Vertex N.idx) :
      (restrictFailures N.idx F).Mem k ↔ F.Mem (decode N.idx k) :=
    mem_restrictFailures_iff N.idx F k
  have hpath :
      (build N.idx).SurvivingPath (restrictFailures N.idx F).Mem u v ↔
        (build N.idx).SurvivingPath (fun k => F.Mem (decode N.idx k)) u v := by
    change AvoidPath (build N.idx).HasArc (restrictFailures N.idx F).Mem u v ↔
      AvoidPath (build N.idx).HasArc (fun k => F.Mem (decode N.idx k)) u v
    exact ⟨fun p => avoidPath_weaken (fun k => (hf k).mpr) p,
      fun p => avoidPath_weaken (fun k => (hf k).mp) p⟩
  calc
    PairedPath N (some (u, v, restrictFailures N.idx F)) ↔
        (build N.idx).SurvivingPath (restrictFailures N.idx F).Mem u v :=
      retained_path_iff_build N (restrictFailures N.idx F).Mem u v
    _ ↔ (build N.idx).SurvivingPath (fun k => F.Mem (decode N.idx k)) u v := hpath
    _ ↔ g.SurvivingPath F.Mem (decode N.idx u) (decode N.idx v) :=
      survivingPath_iff g N.marks N.idx root N.mark_iff F.Mem u v
    _ ↔ g.SurvivingPath F.Mem s t := by
      rw [decode_encode N.idx s u hs, decode_encode N.idx t v ht]

/-- A query can start at any retained vertex. For an arbitrary original
source, the guard excludes paths that start outside the retained graph. -/
theorem survivingPath_iff_paired_guarded {g : Digraph} {root : Fin g.vertexCount}
    (N : Retained g root) (F : FailureSet g.vertexCount) (s t : Fin g.vertexCount) :
    (g.InitiallyReachable root s ∧ g.SurvivingPath F.Mem s t) ↔
      PairedPath N (lower N F s t) := by
  have henc (a : Fin g.vertexCount) :
      (∃ k : Vertex N.idx, encode N.idx a = some k) ↔ g.InitiallyReachable root a :=
    (encode_exists_iff_marked N.idx a).trans (N.mark_iff a)
  have absent (a : Fin g.vertexCount) (ha : encode N.idx a = none) :
      ¬g.InitiallyReachable root a := by
    intro hr
    obtain ⟨k, hk⟩ := (henc a).mpr hr
    rw [ha] at hk
    cases hk
  cases hs : encode N.idx s with
  | none =>
    rw [lower_eq_none_of_unencoded N F s t (Or.inl hs)]
    change _ ↔ False
    exact ⟨fun h => absent s hs h.1, False.elim⟩
  | some u =>
    have hsource := (henc s).mp ⟨u, hs⟩
    cases ht : encode N.idx t with
    | none =>
      rw [lower_eq_none_of_unencoded N F s t (Or.inr ht)]
      change _ ↔ False
      exact ⟨fun h => absent t ht (reachable_along_survivingPath h.2 h.1),
        False.elim⟩
    | some v =>
      simpa only [lower, hs, ht, hsource, true_and] using
        (encoded_paired_iff N F s t u v hs ht).symm

private theorem initiallyReachable_self (g : Digraph) (r : Fin g.vertexCount) :
    g.InitiallyReachable r r := by
  first
  | exact AvoidPath.refl r (fun h : False => h)
  | exact .refl r
  | exact .refl
  | exact initiallyReachable_refl (g := g) (r := r)
  | exact initiallyReachable_refl g r
  | exact?

theorem normalized_survivingPath_iff (g : Digraph) (source target : Fin g.vertexCount)
    (acyclic : IsAcyclic g) (F : FailureSet g.vertexCount) :
    g.SurvivingPath F.Mem source target ↔
      PairedPath (normalize g source acyclic)
        (lower (normalize g source acyclic) F source target) := by
  simpa only [initiallyReachable_self g source, true_and] using
    (survivingPath_iff_paired_guarded (normalize g source acyclic) F source target)

section Counts

open CompactCounts

private theorem mem_enum {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    f i ∈ List.ofFn f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases (motive := fun j => f j ∈ List.ofFn f) ?_ ?_ i
    · rw [List.ofFn_succ]
      simp
    · intro j
      rw [List.ofFn_succ]
      exact List.mem_cons_of_mem _ (ih (fun k : Fin n => f k.succ) j)

private theorem enum_witness {α : Type} {n : Nat} (f : Fin n → α) {a : α}
    (ha : a ∈ List.ofFn f) : ∃ i, f i = a := by
  induction n with
  | zero => simp at ha
  | succ n ih =>
    rw [List.ofFn_succ] at ha
    rcases List.mem_cons.mp ha with h | h
    · exact ⟨0, h.symm⟩
    · obtain ⟨i, hi⟩ := ih (fun j : Fin n => f j.succ) h
      exact ⟨i.succ, hi⟩

private theorem enum_nodup {α : Type} {n : Nat} (f : Fin n → α)
    (hf : ∀ {i j}, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    refine ⟨?_, ih (fun i : Fin n => f i.succ) ?_⟩
    · intro h
      obtain ⟨i, hi⟩ := enum_witness (fun j : Fin n => f j.succ) h
      have he : i.succ = (0 : Fin (n + 1)) := hf hi
      have hv : i.val + 1 = 0 := congrArg Fin.val he
      omega
    · intro i j h
      have he : i.succ = j.succ := hf h
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val he))

private theorem pull_front {α : Type} (a : α) {ys : List α} (h : a ∈ ys) :
    ∃ zs, ys.Perm (a :: zs) := by
  induction ys with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst b
      exact ⟨bs, List.Perm.refl _⟩
    · obtain ⟨zs, hp⟩ := ih ht
      refine ⟨b :: zs, (List.Perm.cons b hp).trans ?_⟩
      apply List.Perm.swap

private theorem perm_nodup_mem {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hm : ∀ a, a ∈ xs ↔ a ∈ ys) :
    xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons a ts =>
      have h : a ∈ ([] : List α) := (hm a).mpr (by simp)
      simp at h
  | cons a ts ih =>
    obtain ⟨zs, hp⟩ := pull_front a ((hm a).mp (by simp))
    have hz : (a :: zs).Nodup := by
      first
      | exact hp.nodup_iff.mp hy
      | exact hp.nodup hy
    have ht := List.nodup_cons.mp hx
    have hzs := List.nodup_cons.mp hz
    have hmem : ∀ b, b ∈ ts ↔ b ∈ zs := by
      intro b
      by_cases e : b = a
      · subst b
        simp [ht.1, hzs.1]
      · have hb : b ∈ a :: ts ↔ b ∈ a :: zs := (hm b).trans hp.mem_iff
        simpa only [List.mem_cons, e, false_or] using hb
    exact (List.Perm.cons a (ih ht.2 hzs.2 hmem)).trans hp.symm

private theorem sum_map_perm {α : Type} (w : α → Nat) {xs ys : List α}
    (h : xs.Perm ys) : (xs.map w).sum = (ys.map w).sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b ts => simp [Nat.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem map_enum {α β : Type} {n : Nat} (f : Fin n → α) (w : α → β) :
    (List.ofFn f).map w = List.ofFn (fun i => w (f i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ, ih]

private theorem rows_toList (g : Digraph) :
    List.ofFn g.outArcs = g.adj.toList := by
  have h : (Array.ofFn g.outArcs).toList = g.adj.toList := by
    apply List.ext_getElem
    · simp [g.adj_size]
    · intro i hi hj
      simp [Digraph.outArcs]
  simpa only [Array.toList_ofFn] using h

private theorem foldl_sum_map {α : Type} (w : α → Nat) (xs : List α) (a : Nat) :
    xs.foldl (fun s x => s + w x) a = a + (xs.map w).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x ts ih => simp [List.foldl, ih, Nat.add_assoc]

private theorem sum_full_rows (g : Digraph) :
    ((fullVertices g).map (fun u => (g.outArcs u).length)).sum = g.arcCount := by
  calc
    _ = (((fullVertices g).map g.outArcs).map List.length).sum := by
      simp only [List.map_map, Function.comp_def]
    _ = g.arcCount := by
      change (((List.ofFn (id : Fin g.vertexCount → Fin g.vertexCount)).map
        g.outArcs).map List.length).sum = g.arcCount
      rw [map_enum]
      change ((List.ofFn g.outArcs).map List.length).sum = g.arcCount
      rw [rows_toList]
      unfold Digraph.arcCount
      generalize g.adj.toList = rows
      first
      | change (rows.map List.length).sum =
          rows.foldl (fun s row => s + row.length) 0
        simpa only [Nat.zero_add] using (foldl_sum_map List.length rows 0).symm
      | induction rows with
        | nil => rfl
        | cons row rows ih =>
          rw [List.map_cons, List.sum_cons, ih] <;>
            first | rfl | exact Nat.add_comm _ _

private theorem supplied_eq_sum (g : Digraph) (xs : List (Fin g.vertexCount)) :
    g.suppliedAdjacencyLength xs =
      (xs.map (fun u => (g.outArcs u).length)).sum := by
  first
  | rfl
  | simpa only [Digraph.suppliedAdjacencyLength, Nat.zero_add] using
      (foldl_sum_map (fun u => (g.outArcs u).length) xs 0)
  | induction xs with
    | nil => rfl
    | cons u us ih =>
      simp [Digraph.suppliedAdjacencyLength, foldl_sum_map, ih,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem kahn_order_counts (g : Digraph) (acyclic : IsAcyclic g) :
    (Kahn.run g).order.toList.length = g.vertexCount ∧
      g.suppliedAdjacencyLength (Kahn.run g).order.toList = g.arcCount := by
  have htop := Kahn.run_isTopologicalList g acyclic
  have hfull : (fullVertices g).Nodup :=
    enum_nodup (id : Fin g.vertexCount → Fin g.vertexCount) (fun h => h)
  have hp : (Kahn.run g).order.toList.Perm (fullVertices g) :=
    perm_nodup_mem htop.1 hfull (fun u =>
      ⟨fun _ => mem_enum id u, fun _ => htop.2.1 u⟩)
  constructor
  · simpa [fullVertices] using hp.length_eq
  · rw [supplied_eq_sum]
    exact (sum_map_perm (fun u => (g.outArcs u).length) hp).trans (sum_full_rows g)

/-- Counts the concrete Kahn order and its row occurrences, the reach scan,
and the compaction passes. These are traversal counts, not a bound on every
operation performed inside Kahn's algorithm. -/
structure Counts where
  kahnOrderSlots : Nat
  kahnOrderArcOccurrences : Nat
  reachVertexVisits : Nat
  reachAdjacencyOccurrences : Nat
  reachProbes : Nat
  mapVisits : Nat
  inverseSlots : Nat
  compactAdjacencyScans : Nat

def Counts.total (c : Counts) : Nat :=
  c.kahnOrderSlots + c.kahnOrderArcOccurrences + c.reachProbes +
    (c.mapVisits + c.inverseSlots + c.compactAdjacencyScans)

def counts (g : Digraph) (root : Fin g.vertexCount) (acyclic : IsAcyclic g) : Counts :=
  let order := (Kahn.run g).order.toList
  let scan := reachScan g root acyclic
  let N := normalize g root acyclic
  ⟨order.length, g.suppliedAdjacencyLength order, scan.vertexVisits,
    scan.adjacencyOccurrences, scan.probes, N.idx.tables.visits,
    N.idx.tables.inverse.size, adjacencyScans N.idx⟩

structure CountBounds (g : Digraph) (compact : Digraph) (c : Counts) : Prop where
  kahnOrderSlots_eq : c.kahnOrderSlots = g.vertexCount
  kahnOrderArcOccurrences_eq : c.kahnOrderArcOccurrences = g.arcCount
  reachVertexVisits_eq : c.reachVertexVisits = g.vertexCount
  reachAdjacencyOccurrences_le : c.reachAdjacencyOccurrences ≤ g.arcCount
  reachProbes_le : c.reachProbes ≤ g.vertexCount + g.arcCount
  mapVisits_eq : c.mapVisits = g.vertexCount
  inverseSlots_le : c.inverseSlots ≤ g.vertexCount
  compactAdjacencyScans_le : c.compactAdjacencyScans ≤ g.arcCount
  compactTraversal_le :
    c.mapVisits + c.inverseSlots + c.compactAdjacencyScans ≤
      2 * g.vertexCount + g.arcCount
  compactVertexCount_eq : compact.vertexCount = c.inverseSlots
  compactArcCount_eq : compact.arcCount = c.compactAdjacencyScans
  total_le : c.total ≤ 4 * g.vertexCount + 3 * g.arcCount

theorem normalization_counts (g : Digraph) (root : Fin g.vertexCount)
    (acyclic : IsAcyclic g) :
    CountBounds g (normalize g root acyclic).graph (counts g root acyclic) := by
  let order := (Kahn.run g).order.toList
  let top : g.IsTopologicalList order := Kahn.run_isTopologicalList g acyclic
  let scan := reachScan g root acyclic
  let N := normalize g root acyclic
  obtain ⟨hkV, hkA⟩ := kahn_order_counts g acyclic
  have hV : order.length = g.vertexCount := hkV
  have hA : g.suppliedAdjacencyLength order = g.arcCount := hkA
  have hrV : scan.vertexVisits = g.vertexCount :=
    (g.scanReachability_vertexVisits root order top).trans hV
  have hrA : scan.adjacencyOccurrences ≤ g.arcCount := by
    have h : scan.adjacencyOccurrences ≤ g.suppliedAdjacencyLength order :=
      g.scanReachability_adjacencyOccurrences_le root order top
    simpa only [hA] using h
  have hrP : scan.probes ≤ g.vertexCount + g.arcCount := by
    have h : scan.probes ≤ order.length + g.suppliedAdjacencyLength order :=
      g.scanReachability_probes_le root order top
    simpa only [hV, hA] using h
  obtain ⟨hm, hi, ha, hc⟩ := traversal_bounds N.idx
  have hout : N.graph.arcCount = adjacencyScans N.idx :=
    (congrArg Digraph.arcCount N.graph_eq_build).trans
      (arcCount_build_eq_adjacencyScans N.idx N.outgoingClosed)
  refine ⟨hV, hA, hrV, hrA, hrP, hm, hi, ha, hc, rfl, hout, ?_⟩
  change order.length + g.suppliedAdjacencyLength order + scan.probes +
      (N.idx.tables.visits + N.idx.tables.inverse.size + adjacencyScans N.idx) ≤
    4 * g.vertexCount + 3 * g.arcCount
  omega

end Counts

end PaperB.Normalization
