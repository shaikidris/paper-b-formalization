import PaperB.StaticOracleTree
import PaperB.RetainedRouteProof
import PaperB.BothReachableRoute

namespace PaperB.EX44.RetainedRouteProof
open PaperB.Digraph

namespace OriginalStaticConnector.Full
open PaperB.EX16Assembly

variable {g : Digraph} {r : Fin g.vertexCount} {k B E : Nat}
variable {rank : Fin g.vertexCount → Nat}

def world (q : OriginalReader g r) : World g q.count :=
  World.mk (vertex := q.ids.originals.read)
    (entry := fun x => (q.reader.entry x : Nat))
    (fun x => (q.reader.stop x : Nat) - 1)

/-- Install the original-tree callbacks with a common bounded debit.
The pair-key, pair-member, and exit-extrema callbacks are inherited from `base`. -/
def install (q : OriginalReader g r) (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    Runtime g.vertexCount q.count k B E :=
  { base with
    source := q.slot r hr
    translate := fun i => ⟨q.ids.find i, debit, hdebit⟩
    ancestor := fun a x => ⟨q.reader.isAncestor a x, debit, hdebit⟩
    lca := fun a b => ⟨(q.reader.lca a b).node, debit, hdebit⟩
    childBelow := fun d x => ⟨q.reader.child d x, debit, hdebit⟩ }

theorem source_vertex (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    (world q).vertex (install q hr base debit hdebit).source = r :=
  q.original_at_slot r hr

theorem vertexInj (q : OriginalReader g r) :
    Function.Injective (world q).vertex := by
  intro a b hab
  apply Option.some.inj
  exact (q.ids.slot_of_original a).symm.trans
    ((congrArg q.ids.find hab).trans (q.ids.slot_of_original b))

theorem normalizedIDs (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    NormalizedIDs (install q hr base debit hdebit) (world q) := by
  constructor
  · intro i x
    exact q.find_eq_some_iff_original i x
  · intro i
    change q.ids.find i = none ↔
      ¬ g.InitiallyReachable
        ((world q).vertex (install q hr base debit hdebit).source) i
    rw [source_vertex q hr base debit hdebit]
    exact q.ids.miss_iff i

private theorem inside_interval (q : OriginalReader g r) (a x : Fin q.count) :
    (world q).Inside a x ↔
      q.reader.entry a ≤ q.reader.entry x ∧
      q.reader.entry x < q.reader.stop a := by
  change (q.reader.entry a ≤ q.reader.entry x ∧
    q.reader.entry x ≤ q.reader.stop a - 1) ↔ _
  have hself := (q.reader.ancestor_iff_interval a a).mp (by
    first
    | exact ⟨0, rfl⟩
    | rfl
    | exact?)
  have hstop : 0 < q.reader.stop a := by omega
  constructor <;> intro h
  · have hx := h.2
    exact ⟨h.1, by omega⟩
  · have hx := h.2
    exact ⟨h.1, by omega⟩

theorem ancestor_exact (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) (a x : Fin q.count) :
    ((install q hr base debit hdebit).fetch (.ancestor a x)).value = true ↔
      (world q).Inside a x :=
  (q.reader.isAncestor_exact a x).trans
    ((q.reader.ancestor_iff_interval a x).trans (inside_interval q a x).symm)

theorem intervals (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    Contracts (install q hr base debit hdebit) (world q) := by
  first
  | exact ⟨ancestor_exact q hr base debit hdebit⟩
  | exact ancestor_exact q hr base debit hdebit
  | constructor
    intro a x
    exact (ancestor_exact q hr base debit hdebit a x).symm

private theorem held_dominance (q : OriginalReader g r) (a x : Fin q.count) :
    g.Dominates r ((world q).vertex a) ((world q).vertex x) ↔
      (world q).Inside a x :=
  (q.held_dominates_iff_interval a x).trans (inside_interval q a x).symm

theorem dominance (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) (a x : Fin q.count) :
    g.Dominates ((world q).vertex (install q hr base debit hdebit).source)
      ((world q).vertex a) ((world q).vertex x) ↔
      (world q).Inside a x := by
  rw [source_vertex q hr base debit hdebit]
  exact held_dominance q a x

private abbrev Progress (g : Digraph) (rank : Fin g.vertexCount → Nat) :=
  ∀ i j, g.HasArc i j → rank i < rank j

private abbrev RankInjective (g : Digraph) (rank : Fin g.vertexCount → Nat) :=
  ∀ ⦃i j⦄, rank i = rank j → i = j

private theorem original_tree (q : OriginalReader g r)
    (progress : Progress g rank) (injRank : RankInjective g rank)
    (a x : Fin g.vertexCount)
    (ha : g.InitiallyReachable r a) (hx : g.InitiallyReachable r x) :
    Ancestor q.parent a x ↔ g.Dominates r a x := by
  have spec : ParentSpec g r q.parent := q.parentSpec
  first
  | exact?
  | symm
    exact?
  | constructor <;> intro h <;> exact?

theorem treeInterval (q : OriginalReader g r)
    (progress : Progress g rank) (injRank : RankInjective g rank)
    (a x : Fin q.count) :
    (world q).Inside a x ↔
      Ancestor q.parent ((world q).vertex a) ((world q).vertex x) :=
  (held_dominance q a x).symm.trans
    (original_tree q progress injRank _ _
      (q.ids.original_reachable a) (q.ids.original_reachable x)).symm

private theorem dominates_antisymmetric
    (progress : Progress g rank)
    {s a b : Fin g.vertexCount}
    (ha : g.InitiallyReachable s a) (hb : g.InitiallyReachable s b)
    (hab : g.Dominates s a b) (hba : g.Dominates s b a) : a = b := by
  by_cases h : a = b
  · exact h
  · have h₁ := rank_lt_of_strict_dominator progress hb hab h
    have h₂ := rank_lt_of_strict_dominator progress ha hba (Ne.symm h)
    omega

private theorem held_self (q : OriginalReader g r) (x : Fin q.count) :
    g.Dominates r ((world q).vertex x) ((world q).vertex x) :=
  (q.held_dominates_iff_interval x x).mpr
    ((q.reader.ancestor_iff_interval x x).mp (by
      first
      | exact ⟨0, rfl⟩
      | rfl
      | exact?))

/-- Lift the static LCA law from stored slots to all original vertices. -/
theorem lca_common (q : OriginalReader g r) (a b : Fin q.count)
    (c : Fin g.vertexCount) :
    (g.Dominates r c ((world q).vertex a) ∧
      g.Dominates r c ((world q).vertex b)) ↔
    g.Dominates r c ((world q).vertex (q.reader.lca a b).node) := by
  by_cases hc : g.InitiallyReachable r c
  · rw [← q.original_at_slot c hc]
    let z := q.slot c hc
    let d := (q.reader.lca a b).node
    change (g.Dominates r ((world q).vertex z) ((world q).vertex a) ∧
      g.Dominates r ((world q).vertex z) ((world q).vertex b)) ↔
      g.Dominates r ((world q).vertex z) ((world q).vertex d)
    exact
      (and_congr
        ((q.held_dominates_iff_interval z a).trans
          (q.reader.ancestor_iff_interval z a).symm)
        ((q.held_dominates_iff_interval z b).trans
          (q.reader.ancestor_iff_interval z b).symm)).trans
        ((q.reader.lca_exact a b z).trans
          ((q.reader.ancestor_iff_interval z d).trans
            (q.held_dominates_iff_interval z d).symm))
  · constructor
    · intro h
      exact (hc (initiallyReachable_of_dominates (q.ids.original_reachable a) h.1)).elim
    · intro h
      exact (hc (initiallyReachable_of_dominates (q.ids.original_reachable (q.reader.lca a b).node) h)).elim

theorem lca_exact (q : OriginalReader g r)
    (progress : Progress g rank) (injRank : RankInjective g rank)
    (a b d : Fin q.count) :
    (q.reader.lca a b).node = d ↔
    ∀ c : Fin g.vertexCount,
      (g.Dominates r c ((world q).vertex a) ∧
        g.Dominates r c ((world q).vertex b)) ↔
      g.Dominates r c ((world q).vertex d) := by
  constructor
  · rintro rfl
    exact lca_common q a b
  · intro h
    let z := (q.reader.lca a b).node
    have hdz : g.Dominates r ((world q).vertex d) ((world q).vertex z) :=
      (lca_common q a b ((world q).vertex d)).mp
        ((h ((world q).vertex d)).mpr (held_self q d))
    have hzd : g.Dominates r ((world q).vertex z) ((world q).vertex d) :=
      (h ((world q).vertex z)).mp
        ((lca_common q a b ((world q).vertex z)).mpr (held_self q z))
    exact vertexInj q (dominates_antisymmetric progress (q.ids.original_reachable z)
      (q.ids.original_reachable d) hzd hdz)

private theorem static_root_fixed (q : OriginalReader g r) :
    q.input.parent.read q.input.root = q.input.root := by
  have hok := q.reader.input_ok
  first
  | exact hok.1
  | exact hok.root_parent
  | exact hok.root_fixed
  | exact?
  | have hv := q.reader.valid
    have hp : q.reader.tables.parent = fun u => q.input.parent.read u := by
      rw [q.reader.tables_exact, q.reader.layout_exact] <;> rfl
    have hroot : q.reader.tables.root = q.input.root := by
      rw [q.reader.tables_exact, q.reader.layout_exact] <;> rfl
    have hf : q.reader.tables.parent q.reader.tables.root =
        q.reader.tables.root := by
      first
      | exact hv.1
      | exact?
    simpa only [hp, hroot] using hf

private theorem original_fixed_of_reachable (q : OriginalReader g r)
    (v : Fin g.vertexCount) (hv : g.InitiallyReachable r v)
    (hf : q.parent v = v) : v = r := by
  by_cases h : v = r
  · exact h
  have spec : ParentSpec g r q.parent := q.parentSpec
  obtain ⟨_, hoff⟩ := spec
  rcases hoff v h with ⟨_, hi⟩ | ⟨hn, _⟩
  · rw [hf] at hi
    exfalso
    first
    | exact hi.1 rfl
    | exact hi.2.1 rfl
    | exact hi.1.1 rfl
    | exact?
    | change _ ∧ _ at hi
      grind
  · exact (hn hv).elim

private theorem slot_fixed_eq_root (q : OriginalReader g r) (u : Fin q.count)
    (hf : q.input.parent.read u = u) : u = q.input.root := by
  have h (x : Fin q.count) (hx : q.input.parent.read x = x) :
      (world q).vertex x = r :=
    original_fixed_of_reachable q _ (q.ids.original_reachable x)
      ((q.parent_at_original x).trans (congrArg q.ids.originals.read hx))
  exact vertexInj q ((h u hf).trans (h q.input.root (static_root_fixed q)).symm)


end OriginalStaticConnector.Full

end PaperB.EX44.RetainedRouteProof
