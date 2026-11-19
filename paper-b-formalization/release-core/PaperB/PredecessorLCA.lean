import PaperB.TopologicalRank

namespace PaperB

open Digraph

def CommonPredDom (g : Digraph) (r v d : Fin g.vertexCount) : Prop :=
  ∀ u, g.HasArc u v → g.InitiallyReachable r u → g.Dominates r d u

variable {g : Digraph} {r v d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}

theorem exists_reachable_arc_predecessor
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    ∃ u, g.HasArc u v ∧ g.InitiallyReachable r u := by
  rcases AvoidPath.eq_or_exists_last_arc hv with he | ⟨u, hpre, huv⟩
  · exact False.elim (hvr he.symm)
  · exact ⟨u, huv, initiallyReachable_of_survivingPath (g := g) hpre⟩

theorem CommonPredDom.ne_vertex
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r)
    (hd : CommonPredDom g r v d) : d ≠ v := by
  obtain ⟨u, huv, hu⟩ := exists_reachable_arc_predecessor hv hvr
  have hlt := progress u v huv
  have hvu : v ≠ u := fun he => (Nat.ne_of_lt hlt) (congrArg rank he.symm)
  intro he
  subst d
  have hback := rank_lt_of_strict_dominator progress hu (hd u huv hu) hvu
  exact (Nat.lt_irrefl _) (Nat.lt_trans hlt hback)

theorem immediateDominator_iff_commonPredDom
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    g.IsImmediateDominator r d v ↔
      CommonPredDom g r v d ∧
        ∀ a, CommonPredDom g r v a → g.Dominates r a d := by
  have recurrence (a : Fin g.vertexCount) (hav : a ≠ v) :
      g.Dominates r a v ↔ CommonPredDom g r v a := by
    unfold CommonPredDom
    exact dominates_iff_reachable_predecessors hvr hav
  constructor
  · rintro ⟨hdv, hd, hdeep⟩
    refine ⟨(recurrence d hdv).mp hd, ?_⟩
    intro a ha
    have hav := ha.ne_vertex progress hv hvr
    exact hdeep a hav ((recurrence a hav).mpr ha)
  · rintro ⟨hd, hdeep⟩
    have hdv := hd.ne_vertex progress hv hvr
    exact ⟨hdv, (recurrence d hdv).mpr hd,
      fun a hav ha => hdeep a ((recurrence a hav).mp ha)⟩

/-- In particular, `spec.immediate hv hvr` gives this criterion for `parent v`. -/
theorem immediateDominator_iff_predecessor_lca
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (spec : ParentSpec g r parent)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    g.IsImmediateDominator r d v ↔
      (∀ u, g.HasArc u v → g.InitiallyReachable r u → Ancestor parent d u) ∧
        ∀ a, (∀ u, g.HasArc u v → g.InitiallyReachable r u →
          Ancestor parent a u) → Ancestor parent a d := by
  have pred_iff (a : Fin g.vertexCount) :
      CommonPredDom g r v a ↔
        ∀ u, g.HasArc u v → g.InitiallyReachable r u → Ancestor parent a u := by
    constructor
    · intro ha u huv hu
      exact (ancestor_iff_dominates progress spec hu).mpr (ha u huv hu)
    · intro ha u huv hu
      exact (ancestor_iff_dominates progress spec hu).mp (ha u huv hu)
  have hi_iff := immediateDominator_iff_commonPredDom (d := d) progress hv hvr
  constructor
  · intro hi
    obtain ⟨hd, hdeep⟩ := hi_iff.mp hi
    have hdr := initiallyReachable_of_dominates hv hi.2.1
    exact ⟨(pred_iff d).mp hd, fun a ha =>
      (ancestor_iff_dominates progress spec hdr).mpr (hdeep a ((pred_iff a).mpr ha))⟩
  · rintro ⟨hd, hdeep⟩
    have hd' := (pred_iff d).mpr hd
    obtain ⟨u, huv, hu⟩ := exists_reachable_arc_predecessor hv hvr
    have hdr := initiallyReachable_of_dominates hu (hd' u huv hu)
    exact hi_iff.mpr ⟨hd', fun a ha =>
      (ancestor_iff_dominates progress spec hdr).mp (hdeep a ((pred_iff a).mp ha))⟩

end PaperB
