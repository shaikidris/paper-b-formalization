import PaperB.SiblingBlocks
import PaperB.DominatorBoundary
import PaperB.BlockProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

/-- Lift a path that stays in `good` to a subtype containing all good
vertices, preserving a test implied by `good`. -/
private theorem avoidPath_lift_subtype {α : Type}
    {arc : α → α → Prop} {good member : α → Prop}
    {test : Subtype member → Prop}
    (hmem : ∀ x : α, good x → member x)
    (htest : ∀ x : Subtype member, good x.val → test x)
    {s t : α} (path : AvoidPath arc (fun x => ¬ good x) s t) :
    ∀ (hs : member s) (ht : member t),
      AvoidPath (fun x y : Subtype member => arc x.val y.val)
        (fun x => ¬ test x) ⟨s, hs⟩ ⟨t, ht⟩ := by
  have good_of_alive (x : α) (hx : ¬ ¬ good x) : good x :=
    Classical.byContradiction hx
  induction path with
  | refl x hx =>
      intro hs ht
      exact AvoidPath.refl (⟨x, hs⟩ : Subtype member)
        (fun h => h (htest ⟨x, hs⟩ (good_of_alive x hx)))
  | step x y z hx hxy tail ih =>
      intro hs ht
      have hy : member y := hmem y (good_of_alive y tail.source_alive)
      exact AvoidPath.step (⟨x, hs⟩ : Subtype member) (⟨y, hy⟩ : Subtype member) (⟨z, ht⟩ : Subtype member)
        (fun h => h (htest ⟨x, hs⟩ (good_of_alive x hx)))
        hxy (ih hy ht)

namespace Digraph

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- A block member can be reached from its leader without leaving the block. -/
theorem siblingBlock_internal (hd : g.InitiallyReachable r d)
    (c : SiblingBlockKey g r d parent) (v : SiblingVertex g r d)
    (hv : siblingBlockOf progress injective spec v = c) :
    AvoidPath (fun x y : SiblingVertex g r d => g.HasArc x.val y.val)
      (fun x => siblingBlockOf progress injective spec x ≠ c)
      (siblingBlockLeader spec hd c) v := by
  by_cases hc : c.val = d
  · have hkey : c = SiblingBlockKey.root g r d parent := Subtype.ext hc
    have hvd : v.val = d :=
      (siblingBlockOf_eq_root_iff progress injective spec v).1 (hv.trans hkey)
    have hleader : siblingBlockLeader spec hd c = v :=
      Subtype.ext (hc.trans hvd.symm)
    rw [hleader]
    exact AvoidPath.refl v (fun h => h hv)
  · have hcv : g.Dominates r c.val v.val :=
      (siblingBlockOf_eq_child_iff progress injective spec v c hc).1 hv
    have hsuffix : g.InitiallyReachable c.val v.val :=
      initiallyReachable_suffix_of_dominates v.property.1 hcv
    have hsub := survivingPath_within_dominator_subtree
      (r := r) (d := c.val) (failed := fun _ => False)
      progress v.property.1 hcv hsuffix
    have hpath : AvoidPath g.HasArc
        (fun z => ¬ (g.InitiallyReachable r z ∧ g.Dominates r c.val z))
        c.val v.val :=
      AvoidPath.mono hsub (fun _ hz => Or.inr hz)
    have hdc : g.Dominates r d c.val :=
      (siblingBlockLeader spec hd c).property.2
    have hmem (z : Fin g.vertexCount)
        (hz : g.InitiallyReachable r z ∧ g.Dominates r c.val z) :
        g.InitiallyReachable r z ∧ g.Dominates r d z := by
      rcases hz with ⟨hReach, hcz⟩
      refine ⟨hReach, ?_⟩
      first
      | exact dominates_trans hdc hcz
      | exact hdc.trans hcz
      | solve_by_elim [dominates_trans]
      | exact?
    exact avoidPath_lift_subtype
      (good := fun z => g.InitiallyReachable r z ∧ g.Dominates r c.val z)
      (member := fun z => g.InitiallyReachable r z ∧ g.Dominates r d z)
      (test := fun z : SiblingVertex g r d =>
        siblingBlockOf progress injective spec z = c)
      hmem
      (fun z hz =>
        (siblingBlockOf_eq_child_iff progress injective spec z c hc).2 hz.2)
      hpath (siblingBlockLeader spec hd c).property v.property

/-- The sibling partition as a block system on the original DAG arcs. -/
noncomputable def siblingBlockSystem (hd : g.InitiallyReachable r d) :
    BlockSystem (SiblingVertex g r d) (SiblingBlockKey g r d parent) where
  block := siblingBlockOf progress injective spec
  leader := siblingBlockLeader spec hd
  leader_block := siblingBlockOf_leader progress injective spec hd
  arc := fun u v => g.HasArc u.val v.val
  internal := siblingBlock_internal progress injective spec hd

/-- Every arc crossing between sibling blocks enters the destination leader. -/
theorem siblingBlockSystem_enter (hd : g.InitiallyReachable r d)
    (u v : SiblingVertex g r d)
    (harc : (siblingBlockSystem progress injective spec hd).arc u v)
    (hne : (siblingBlockSystem progress injective spec hd).block u ≠
      (siblingBlockSystem progress injective spec hd).block v) :
    v = (siblingBlockSystem progress injective spec hd).leader
      ((siblingBlockSystem progress injective spec hd).block v) := by
  let c : SiblingBlockKey g r d parent :=
    siblingBlockOf progress injective spec v
  have hv : siblingBlockOf progress injective spec v = c := rfl
  change g.HasArc u.val v.val at harc
  change siblingBlockOf progress injective spec u ≠ c at hne
  change v = siblingBlockLeader spec hd c
  apply Subtype.ext
  change v.val = c.val
  by_cases hc : c.val = d
  · have hkey : c = SiblingBlockKey.root g r d parent := Subtype.ext hc
    have hvd : v.val = d :=
      (siblingBlockOf_eq_root_iff progress injective spec v).1 (hv.trans hkey)
    exact hvd.trans hc.symm
  · have hcv : g.Dominates r c.val v.val :=
      (siblingBlockOf_eq_child_iff progress injective spec v c hc).1 hv
    have hcu : ¬ g.Dominates r c.val u.val := by
      intro hu
      exact hne ((siblingBlockOf_eq_child_iff progress injective spec u c hc).2 hu)
    exact eq_dominator_of_entering_subtree
      harc u.property.1 v.property.1 hcv hcu

/-- Avoiding the failed leaders in the original DAG is equivalent to
avoiding the failed keys in the quotient. -/
theorem siblingBlockSystem_leader_path_iff (hd : g.InitiallyReachable r d)
    {failed : SiblingBlockKey g r d parent → Prop}
    {s t : SiblingBlockKey g r d parent} :
    let S := siblingBlockSystem progress injective spec hd
    AvoidPath S.arc (S.LeaderFailed failed) (S.leader s) (S.leader t) ↔
      AvoidPath S.QuotientEdge failed s t :=
  (siblingBlockSystem progress injective spec hd).leader_path_iff
    (siblingBlockSystem_enter progress injective spec hd)

end Digraph
end PaperB
