import PaperB.ExitPaths

/-! Paper B initial declaration and boundary-case replay. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

#print axioms PaperB.AvoidPath.source_alive
#print axioms PaperB.AvoidPath.target_alive
#print axioms PaperB.AvoidPath.mono
#print axioms PaperB.AvoidPath.trans
#print axioms PaperB.Digraph.survivingPath_source_alive
#print axioms PaperB.Digraph.survivingPath_target_alive
#print axioms PaperB.Digraph.survivingPath_mono
#print axioms PaperB.Digraph.survivingPath_trans
#print axioms PaperB.Digraph.reachableAvoiding_two_diag
#print axioms PaperB.LabelledQuotient.mem_implies_lost
#print axioms PaperB.LabelledQuotient.direct_arc_exitTailMem
#print axioms PaperB.LabelledQuotient.exitTailMem_transfer_of_onwardPath
#print axioms PaperB.LabelledQuotient.suffix_avoids_parent_of_shared
#print axioms PaperB.LabelledQuotient.exitTailMem_transfer_inherited
#print axioms PaperB.LabelledQuotient.split_at_fresh_or_avoid_child
#print axioms PaperB.LabelledQuotient.exitTailMem_converse_split

#print axioms PaperB.LabelledQuotient.exitTailMem_iff_of_paths

namespace PaperB.Controls

private abbrev raw : Digraph :=
  ⟨3, #[[], [0, 0], [1]], rfl⟩

example : raw.arcCount = 3 := rfl

example : raw.ReachableAvoiding .none 0 0 :=
  .refl _ (fun h => h)

example : ¬ raw.ReachableAvoiding (.one 0) 0 0 :=
  fun path => path.source_alive rfl

example : ¬ raw.ReachableAvoiding (.one 0) 1 0 :=
  fun path => path.target_alive rfl

example : raw.ReachableAvoiding (.two 2 2) 1 0 ↔ raw.ReachableAvoiding (.one 2) 1 0 :=
  raw.reachableAvoiding_two_diag 2 1 0

/-- Same quotient endpoints, distinct physical tails at vertex 1. The third tail
occurs on an arc from vertex 2 only. -/
private abbrev exits : LabelledQuotient :=
  ⟨3, 4, 0, #[[⟨1,0⟩, ⟨2,0⟩], [⟨3,0⟩, ⟨3,2⟩], [⟨3,1⟩], []], rfl⟩

private def cut : exits.CutPair := ⟨1, 2, by decide, by decide, by decide⟩

example : exits.ExitTailMem cut 1 3 0 := by
  refine ⟨⟨3,0⟩, ?_, rfl, .refl _ ?_⟩ <;> decide

example : exits.ExitTailMem cut 1 3 2 := by
  refine ⟨⟨3,2⟩, ?_, rfl, .refl _ ?_⟩ <;> decide

example : ¬ exits.ExitTailMem cut 1 3 1 := by
  rintro ⟨e, he, ht, _⟩
  change e ∈ [⟨3,0⟩, ⟨3,2⟩] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h <;> subst e <;> revert ht <;> decide


/-- The original graph of Figure 1, in the order r, U, V, ℓ, h, p, y. -/
private abbrev figure : Digraph :=
  ⟨7, #[[1,2], [3,4], [5], [5], [6], [6], []], rfl⟩

private instance (g : Digraph) (u v : Fin g.vertexCount) : Decidable (g.HasArc u v) :=
  inferInstanceAs (Decidable (v ∈ g.outArcs u))

private instance {n : Nat} (F : FailureSet n) (v : Fin n) : Decidable (F.Mem v) := by
  cases F <;> unfold FailureSet.Mem <;> infer_instance

example : figure.arcCount = 8 := rfl

example : figure.ReachableAvoiding (.two 4 2) 0 6 :=
  .step 0 1 6 (by decide) (by decide)
    (.step 1 3 6 (by decide) (by decide)
      (.step 3 5 6 (by decide) (by decide)
        (.step 5 6 6 (by decide) (by decide) (.refl 6 (by decide)))))

example : figure.ReachableAvoiding (.two 3 2) 0 6 :=
  .step 0 1 6 (by decide) (by decide)
    (.step 1 4 6 (by decide) (by decide)
      (.step 4 6 6 (by decide) (by decide) (.refl 6 (by decide))))

private theorem firstStepOrEqual {V : Type} {edge : V → V → Prop}
    {failed : V → Prop} {u v : V} (path : AvoidPath edge failed u v) :
    u = v ∨ ∃ w, edge u w ∧ ¬ failed w := by
  cases path with
  | refl => exact Or.inl rfl
  | step a b c _ arc rest => exact Or.inr ⟨b, arc, rest.source_alive⟩

example : ¬ figure.ReachableAvoiding (.two 1 2) 0 6 := by
  intro path
  rcases firstStepOrEqual path with same | ⟨w, arc, alive⟩
  · exact (by decide : (0 : Fin 7) ≠ 6) same
  · change w ∈ [1, 2] at arc
    exact alive (by simpa [FailureSet.Mem] using arc)

end PaperB.Controls
