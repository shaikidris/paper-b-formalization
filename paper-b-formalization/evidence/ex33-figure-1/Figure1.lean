import PaperB.Exit

namespace PaperB

/-!
PaperB EX3.3, Figure 1. The labelled quotient is supplied directly.
Quotient IDs: r, U, V, p, y.
Original IDs (used for tail labels): r, U, V, ell, h, p, y.
-/
private abbrev fig1 : LabelledQuotient :=
  ⟨7, 5, 0,
    #[[⟨1, 0⟩, ⟨2, 0⟩], [⟨3, 3⟩, ⟨4, 4⟩], [⟨3, 2⟩], [⟨4, 5⟩], []],
    rfl⟩

private def fig1B : fig1.CutPair :=
  ⟨1, 2, by decide, by decide, by decide⟩

private def fig1P : fig1.CutPair :=
  ⟨1, 3, by decide, by decide, by decide⟩

private theorem fig1_outU_cases
    {e : QuotientArc fig1.origVertexCount fig1.vertexCount}
    (he : e ∈ fig1.outArcs 1) : e = ⟨3, 3⟩ ∨ e = ⟨4, 4⟩ := by
  change e ∈ [⟨3, 3⟩, ⟨4, 4⟩] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h
  · exact Or.inl (by subst e; rfl)
  · exact Or.inr (by subst e; rfl)

private theorem fig1_noArcFromY {w : Fin fig1.vertexCount} :
    ¬ fig1.HasQuotientArc 4 w := by
  rintro ⟨e, he, _⟩
  change e ∈ [] at he
  simp only [List.not_mem_nil] at he

private theorem fig1_end_eq_y
    {failed : Fin fig1.vertexCount → Prop} {u v : Fin fig1.vertexCount}
    (path : fig1.SurvivingPath failed u v) : u = 4 → v = 4 := by
  induction path <;> intro hu
  · exact hu
  · exfalso
    have impossible {a b : Fin fig1.vertexCount}
        (harc : fig1.HasQuotientArc a b) (ha : a = 4) : False := by
      subst a
      exact fig1_noArcFromY harc
    apply impossible
    · assumption
    · first
      | exact hu
      | solve_by_elim

private theorem fig1_pathFromY_iff
    {failed : Fin fig1.vertexCount → Prop} {v : Fin fig1.vertexCount} :
    fig1.SurvivingPath failed 4 v ↔ v = 4 ∧ ¬ failed v := by
  constructor
  · intro path
    exact ⟨fig1_end_eq_y path rfl, path.target_alive⟩
  · rintro ⟨rfl, alive⟩
    exact .refl _ alive

private theorem fig1_pToY_avoidingB : fig1.SurvivingPath fig1B.Mem 3 4 := by
  have facts :
      (⟨4, 5⟩ : QuotientArc fig1.origVertexCount fig1.vertexCount) ∈ fig1.outArcs 3 ∧
        ¬ fig1B.Mem 3 ∧ ¬ fig1B.Mem 4 := by decide
  have arc : fig1.HasQuotientArc 3 4 := ⟨⟨4, 5⟩, facts.1, rfl⟩
  have stayP : fig1.SurvivingPath fig1B.Mem 3 3 := .refl _ facts.2.1
  have stayY : fig1.SurvivingPath fig1B.Mem 4 4 := .refl _ facts.2.2
  constructor <;>
    first
    | exact arc
    | exact stayP
    | exact stayY
    | exact facts.2.1
    | exact facts.2.2

-- X_U^B(p) = {ell}.
example (t : Fin fig1.origVertexCount) :
    fig1.ExitTailMem fig1B 1 3 t ↔ t = 3 := by
  constructor
  · rintro ⟨e, he, ht, path⟩
    rcases fig1_outU_cases he with rfl | rfl
    · first
      | exact ht
      | exact ht.symm
    · have hp :=
        (fig1_pathFromY_iff (failed := fig1B.Mem) (v := 3)).mp path
      exact False.elim ((show (3 : Fin fig1.vertexCount) ≠ 4 by decide) hp.1)
  · rintro rfl
    have facts :
        (⟨3, 3⟩ : QuotientArc fig1.origVertexCount fig1.vertexCount) ∈ fig1.outArcs 1 ∧
          ¬ fig1B.Mem 3 := by decide
    exact ⟨⟨3, 3⟩, facts.1, rfl, .refl _ facts.2⟩

-- X_U^P(y) = {h}.
example (t : Fin fig1.origVertexCount) :
    fig1.ExitTailMem fig1P 1 4 t ↔ t = 4 := by
  constructor
  · rintro ⟨e, he, ht, path⟩
    rcases fig1_outU_cases he with rfl | rfl
    · exact False.elim (path.source_alive (show fig1P.Mem 3 by decide))
    · first
      | exact ht
      | exact ht.symm
  · rintro rfl
    have facts :
        (⟨4, 4⟩ : QuotientArc fig1.origVertexCount fig1.vertexCount) ∈ fig1.outArcs 1 ∧
          ¬ fig1P.Mem 4 := by decide
    exact ⟨⟨4, 4⟩, facts.1, rfl, .refl _ facts.2⟩

-- X_U^B(y) = {ell, h}.
example (t : Fin fig1.origVertexCount) :
    fig1.ExitTailMem fig1B 1 4 t ↔ t = 3 ∨ t = 4 := by
  constructor
  · rintro ⟨e, he, ht, _⟩
    rcases fig1_outU_cases he with rfl | rfl
    · apply Or.inl
      first
      | exact ht
      | exact ht.symm
    · apply Or.inr
      first
      | exact ht
      | exact ht.symm
  · rintro (rfl | rfl)
    · refine ⟨⟨3, 3⟩, ?_, rfl, fig1_pToY_avoidingB⟩
      decide
    · have facts :
          (⟨4, 4⟩ : QuotientArc fig1.origVertexCount fig1.vertexCount) ∈ fig1.outArcs 1 ∧
            ¬ fig1B.Mem 4 := by decide
      exact ⟨⟨4, 4⟩, facts.1, rfl, .refl _ facts.2⟩

private def figForest := LabelledQuotient.buildProperLossForest fig1 (fun v => v.val)

example : figForest.realKeys.map (fun B => (B.fst.val, B.snd.val)) =
    [(1, 2), (1, 3)] := by decide

example : (List.ofFn fun i : Fin (figForest.realNodeCount + 1) =>
    (figForest.parent i).val) = [0, 0, 1] := by decide

example : (List.ofFn fun i : Fin fig1.vertexCount =>
    (figForest.label i).val) = [0, 0, 0, 1, 2] := by decide

example :
    let child : Fin (figForest.realNodeCount + 1) := ⟨2, by decide⟩
    let v : Fin fig1.vertexCount := ⟨4, by decide⟩
    let keys := figForest.realKeys.map (fun B => (B.fst.val, B.snd.val))
    figForest.parent child = ⟨1, by decide⟩ ∧
      figForest.label v = ⟨2, by decide⟩ ∧
      keys[(figForest.parent child).val - 1]? = some (1, 2) ∧
      keys[child.val - 1]? = some (1, 3) := by decide

end PaperB
