import PaperB.Spec

/-! Exit-transfer steps on a supplied labelled graph, with the required surviving paths explicit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace LabelledQuotient

/-- Generic fresh-endpoint exit transfer (core composition step in Theorem 4.1):
    if original physical tail `x` witnesses an exit from `s` to an intermediate
    endpoint `p` in `H - B`, and `p` has an actual surviving path onwards to `y`
    avoiding the parent pair `B`, then the same tail `x` witnesses `x ∈ X^B_s(y)`. -/
theorem exitTailMem_transfer_of_onwardPath
    {H : LabelledQuotient} {B : CutPair H}
    {s p y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hExitToFresh : H.ExitTailMem B s p x)
    (hOnward : H.SurvivingPath B.Mem p y) :
    H.ExitTailMem B s y x := by
  let ⟨e, he, hTail, hToFresh⟩ := hExitToFresh
  exact ⟨e, he, hTail, AvoidPath.trans hToFresh hOnward⟩

/-- Inherited-continuation lemma (Theorem 4.1, shared-endpoint case):
    when `s ∈ P`, `y` is lost under `P`, and every vertex in `B \ {s}` remains
    reachable from `H.root` in `H - P`, any continuation in `H - P` to `y`
    also avoids all of `B`. -/
theorem suffix_avoids_parent_of_shared
    {H : LabelledQuotient} {B P : CutPair H}
    {s w y : Fin H.vertexCount}
    (hsP : P.Mem s)
    (hLostP : H.Lost P y)
    (hReachOther : ∀ v : Fin H.vertexCount, B.Mem v → v ≠ s →
      H.SurvivingPath P.Mem H.root v)
    (hCont : H.SurvivingPath P.Mem w y) :
    H.SurvivingPath B.Mem w y := by
  revert hLostP
  induction hCont with
  | refl z aliveP =>
      intro hLostP
      refine AvoidPath.refl z (fun hzB => ?_)
      have hz_ne_s : z ≠ s := fun hEq => aliveP (by rw [hEq]; exact hsP)
      exact hLostP (hReachOther z hzB hz_ne_s)
  | step z next tgt aliveP arc rest ih =>
      intro hLostP
      refine AvoidPath.step z next tgt (fun hzB => ?_) arc (ih hLostP)
      have hz_ne_s : z ≠ s := fun hEq => aliveP (by rw [hEq]; exact hsP)
      have hPref : H.SurvivingPath P.Mem H.root z := hReachOther z hzB hz_ne_s
      exact hLostP (AvoidPath.trans hPref (AvoidPath.step z next tgt aliveP arc rest))

/-- Inherited exit-tail inclusion `X^P_s(y) ⊆ X^B_s(y)` when `s ∈ B ∩ P`. -/
theorem exitTailMem_transfer_inherited
    {H : LabelledQuotient} {B P : CutPair H}
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hsP : P.Mem s)
    (hLostP : H.Lost P y)
    (hReachOther : ∀ v : Fin H.vertexCount, B.Mem v → v ≠ s →
      H.SurvivingPath P.Mem H.root v)
    (hExitChild : H.ExitTailMem P s y x) :
    H.ExitTailMem B s y x := by
  let ⟨e, he, hTail, hCont⟩ := hExitChild
  exact ⟨e, he, hTail, suffix_avoids_parent_of_shared hsP hLostP hReachOther hCont⟩

/-- Converse path-splitting lemma for Theorem 4.1:
    any path in `H - B` to `y ∉ P` either visits a fresh endpoint `p ∈ P \ B`
    along a prefix in `H - B`, or avoids `P` altogether. -/
theorem split_at_fresh_or_avoid_child
    {H : LabelledQuotient} {B P : CutPair H}
    {w y : Fin H.vertexCount}
    (hPath : H.SurvivingPath B.Mem w y)
    (hyNotP : ¬ P.Mem y) :
    (∃ p : Fin H.vertexCount, IsFreshEndpoint B P p ∧ H.SurvivingPath B.Mem w p) ∨
      H.SurvivingPath P.Mem w y := by
  revert hyNotP
  induction hPath with
  | refl z _ =>
      intro hzNotP
      exact Or.inr (AvoidPath.refl z hzNotP)
  | step z next tgt aliveB arc _ ih =>
      intro hTgtNotP
      if hzP : P.Mem z then
        exact Or.inl ⟨z, ⟨hzP, aliveB⟩, AvoidPath.refl z aliveB⟩
      else
        cases ih hTgtNotP with
        | inl hFresh =>
            let ⟨p, hpFresh, hToP⟩ := hFresh
            exact Or.inl ⟨p, hpFresh, AvoidPath.step z next p aliveB arc hToP⟩
        | inr hAvoidP =>
            exact Or.inr (AvoidPath.step z next tgt hzP arc hAvoidP)

/-- Converse exit-tail decomposition for Theorem 4.1:
    when `y ∈ J(P)` and `s ∉ P → H.root` reaches `s` in `H - P`, every physical
    tail in `X^B_s(y)` comes either from `X^B_s(p)` for some `p ∈ P \ B` or from
    `X^P_s(y)` with `s ∈ P`. -/
theorem exitTailMem_converse_split
    {H : LabelledQuotient} {B P : CutPair H}
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hProperP : H.ProperLoss P y)
    (hReachDisjoint : ¬ P.Mem s → H.SurvivingPath P.Mem H.root s)
    (hExitParent : H.ExitTailMem B s y x) :
    (∃ p : Fin H.vertexCount, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  let ⟨hLostP, hyNotP⟩ := hProperP
  let ⟨e, he, hTail, hContB⟩ := hExitParent
  cases split_at_fresh_or_avoid_child hContB hyNotP with
  | inl hFresh =>
      let ⟨p, hpFresh, hToP⟩ := hFresh
      exact Or.inl ⟨p, hpFresh, ⟨e, he, hTail, hToP⟩⟩
  | inr hAvoidP =>
      if hsP : P.Mem s then
        exact Or.inr ⟨hsP, ⟨e, he, hTail, hAvoidP⟩⟩
      else
        have hRootToS : H.SurvivingPath P.Mem H.root s := hReachDisjoint hsP
        have hArc : H.HasQuotientArc s e.head := ⟨e, he, rfl⟩
        have hSToY : H.SurvivingPath P.Mem s y :=
          AvoidPath.step s e.head y hsP hArc hAvoidP
        exact False.elim (hLostP (AvoidPath.trans hRootToS hSToY))


/-- Pointwise exit-set transfer under explicit path and cut-intersection facts.
The quotient and forest construction must supply these facts for a real forest edge. -/
theorem exitTailMem_iff_of_paths
    {H : LabelledQuotient} {B P : CutPair H}
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (hProper : H.ProperLoss P y)
    (onward : ∀ p, IsFreshEndpoint B P p → H.SurvivingPath B.Mem p y)
    (oldSurvives : ∀ v, B.Mem v → ¬ P.Mem v → H.SurvivingPath P.Mem H.root v)
    (atMostOneShared : ∀ u v, B.Mem u → P.Mem u → B.Mem v → P.Mem v → u = v) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  constructor
  · exact exitTailMem_converse_split hProper (oldSurvives s hs)
  · intro witness
    rcases witness with ⟨p, fresh, exitToP⟩ | ⟨shared, inherited⟩
    · exact exitTailMem_transfer_of_onwardPath exitToP (onward p fresh)
    · refine exitTailMem_transfer_inherited shared hProper.1 ?_ inherited
      intro v hv different
      exact oldSurvives v hv (fun alsoShared => different (atMostOneShared v s hv alsoShared hs shared))

end LabelledQuotient

end PaperB
