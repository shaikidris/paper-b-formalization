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

/-- An endpoint of the parent outside the child survives both child deletions. -/
theorem oldEndpoint_survives_of_rank
    {H : LabelledQuotient} {B P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (freshLater : ∀ p, IsFreshEndpoint B P p → ∀ b, B.Mem b → rank b < rank p)
    (atMostOneShared : ∀ u v, B.Mem u → P.Mem u → B.Mem v → P.Mem v → u = v)
    {b : Fin H.vertexCount} (hb : B.Mem b) (hbP : ¬ P.Mem b) :
    H.SurvivingPath P.Mem H.root b := by
  have ranksAlong {u v : Fin H.vertexCount} {failed : Fin H.vertexCount → Prop}
      (path : H.SurvivingPath failed u v) : rank u ≤ rank v := by
    induction path with
    | refl _ _ => exact Nat.le_refl _
    | step start next finish _ arc _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (rankArc start next arc)) ih
  have excludeLater {deleted later u v : Fin H.vertexCount}
      (path : H.SurvivingPath (fun z => z = deleted) u v)
      (hLater : rank v < rank later) :
      H.SurvivingPath (fun z => z = deleted ∨ z = later) u v := by
    induction path with
    | refl node alive =>
      exact .refl node (fun h => h.elim alive (fun hEq => (Nat.ne_of_lt hLater) (congrArg rank hEq)))
    | step start next finish alive arc rest ih =>
      have before := Nat.lt_of_le_of_lt (ranksAlong rest) hLater
      have hStart := Nat.lt_trans (rankArc start next arc) before
      exact .step start next finish
        (fun h => h.elim alive (fun hEq => (Nat.ne_of_lt hStart) (congrArg rank hEq)))
        arc (ih hLater)
  by_cases shared : B.Mem P.fst
  · have fresh : IsFreshEndpoint B P P.snd := by
      refine ⟨Or.inr rfl, fun sharedRight => ?_⟩
      exact P.ne (atMostOneShared P.fst P.snd shared (Or.inl rfl) sharedRight (Or.inr rfl))
    exact excludeLater
      (flat.2 P.fst b P.fst_ne_root (fun h => hbP (Or.inl h))) (freshLater P.snd fresh b hb)
  · have fresh : IsFreshEndpoint B P P.fst := ⟨Or.inl rfl, shared⟩
    have survivor := excludeLater
      (flat.2 P.snd b P.snd_ne_root (fun h => hbP (Or.inr h))) (freshLater P.fst fresh b hb)
    exact AvoidPath.mono survivor (fun _ h => h.elim Or.inr Or.inl)

/-- A new child endpoint has a suffix to every proper child loss, avoiding the parent. -/
theorem freshEndpoint_onward_of_rank
    {H : LabelledQuotient} {B P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {p y : Fin H.vertexCount}
    (fresh : IsFreshEndpoint B P p)
    (freshLater : ∀ b, B.Mem b → rank b < rank p)
    (proper : H.ProperLoss P y) :
    H.SurvivingPath B.Mem p y := by
  have afterParent {u v : Fin H.vertexCount} {failed : Fin H.vertexCount → Prop}
      (path : H.SurvivingPath failed u v) (startsLater : rank p ≤ rank u) :
      H.SurvivingPath B.Mem u v := by
    induction path with
    | refl u _ =>
      exact .refl u (fun hu => Nat.not_lt_of_ge startsLater (freshLater u hu))
    | step u w v _ arc _ rest =>
      have nextLater := Nat.le_trans startsLater (Nat.le_of_lt (rankArc u w arc))
      exact .step u w v (fun hu => Nat.not_lt_of_ge startsLater (freshLater u hu))
        arc (rest nextLater)
  have splitAt {deleted u v : Fin H.vertexCount}
      (path : H.SurvivingPath (fun z => z = deleted) u v) :
      H.SurvivingPath B.Mem p v ∨ H.SurvivingPath (fun z => z = p ∨ z = deleted) u v := by
    induction path with
    | refl u alive =>
      by_cases equal : u = p
      · subst u
        exact Or.inl (.refl p fresh.2)
      · exact Or.inr (.refl u (fun h => h.elim equal alive))
    | step u w v alive arc suffix ih =>
      by_cases equal : u = p
      · subst u
        exact Or.inl (afterParent (.step p w v alive arc suffix) (Nat.le_refl _))
      · exact ih.elim Or.inl (fun rest => Or.inr (.step u w v (fun h => h.elim equal alive) arc rest))
  rcases fresh.1 with left | right
  · subst p
    have path := flat.2 P.snd y P.snd_ne_root (fun h => proper.2 (Or.inr h))
    exact (splitAt path).elim id (fun both => False.elim (proper.1 both))
  · subst p
    have path := flat.2 P.fst y P.fst_ne_root (fun h => proper.2 (Or.inl h))
    exact (splitAt path).elim id (fun both =>
      False.elim (proper.1 (AvoidPath.mono both (fun _ h => h.elim Or.inr Or.inl))))

/-- Exit transfer for two distinct cuts with all fresh child endpoints ordered later. -/
theorem exitTailMem_iff_of_flat_rank
    {H : LabelledQuotient} {B P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (freshLater : ∀ p, IsFreshEndpoint B P p → ∀ b, B.Mem b → rank b < rank p)
    (distinctCuts : ¬ ∀ z, B.Mem z ↔ P.Mem z)
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss P y) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  have exhausts (pair : CutPair H) {u v z : Fin H.vertexCount} (different : u ≠ v)
      (hu : pair.Mem u) (hv : pair.Mem v) :
      pair.Mem z ↔ z = u ∨ z = v := by
    rcases hu with left | right <;> rcases hv with first | second
    · exact False.elim (different (left.trans first.symm))
    · subst u
      subst v
      exact Iff.rfl
    · subst u
      subst v
      exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩
    · exact False.elim (different (right.trans second.symm))
  have atMostOneShared (u v : Fin H.vertexCount)
      (huB : B.Mem u) (huP : P.Mem u) (hvB : B.Mem v) (hvP : P.Mem v) : u = v := by
    by_cases equal : u = v
    · exact equal
    · exact False.elim (distinctCuts (fun _ => (exhausts B equal huB hvB).trans
        (exhausts P equal huP hvP).symm))
  exact exitTailMem_iff_of_paths hs proper
    (fun p fresh => freshEndpoint_onward_of_rank rankArc flat fresh (freshLater p fresh) proper)
    (fun _ hb hbP => oldEndpoint_survives_of_rank rankArc flat freshLater atMostOneShared hb hbP)
    atMostOneShared

/-- In a flat DAG, a proper loss strictly follows both endpoints of the cut. -/
theorem properLoss_follows_endpoints
    {H : LabelledQuotient} {B : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {y b : Fin H.vertexCount} (proper : H.ProperLoss B y) (hb : B.Mem b) :
    rank b < rank y := by
  have ranksAlong {u v : Fin H.vertexCount} {failed : Fin H.vertexCount → Prop}
      (path : H.SurvivingPath failed u v) : rank u ≤ rank v := by
    induction path with
    | refl _ _ => exact Nat.le_refl _
    | step u w _ _ arc _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (rankArc u w arc)) ih
  have beforeOrAvoids {deleted u : Fin H.vertexCount}
      (path : H.SurvivingPath (fun z => z = deleted) u y) :
      rank b < rank y ∨ H.SurvivingPath (fun z => z = b ∨ z = deleted) u y := by
    have notTarget : y ≠ b := fun h => proper.2 (h.symm ▸ hb)
    induction path with
    | refl u alive =>
      exact Or.inr (.refl u (fun h => h.elim notTarget alive))
    | step u v y alive arc rest ih =>
      by_cases equal : u = b
      · subst u
        exact Or.inl (Nat.lt_of_lt_of_le (rankArc b v arc) (ranksAlong rest))
      · exact (ih proper notTarget).elim Or.inl (fun tail => Or.inr (.step u v y (fun h => h.elim equal alive) arc tail))
  rcases hb with first | second
  · subst b
    have path := flat.2 B.snd y B.snd_ne_root (fun h => proper.2 (Or.inr h))
    exact (beforeOrAvoids path).elim id (fun both => False.elim (proper.1 both))
  · subst b
    have path := flat.2 B.fst y B.fst_ne_root (fun h => proper.2 (Or.inl h))
    exact (beforeOrAvoids path).elim id (fun both =>
      False.elim (proper.1 (AvoidPath.mono both (fun _ h => h.elim Or.inr Or.inl))))

/-- Pointwise exit transfer for nested cuts in a flat acyclic quotient. -/
theorem exitTailMem_iff_of_nested_cuts
    {H : LabelledQuotient} {B P : CutPair H}
    (acyclic : H.IsAcyclic) (flat : H.IsFlat)
    (childEndpointsLost : ∀ p, P.Mem p → H.Lost B p)
    (distinctCuts : ¬ ∀ z, B.Mem z ↔ P.Mem z)
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss P y) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  obtain ⟨rank, rankArc⟩ := acyclic
  refine exitTailMem_iff_of_flat_rank rankArc flat ?_ distinctCuts hs proper
  intro p hFresh b hb
  exact properLoss_follows_endpoints rankArc flat ⟨childEndpointsLost p hFresh.1, hFresh.2⟩ hb

end LabelledQuotient

end PaperB
