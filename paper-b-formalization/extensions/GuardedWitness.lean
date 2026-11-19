import PaperB.Graph

namespace PaperB

inductive DecoderGate (Label : Type u) where
  | zero
  | terminal (label : Label)
  | orGate
  | guard (blocks : Label → Prop)

/-- The physical graph supplies all children. Ranks decrease along its arcs. -/
structure GuardedDecoder (g : Digraph) (Label : Type u) where
  root : Fin g.vertexCount
  gate : Fin g.vertexCount → DecoderGate Label
  rank : Fin g.vertexCount → Nat
  rank_lt : ∀ {v w}, g.HasArc v w → rank w < rank v
  zero_sink : ∀ {v w}, gate v = .zero → ¬ g.HasArc v w
  terminal_sink : ∀ {v w i}, gate v = .terminal i → ¬ g.HasArc v w
  guard_child : ∀ {v B}, gate v = .guard B →
    ∃ c, ∀ w, g.HasArc v w ↔ w = c

namespace GuardedDecoder

variable {g : Digraph} {Label : Type u}

def singleton (i : Label) : Label → Prop := fun j => j = i

def withCandidate (Q : Label → Prop) (i : Label) : Label → Prop :=
  fun j => Q j ∨ j = i

def Admissible (Q K : Label → Prop) : Prop :=
  (∃ i, K i) ∧ ∀ i, Q i → K i

def GuardFailed (d : GuardedDecoder g Label) (K : Label → Prop)
    (v : Fin g.vertexCount) : Prop :=
  match d.gate v with
  | .guard B => ∃ i, B i ∧ K i
  | _ => False

private def truthStep (d : GuardedDecoder g Label) (K : Label → Prop)
    (v : Fin g.vertexCount)
    (below : ∀ w, d.rank w < d.rank v → Prop) : Prop :=
  match d.gate v with
  | .zero => False
  | .terminal i => K i
  | .orGate => ∃ w, ∃ arc : g.HasArc v w, below w (d.rank_lt arc)
  | .guard B => (¬ ∃ i, B i ∧ K i) ∧
      (∃ w, ∃ arc : g.HasArc v w, below w (d.rank_lt arc))

/-- Exact recursive evaluation, well-founded on the DAG's topological rank. -/
def TrueAt (d : GuardedDecoder g Label) (K : Label → Prop)
    (v : Fin g.vertexCount) : Prop :=
  (measure d.rank).wf.fix (fun v below => d.truthStep K v below) v

private theorem trueAt_unfold (d : GuardedDecoder g Label) (K : Label → Prop)
    (v : Fin g.vertexCount) :
    d.TrueAt K v = d.truthStep K v (fun w _ => d.TrueAt K w) :=
  WellFounded.fix_eq (measure d.rank).wf
    (fun v below => d.truthStep K v below) v

theorem trueAt_eq (d : GuardedDecoder g Label) (K : Label → Prop)
    (v : Fin g.vertexCount) :
    d.TrueAt K v ↔
      (match d.gate v with
       | .zero => False
       | .terminal i => K i
       | .orGate => ∃ w, g.HasArc v w ∧ d.TrueAt K w
       | .guard B => (¬ ∃ i, B i ∧ K i) ∧
           (∃ w, g.HasArc v w ∧ d.TrueAt K w)) := by
  rw [d.trueAt_unfold K v]
  cases h : d.gate v with
  | zero => simp only [truthStep, h]
  | terminal i => simp only [truthStep, h]
  | orGate =>
      simp only [truthStep, h]
      constructor
      · rintro ⟨w, arc, ht⟩
        exact ⟨w, arc, ht⟩
      · rintro ⟨w, arc, ht⟩
        exact ⟨w, arc, ht⟩
  | guard B =>
      simp only [truthStep, h]
      constructor
      · rintro ⟨pass, w, arc, ht⟩
        exact ⟨pass, w, arc, ht⟩
      · rintro ⟨pass, w, arc, ht⟩
        exact ⟨pass, w, arc, ht⟩

theorem trueAt_guard (d : GuardedDecoder g Label) (K : Label → Prop)
    {v : Fin g.vertexCount} {B : Label → Prop} (hg : d.gate v = .guard B) :
    ∃ c, (∀ w, g.HasArc v w ↔ w = c) ∧
      (d.TrueAt K v ↔ (¬ ∃ i, B i ∧ K i) ∧ d.TrueAt K c) := by
  obtain ⟨c, hc⟩ := d.guard_child hg
  refine ⟨c, hc, ?_⟩
  rw [d.trueAt_eq K v, hg]
  constructor
  · rintro ⟨pass, w, arc, ht⟩
    have hw : w = c := (hc w).mp arc
    subst w
    exact ⟨pass, ht⟩
  · rintro ⟨pass, ht⟩
    exact ⟨pass, c, (hc c).mpr rfl, ht⟩

/-- Targets are physical terminal vertices, so multiple targets may share a label. -/
def ReachesLabel (d : GuardedDecoder g Label)
    (failed : Fin g.vertexCount → Prop) (v : Fin g.vertexCount)
    (i : Label) : Prop :=
  ∃ z, d.gate z = .terminal i ∧ g.SurvivingPath failed v z

private theorem path_of_true (d : GuardedDecoder g Label) (K : Label → Prop) :
    ∀ v, d.TrueAt K v → ∃ i, K i ∧ d.ReachesLabel (d.GuardFailed K) v i := by
  intro v
  apply (measure d.rank).wf.induction
    (C := fun a => d.TrueAt K a → ∃ i, K i ∧ d.ReachesLabel (d.GuardFailed K) a i) v
  intro a ih ha
  cases hg : d.gate a with
  | zero =>
      rw [d.trueAt_eq K a, hg] at ha
      exact ha.elim
  | terminal i =>
      rw [d.trueAt_eq K a, hg] at ha
      have alive : ¬ d.GuardFailed K a := by simp [GuardFailed, hg]
      exact ⟨i, ha, a, hg, AvoidPath.refl a alive⟩
  | orGate =>
      rw [d.trueAt_eq K a, hg] at ha
      obtain ⟨w, arc, hw⟩ := ha
      obtain ⟨i, hi, z, hz, p⟩ := ih w (d.rank_lt arc) hw
      have alive : ¬ d.GuardFailed K a := by simp [GuardFailed, hg]
      exact ⟨i, hi, z, hz, AvoidPath.step a w z alive arc p⟩
  | guard B =>
      rw [d.trueAt_eq K a, hg] at ha
      obtain ⟨pass, w, arc, hw⟩ := ha
      obtain ⟨i, hi, z, hz, p⟩ := ih w (d.rank_lt arc) hw
      have alive : ¬ d.GuardFailed K a := by
        simpa only [GuardFailed, hg] using pass
      exact ⟨i, hi, z, hz, AvoidPath.step a w z alive arc p⟩

private theorem true_of_path (d : GuardedDecoder g Label) (K : Label → Prop)
    {v z : Fin g.vertexCount} {i : Label} (hi : K i)
    (p : g.SurvivingPath (d.GuardFailed K) v z)
    (hz : d.gate z = .terminal i) : d.TrueAt K v := by
  change AvoidPath g.HasArc (d.GuardFailed K) v z at p
  revert hz
  induction p with
  | refl a _ =>
      intro hz
      rw [d.trueAt_eq K a, hz]
      exact hi
  | step a b c alive arc _ ih =>
      intro hz
      cases hg : d.gate a with
      | zero => exact (d.zero_sink hg arc).elim
      | terminal j => exact (d.terminal_sink hg arc).elim
      | orGate =>
          rw [d.trueAt_eq K a, hg]
          exact ⟨b, arc, ih hz⟩
      | guard B =>
          rw [d.trueAt_eq K a, hg]
          have pass : ¬ ∃ j, B j ∧ K j := by
            simpa only [GuardFailed, hg] using alive
          exact ⟨pass, b, arc, ih hz⟩

theorem trueAt_iff_path (d : GuardedDecoder g Label) (K : Label → Prop)
    (v : Fin g.vertexCount) :
    d.TrueAt K v ↔ ∃ i, K i ∧ d.ReachesLabel (d.GuardFailed K) v i := by
  constructor
  · exact d.path_of_true K v
  · rintro ⟨i, hi, z, hz, p⟩
    exact d.true_of_path K hi p hz

private theorem path_mono {F F' : Fin g.vertexCount → Prop}
    (h : ∀ v, F' v → F v) {v z : Fin g.vertexCount}
    (p : g.SurvivingPath F v z) : g.SurvivingPath F' v z := by
  change AvoidPath g.HasArc F v z at p
  change AvoidPath g.HasArc F' v z
  induction p with
  | refl a alive => exact AvoidPath.refl a (fun hf => alive (h a hf))
  | step a b c alive arc _ ih =>
      exact AvoidPath.step a b c (fun hf => alive (h a hf)) arc ih

private theorem path_source_alive {F : Fin g.vertexCount → Prop}
    {v z : Fin g.vertexCount} (p : g.SurvivingPath F v z) : ¬ F v := by
  change AvoidPath g.HasArc F v z at p
  induction p with
  | refl a alive => exact alive
  | step a b c alive arc _ ih => exact alive

theorem guardFailed_mono (d : GuardedDecoder g Label) {J K : Label → Prop}
    (hsub : ∀ i, J i → K i) (v : Fin g.vertexCount) :
    d.GuardFailed J v → d.GuardFailed K v := by
  intro h
  cases hg : d.gate v with
  | zero => simpa only [GuardFailed, hg] using h
  | terminal i => simpa only [GuardFailed, hg] using h
  | orGate => simpa only [GuardFailed, hg] using h
  | guard B =>
      simp only [GuardFailed, hg] at h ⊢
      obtain ⟨i, hb, hi⟩ := h
      exact ⟨i, hb, hsub i hi⟩

/-- A guard meeting `Q` is deleted first, along with its incident arcs. -/
def RemainingFailed (d : GuardedDecoder g Label) (Q : Label → Prop)
    (i : Label) (v : Fin g.vertexCount) : Prop :=
  ¬ d.GuardFailed Q v ∧ d.GuardFailed (singleton i) v

/-- An original-graph path avoiding both failure predicates is precisely a
surviving path in the residual graph with the candidate's guards failed. -/
def ResidualQuery (d : GuardedDecoder g Label) (Q : Label → Prop)
    (i : Label) : Prop :=
  d.ReachesLabel (fun v => d.GuardFailed Q v ∨ d.RemainingFailed Q i v) d.root i

theorem guardFailed_withCandidate (d : GuardedDecoder g Label)
    (Q : Label → Prop) (i : Label) (v : Fin g.vertexCount) :
    d.GuardFailed (withCandidate Q i) v ↔
      d.GuardFailed Q v ∨ d.RemainingFailed Q i v := by
  have hu : d.GuardFailed (withCandidate Q i) v ↔
      d.GuardFailed Q v ∨ d.GuardFailed (singleton i) v := by
    cases hg : d.gate v with
    | zero => simp [GuardFailed, hg]
    | terminal j => simp [GuardFailed, hg]
    | orGate => simp [GuardFailed, hg]
    | guard B =>
        simp only [GuardFailed, hg, withCandidate, singleton]
        constructor
        · rintro ⟨j, hb, hj⟩
          rcases hj with hq | he
          · exact Or.inl ⟨j, hb, hq⟩
          · exact Or.inr ⟨j, hb, he⟩
        · intro h
          rcases h with ⟨j, hb, hq⟩ | ⟨j, hb, he⟩
          · exact ⟨j, hb, Or.inl hq⟩
          · exact ⟨j, hb, Or.inr he⟩
  rw [hu]
  by_cases hq : d.GuardFailed Q v <;> simp [RemainingFailed, hq]

theorem residualQuery_iff_path (d : GuardedDecoder g Label)
    (Q : Label → Prop) (i : Label) :
    d.ResidualQuery Q i ↔
      d.ReachesLabel (d.GuardFailed (withCandidate Q i)) d.root i := by
  constructor
  · rintro ⟨z, hz, p⟩
    exact ⟨z, hz, path_mono (g := g)
      (fun v => (d.guardFailed_withCandidate Q i v).mp) p⟩
  · rintro ⟨z, hz, p⟩
    exact ⟨z, hz, path_mono (g := g)
      (fun v => (d.guardFailed_withCandidate Q i v).mpr) p⟩

theorem no_detection_of_root_deleted (d : GuardedDecoder g Label)
    {Q K : Label → Prop} (hK : Admissible Q K)
    (hdel : d.GuardFailed Q d.root) : ¬ d.TrueAt K d.root := by
  intro ht
  obtain ⟨i, hi, z, hz, p⟩ := (d.trueAt_iff_path K d.root).mp ht
  exact path_source_alive (g := g) p (d.guardFailed_mono hK.2 d.root hdel)

def HealthyZero (d : GuardedDecoder g Label) (t₀ : Label) : Prop :=
  ¬ d.TrueAt (singleton t₀) d.root

theorem detects_iff_true (d : GuardedDecoder g Label) {t₀ : Label}
    (healthy : d.HealthyZero t₀) (K : Label → Prop) :
    (¬ (d.TrueAt K d.root ↔ d.TrueAt (singleton t₀) d.root)) ↔
      d.TrueAt K d.root := by
  classical
  constructor
  · intro h
    by_cases ht : d.TrueAt K d.root
    · exact ht
    · exact (h ⟨fun hk => (ht hk).elim, fun hr => (healthy hr).elim⟩).elim
  · intro ht he
    exact healthy (he.mp ht)

theorem candidate_admissible (Q : Label → Prop) (i : Label) :
    Admissible Q (withCandidate Q i) :=
  ⟨⟨i, Or.inr rfl⟩, fun _ h => Or.inl h⟩

theorem candidate_true_of_query (d : GuardedDecoder g Label)
    {Q : Label → Prop} {i : Label} (hq : d.ResidualQuery Q i) :
    d.TrueAt (withCandidate Q i) d.root :=
  (d.trueAt_iff_path (withCandidate Q i) d.root).mpr
    ⟨i, Or.inr rfl, (d.residualQuery_iff_path Q i).mp hq⟩

/-- The same physical terminal and path work on `Q ∪ {i} ⊆ K`. -/
theorem shrink_detecting (d : GuardedDecoder g Label) {t₀ : Label}
    (healthy : d.HealthyZero t₀) {Q K : Label → Prop}
    (hK : Admissible Q K) (ht : d.TrueAt K d.root) :
    ∃ i, i ≠ t₀ ∧ K i ∧ (∀ j, withCandidate Q i j → K j) ∧
      Admissible Q (withCandidate Q i) ∧
      d.TrueAt (withCandidate Q i) d.root ∧ d.ResidualQuery Q i := by
  obtain ⟨i, hi, z, hz, p⟩ := (d.trueAt_iff_path K d.root).mp ht
  have hne : i ≠ t₀ := by
    intro he
    subst i
    have hsub : ∀ j, singleton t₀ j → K j := by
      intro j hj
      change j = t₀ at hj
      subst j
      exact hi
    have p₀ : g.SurvivingPath (d.GuardFailed (singleton t₀)) d.root z :=
      path_mono (g := g) (d.guardFailed_mono hsub) p
    exact healthy ((d.trueAt_iff_path (singleton t₀) d.root).mpr
      ⟨t₀, rfl, z, hz, p₀⟩)
  have hsub : ∀ j, withCandidate Q i j → K j := by
    intro j hj
    change Q j ∨ j = i at hj
    rcases hj with hq | he
    · exact hK.2 j hq
    · subst j
      exact hi
  have hw : d.ReachesLabel (d.GuardFailed (withCandidate Q i)) d.root i :=
    ⟨z, hz, path_mono (g := g) (d.guardFailed_mono hsub) p⟩
  have hq := (d.residualQuery_iff_path Q i).mpr hw
  exact ⟨i, hne, hi, hsub, candidate_admissible Q i,
    d.candidate_true_of_query hq, hq⟩

/-- For either prescribed set, a true candidate test answers its own query. -/
theorem candidate_true_iff_residualQuery (d : GuardedDecoder g Label)
    {t₀ i : Label} {Q : Label → Prop} (healthy : d.HealthyZero t₀)
    (hQ : Q = (fun _ => False) ∨ Q = singleton t₀) :
    d.TrueAt (withCandidate Q i) d.root ↔ d.ResidualQuery Q i := by
  constructor
  · intro ht
    obtain ⟨j, hj₀, hj, _, _, _, hquery⟩ :=
      d.shrink_detecting healthy (candidate_admissible Q i) ht
    change Q j ∨ j = i at hj
    rcases hj with hjQ | hji
    · rcases hQ with he | he
      · rw [he] at hjQ
        exact hjQ.elim
      · rw [he] at hjQ
        exact (hj₀ hjQ).elim
    · subst j
      exact hquery
  · exact d.candidate_true_of_query

/-- In the healthy-zero case, detection is equivalent to a positive residual
query for a label other than `t₀`. This holds in particular for `Q = ∅` and
`Q = {t₀}`. -/
theorem exists_detecting_iff_residualQuery (d : GuardedDecoder g Label)
    {t₀ : Label} (healthy : d.HealthyZero t₀) (Q : Label → Prop) :
    (∃ K, Admissible Q K ∧
      ¬ (d.TrueAt K d.root ↔ d.TrueAt (singleton t₀) d.root)) ↔
      ∃ i, i ≠ t₀ ∧ d.ResidualQuery Q i := by
  constructor
  · rintro ⟨K, hK, hdetect⟩
    have ht := (d.detects_iff_true healthy K).mp hdetect
    obtain ⟨i, hne, _, _, _, _, hq⟩ := d.shrink_detecting healthy hK ht
    exact ⟨i, hne, hq⟩
  · rintro ⟨i, _, hq⟩
    exact ⟨withCandidate Q i, candidate_admissible Q i,
      (d.detects_iff_true healthy (withCandidate Q i)).mpr
        (d.candidate_true_of_query hq)⟩

end GuardedDecoder
end PaperB
