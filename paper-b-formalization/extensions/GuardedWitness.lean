import Lean
import PaperB.Graph

namespace PaperB

universe u

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

namespace PaperB.EX62

open PaperB
universe u

/-! Each list enumerates actual residual guard incidences or terminal occurrences.
The grouping routine uses one scatter pass per list. -/

structure FailureSlots (V : Type u) where
  first : Option V
  second : Option V

def FailureSlots.Fails {V : Type u} (s : FailureSlots V) (v : V) : Prop :=
  s.first = some v ∨ s.second = some v

structure Bucket (V : Type u) where
  guards : List V
  targets : List V

variable {V : Type u} {n : Nat}

def Bucket.slots (b : Bucket V) : FailureSlots V :=
  match b.guards with
  | [] => ⟨none, none⟩
  | [v] => ⟨some v, none⟩
  | v :: w :: _ => ⟨some v, some w⟩

private theorem slots_mem (b : Bucket V) (h : b.guards.length ≤ 2)
    (v : V) : b.slots.Fails v ↔ v ∈ b.guards := by
  rcases b with ⟨gs, ts⟩
  rcases gs with _ | ⟨a, _ | ⟨c, _ | ⟨e, es⟩⟩⟩
  · simp [Bucket.slots, FailureSlots.Fails]
  · simp [Bucket.slots, FailureSlots.Fails, eq_comm]
  · simp [Bucket.slots, FailureSlots.Fails, eq_comm]
  · simp only [List.length_cons] at h
    omega

abbrev Table (n : Nat) (V : Type u) :=
  { a : Array (Bucket V) // a.size = n }

private def emptyBucket : Bucket V := ⟨[], []⟩

def empty (n : Nat) : Table n V :=
  ⟨Array.replicate n emptyBucket, by simp⟩

def get (t : Table n V) (i : Fin n) : Bucket V :=
  t.val[i.val]'(by rw [t.property]; exact i.isLt)

def update (t : Table n V) (i : Fin n) (f : Bucket V → Bucket V) :
    Table n V :=
  ⟨t.val.set i.val (f (get t i)) (by rw [t.property]; exact i.isLt),
    by simp [t.property]⟩

private theorem get_empty (i : Fin n) :
    get (empty n : Table n V) i = emptyBucket := by
  simp [get, empty]

private theorem get_update (t : Table n V) (i j : Fin n)
    (f : Bucket V → Bucket V) :
    get (update t i f) j = if j = i then f (get t j) else get t j := by
  by_cases h : j = i
  · subst j
    simp [get, update]
  · have hji : j.val ≠ i.val := fun e => h (Fin.ext e)
    simp [get, update, h]
    rw [Array.getElem_set]
    split <;> first | rfl | omega

def addGuard [DecidableEq V] (b : Bucket V) (v : V) : Bucket V :=
  { b with guards := if v ∈ b.guards then b.guards else v :: b.guards }

def addTerminal (b : Bucket V) (v : V) : Bucket V :=
  { b with targets := v :: b.targets }

/-- Each iteration reads one raw occurrence and updates its one bucket. -/
def pass (step : Bucket V → V → Bucket V) :
    List (Fin n × V) → Table n V → Nat → Table n V × Nat
  | [], t, scans => (t, scans)
  | (i, v) :: xs, t, scans =>
      pass step xs (update t i (fun b => step b v)) (scans + 1)

theorem pass_scans (step : Bucket V → V → Bucket V)
    (xs : List (Fin n × V)) (t : Table n V) (scans : Nat) :
    (pass step xs t scans).2 = scans + xs.length := by
  induction xs generalizing t scans with
  | nil => simp [pass]
  | cons p xs ih =>
      rcases p with ⟨i, v⟩
      simp only [pass, ih, List.length_cons]
      omega

/-- Specification only: the raw subsequence for a label, in input order. -/
def hits (i : Fin n) : List (Fin n × V) → List V
  | [] => []
  | (j, v) :: xs => if i = j then v :: hits i xs else hits i xs

private theorem mem_hits (i : Fin n) (v : V) (xs : List (Fin n × V)) :
    v ∈ hits i xs ↔ (i, v) ∈ xs := by
  induction xs with
  | nil => simp [hits]
  | cons p xs ih =>
      rcases p with ⟨j, w⟩
      by_cases h : i = j
      · subst j
        simp [hits, ih]
      · simp [hits, h, ih]

private theorem get_pass (step : Bucket V → V → Bucket V)
    (xs : List (Fin n × V)) (t : Table n V) (scans : Nat) (i : Fin n) :
    get (pass step xs t scans).1 i =
      (hits i xs).foldl step (get t i) := by
  induction xs generalizing t scans with
  | nil => rfl
  | cons p xs ih =>
      rcases p with ⟨j, v⟩
      by_cases h : i = j
      · subst j
        simp [pass, ih, get_update, hits]
      · simp [pass, ih, get_update, hits, h]

private theorem addGuard_mem [DecidableEq V] (b : Bucket V) (w v : V) :
    v ∈ (addGuard b w).guards ↔ v = w ∨ v ∈ b.guards := by
  by_cases h : w ∈ b.guards
  · simp only [addGuard, if_pos h]
    constructor
    · exact Or.inr
    · rintro (e | hv)
      · subst v
        exact h
      · exact hv
  · simp [addGuard, h]

private theorem foldGuard_mem [DecidableEq V] (xs : List V)
    (b : Bucket V) (v : V) :
    v ∈ (xs.foldl addGuard b).guards ↔ v ∈ xs ∨ v ∈ b.guards := by
  induction xs generalizing b with
  | nil => simp
  | cons w xs ih =>
      simp only [List.foldl_cons, ih, addGuard_mem, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

private theorem foldGuard_nodup [DecidableEq V] (xs : List V)
    (b : Bucket V) (hb : b.guards.Nodup) :
    (xs.foldl addGuard b).guards.Nodup := by
  induction xs generalizing b with
  | nil => exact hb
  | cons w xs ih =>
      change (xs.foldl addGuard (addGuard b w)).guards.Nodup
      apply ih
      by_cases h : w ∈ b.guards <;> simp [addGuard, h, hb, List.nodup_cons]

private theorem foldGuard_length [DecidableEq V] (xs : List V)
    (b : Bucket V) :
    (xs.foldl addGuard b).guards.length ≤ b.guards.length + xs.length := by
  induction xs generalizing b with
  | nil => simp
  | cons w xs ih =>
      have h := ih (addGuard b w)
      have hw : (addGuard b w).guards.length ≤ b.guards.length + 1 := by
        by_cases hm : w ∈ b.guards <;> simp [addGuard, hm]
      simp only [List.foldl_cons, List.length_cons]
      omega

private theorem foldGuard_targets [DecidableEq V] (xs : List V)
    (b : Bucket V) : (xs.foldl addGuard b).targets = b.targets := by
  induction xs generalizing b with
  | nil => rfl
  | cons w xs ih => simp [ih, addGuard]

private theorem foldTerminal_guards (xs : List V) (b : Bucket V) :
    (xs.foldl addTerminal b).guards = b.guards := by
  induction xs generalizing b with
  | nil => rfl
  | cons w xs ih => simp [ih, addTerminal]

private theorem foldTerminal_targets (xs : List V) (b : Bucket V) :
    (xs.foldl addTerminal b).targets = xs.reverse ++ b.targets := by
  induction xs generalizing b with
  | nil => rfl
  | cons w xs ih =>
      simp [ih, addTerminal, List.reverse_cons, List.append_assoc]

/-- No occurrence sorting, per-label rescan, or terminal deduplication. -/
def build [DecidableEq V] (gs ts : List (Fin n × V)) : Table n V × Nat :=
  let p := pass addGuard gs (empty n) 0
  pass addTerminal ts p.1 p.2

theorem build_scans [DecidableEq V] (gs ts : List (Fin n × V)) :
    (build gs ts).2 = gs.length + ts.length := by
  simp [build, pass_scans]

private theorem build_guards [DecidableEq V]
    (gs ts : List (Fin n × V)) (i : Fin n) :
    (get (build gs ts).1 i).guards =
      ((hits i gs).foldl addGuard emptyBucket).guards := by
  simp only [build, get_pass, foldTerminal_guards, get_empty]

theorem build_targets [DecidableEq V]
    (gs ts : List (Fin n × V)) (i : Fin n) :
    (get (build gs ts).1 i).targets = (hits i ts).reverse := by
  simp only [build, get_pass, foldTerminal_targets, foldGuard_targets,
    get_empty, emptyBucket, List.append_nil]

private theorem length_of_no_three {xs : List V} (hn : xs.Nodup)
    (hw : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs →
      a = b ∨ a = c ∨ b = c) : xs.length ≤ 2 := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp
  · simp
  · simp
  · simp only [List.nodup_cons] at hn
    rcases hw a b c (by simp) (by simp) (by simp) with h | h | h
    · exact (hn.1 (by simp [h])).elim
    · exact (hn.1 (by simp [h])).elim
    · exact (hn.2.1 (by simp [h])).elim

/-- Enumeration of the declared labels, independent of occupied buckets. -/
def labels : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => 0 :: (labels n).map Fin.succ

@[simp] theorem labels_length (n : Nat) : (labels n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [labels, ih]

theorem mem_labels (i : Fin n) : i ∈ labels n := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases (by simp [labels]) (fun j => ?_) i
      simp only [labels, List.mem_cons, List.mem_map]
      exact Or.inr ⟨j, ih j, rfl⟩

def rows (t : Table n V) : List (Fin n × Bucket V) :=
  (labels n).map fun i => (i, get t i)

@[simp] theorem rows_length (t : Table n V) : (rows t).length = n := by
  simp [rows]

theorem mem_rows (t : Table n V) (i : Fin n) (b : Bucket V) :
    (i, b) ∈ rows t ↔ b = get t i := by
  constructor
  · intro h
    obtain ⟨j, _, e⟩ := List.mem_map.mp h
    have hj : j = i := congrArg Prod.fst e
    subst j
    exact (congrArg Prod.snd e).symm
  · intro h
    subst b
    exact List.mem_map.mpr ⟨i, mem_labels i, rfl⟩

/-- Sum a field over a list; used for the sizes of the materialized rows. -/
def sumOn {A : Type u} : List A → (A → Nat) → Nat
  | [], _ => 0
  | a :: as, f => f a + sumOn as f

private theorem sumOn_map {A B : Type u} (xs : List A) (g : A → B)
    (f : B → Nat) :
    sumOn (xs.map g) f = sumOn xs (fun a => f (g a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sumOn, ih]

private theorem sumOn_const {A : Type u} (xs : List A) (k : Nat) :
    sumOn xs (fun _ => k) = xs.length * k := by
  induction xs with
  | nil => simp [sumOn]
  | cons a xs ih =>
      simp [sumOn, ih, Nat.add_mul, Nat.add_comm]

private theorem sumOn_mono {A : Type u} (xs : List A) {f g : A → Nat}
    (h : ∀ a, f a ≤ g a) : sumOn xs f ≤ sumOn xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a xs ih => exact Nat.add_le_add (h a) ih

private theorem sumOn_add {A : Type u} (xs : List A) (f g : A → Nat) :
    sumOn xs (fun a => f a + g a) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [sumOn, ih]
      omega

private theorem sum_indicator (j : Fin n) :
    sumOn (labels n) (fun i => if i = j then 1 else 0) = 1 := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      have nz (i : Fin n) : i.succ ≠ (0 : Fin (n + 1)) := by
        intro e
        have h := congrArg Fin.val e
        change i.val + 1 = 0 at h
        omega
      refine Fin.cases ?_ (fun k => ?_) j
      · have e : (fun i : Fin n =>
            if i.succ = (0 : Fin (n + 1)) then (1 : Nat) else 0) =
            (fun _ : Fin n => (0 : Nat)) := by
          funext i
          simp only [if_neg (nz i)]
        simp only [labels, sumOn, sumOn_map, e, sumOn_const,
          Nat.mul_zero, Nat.add_zero] <;> simp
      · have e : (fun i : Fin n => if i.succ = k.succ then (1 : Nat) else 0) =
            (fun i => if i = k then 1 else 0) := by
          funext i
          have he : i.succ = k.succ ↔ i = k := by
            constructor
            · intro h
              apply Fin.ext
              have hv := congrArg Fin.val h
              change i.val + 1 = k.val + 1 at hv
              omega
            · intro h
              subst i
              rfl
          simp only [he]
        simp only [labels, sumOn, if_neg (Ne.symm (nz k)), sumOn_map, e,
          ih k, Nat.zero_add]

private theorem sum_hits (xs : List (Fin n × V)) :
    sumOn (labels n) (fun i => (hits i xs).length) = xs.length := by
  induction xs with
  | nil => simp [hits, sumOn_const]
  | cons p xs ih =>
      rcases p with ⟨j, v⟩
      have e : (fun i => (hits i ((j, v) :: xs)).length) =
          (fun i => (if i = j then 1 else 0) + (hits i xs).length) := by
        funext i
        by_cases h : i = j <;> simp [hits, h, Nat.add_comm]
      rw [e, sumOn_add, sum_indicator, ih] <;> simp [Nat.add_comm]

structure Input {g : Digraph} (d : GuardedDecoder g (Fin n))
    (Q : Fin n → Prop) where
  remaining : List (Fin n × Fin g.vertexCount)
  terminals : List (Fin n × Fin g.vertexCount)
  remaining_spec : ∀ i v, (i, v) ∈ remaining ↔ d.RemainingFailed Q i v
  terminal_spec : ∀ i v, (i, v) ∈ terminals ↔ d.gate v = .terminal i
  width : ∀ i a b c,
    d.RemainingFailed Q i a → d.RemainingFailed Q i b →
    d.RemainingFailed Q i c → a = b ∨ a = c ∨ b = c

namespace Input

variable {g : Digraph} {d : GuardedDecoder g (Fin n)} {Q : Fin n → Prop}

def result (x : Input d Q) : Table n (Fin g.vertexCount) × Nat :=
  build x.remaining x.terminals

def bucket (x : Input d Q) (i : Fin n) : Bucket (Fin g.vertexCount) :=
  get x.result.1 i

theorem scans (x : Input d Q) :
    x.result.2 = x.remaining.length + x.terminals.length :=
  build_scans _ _

theorem guards_exact (x : Input d Q) (i : Fin n) (v : Fin g.vertexCount) :
    v ∈ (x.bucket i).guards ↔ d.RemainingFailed Q i v := by
  change v ∈ (get (build x.remaining x.terminals).1 i).guards ↔ _
  rw [build_guards, foldGuard_mem]
  simpa only [emptyBucket, List.not_mem_nil, or_false, mem_hits] using
    x.remaining_spec i v

theorem guards_nodup (x : Input d Q) (i : Fin n) :
    (x.bucket i).guards.Nodup := by
  change (get (build x.remaining x.terminals).1 i).guards.Nodup
  rw [build_guards]
  exact foldGuard_nodup _ _ (by simp [emptyBucket])

theorem guards_length (x : Input d Q) (i : Fin n) :
    (x.bucket i).guards.length ≤ 2 := by
  apply length_of_no_three (x.guards_nodup i)
  intro a b c ha hb hc
  exact x.width i a b c ((x.guards_exact i a).mp ha)
    ((x.guards_exact i b).mp hb) ((x.guards_exact i c).mp hc)

/-- In particular, this applies before each insertion in the guard pass. -/
theorem guard_pass_prefix_length (x : Input d Q)
    (xs : List (Fin n × Fin g.vertexCount))
    (hsub : ∀ p, p ∈ xs → p ∈ x.remaining) (i : Fin n) :
    (get (pass addGuard xs (empty n) 0).1 i).guards.length ≤ 2 := by
  rw [get_pass, get_empty]
  apply length_of_no_three (foldGuard_nodup _ _ (by simp [emptyBucket]))
  have hmem (v : Fin g.vertexCount)
      (hv : v ∈ ((hits i xs).foldl addGuard emptyBucket).guards) :
      d.RemainingFailed Q i v := by
    have hm : (i, v) ∈ xs := by
      simpa only [foldGuard_mem, emptyBucket, List.not_mem_nil, or_false,
        mem_hits] using hv
    exact (x.remaining_spec i v).mp (hsub _ hm)
  intro a b c ha hb hc
  exact x.width i a b c (hmem a ha) (hmem b hb) (hmem c hc)

theorem slots_exact (x : Input d Q) (i : Fin n) (v : Fin g.vertexCount) :
    (x.bucket i).slots.Fails v ↔ d.RemainingFailed Q i v :=
  (slots_mem _ (x.guards_length i) v).trans (x.guards_exact i v)

/-- The reversal comes from consing; every occurrence is retained. -/
theorem targets_list (x : Input d Q) (i : Fin n) :
    (x.bucket i).targets = (hits i x.terminals).reverse :=
  build_targets _ _ _

theorem targets_exact (x : Input d Q) (i : Fin n) (v : Fin g.vertexCount) :
    v ∈ (x.bucket i).targets ↔ d.gate v = .terminal i := by
  rw [x.targets_list]
  simpa only [List.mem_reverse, mem_hits] using x.terminal_spec i v

theorem row_exact (x : Input d Q) (i : Fin n) (b : Bucket (Fin g.vertexCount))
    (h : (i, b) ∈ rows x.result.1) :
    b.guards.Nodup ∧ b.guards.length ≤ 2 ∧
    (∀ v, v ∈ b.guards ↔ d.RemainingFailed Q i v) ∧
    (∀ v, b.slots.Fails v ↔ d.RemainingFailed Q i v) ∧
    b.targets = (hits i x.terminals).reverse ∧
    (∀ v, v ∈ b.targets ↔ d.gate v = .terminal i) := by
  have hb : b = x.bucket i := (mem_rows _ _ _).mp h
  subst b
  exact ⟨x.guards_nodup i, x.guards_length i, x.guards_exact i,
    x.slots_exact i, x.targets_list i, x.targets_exact i⟩

theorem total_targets (x : Input d Q) :
    sumOn (rows x.result.1) (fun r => r.2.targets.length) =
      x.terminals.length := by
  simp only [rows, sumOn_map]
  change sumOn (labels n) (fun i => (x.bucket i).targets.length) =
    x.terminals.length
  simpa only [x.targets_list, List.length_reverse] using sum_hits x.terminals

theorem total_guards_raw (x : Input d Q) :
    sumOn (rows x.result.1) (fun r => r.2.guards.length) ≤
      x.remaining.length := by
  simp only [rows, sumOn_map]
  change sumOn (labels n) (fun i => (x.bucket i).guards.length) ≤ _
  calc
    _ ≤ sumOn (labels n) (fun i => (hits i x.remaining).length) := by
      apply sumOn_mono
      intro i
      change (get (build x.remaining x.terminals).1 i).guards.length ≤ _
      rw [build_guards]
      simpa [emptyBucket] using
        (foldGuard_length (hits i x.remaining)
          (emptyBucket : Bucket (Fin g.vertexCount)))
    _ = x.remaining.length := sum_hits x.remaining

theorem total_guards_width (x : Input d Q) :
    sumOn (rows x.result.1) (fun r => r.2.guards.length) ≤ 2 * n := by
  simp only [rows, sumOn_map]
  change sumOn (labels n) (fun i => (x.bucket i).guards.length) ≤ _
  calc
    _ ≤ sumOn (labels n) (fun _ => 2) :=
      sumOn_mono _ (x.guards_length)
    _ = 2 * n := by rw [sumOn_const, labels_length, Nat.mul_comm]

/-- Row headers plus all guard and terminal list cells. Empty labels
    contribute one row each. There are also two slot fields per row. -/
theorem total_list_size (x : Input d Q) :
    (rows x.result.1).length +
      sumOn (rows x.result.1) (fun r => r.2.guards.length) +
      sumOn (rows x.result.1) (fun r => r.2.targets.length) ≤
    n + min x.remaining.length (2 * n) + x.terminals.length := by
  rw [rows_length, x.total_targets]
  have h : sumOn (rows x.result.1) (fun r => r.2.guards.length) ≤
      min x.remaining.length (2 * n) := by
    rcases Nat.le_total x.remaining.length (2 * n) with h | h
    · rw [Nat.min_eq_left h]
      exact x.total_guards_raw
    · rw [Nat.min_eq_right h]
      exact x.total_guards_width
  omega

/--
A separately supplied list oracle can interpret a row directly.
`survives` is the caller's residual reachability relation, parameterized
by the additional failed vertices; baseline failures are already part
of that relation. This lemma builds no index and asserts no oracle bound.
-/
theorem list_oracle_row (x : Input d Q) (i : Fin n)
    (oracle : FailureSlots (Fin g.vertexCount) → List (Fin g.vertexCount) → Bool)
    (survives : (Fin g.vertexCount → Prop) → Fin g.vertexCount → Prop)
    (correct : ∀ f ts, oracle f ts = true ↔
      ∃ v, v ∈ ts ∧ survives f.Fails v) :
    oracle (x.bucket i).slots (x.bucket i).targets = true ↔
      ∃ v, d.gate v = .terminal i ∧ survives (d.RemainingFailed Q i) v := by
  have hf : (x.bucket i).slots.Fails = d.RemainingFailed Q i :=
    funext fun v => propext (x.slots_exact i v)
  rw [correct, hf]
  constructor
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, (x.targets_exact i v).mp hv, hs⟩
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, (x.targets_exact i v).mpr hv, hs⟩

end Input
end PaperB.EX62
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.EX62.SharedResidual

/-
Pass the packed mask's Boolean lookup to `guardCheck`, or pass an
already-refined vertex check directly to `build`. The proof argument to
`survivingPath_iff` is exact: for EX6.2, take `base := d.GuardFailed Q`.

The excerpt does not include the query-row declaration. `queryRow_iff`
therefore takes the existing row interpretation with its path test
abstracted; it does not introduce a second row format or interpretation.
-/

def guardCheck {Label V : Type} (maskBit : Label → Bool)
    (guardLabels : V → List Label) (v : V) : Bool :=
  (guardLabels v).any maskBit

theorem guardCheck_refines {Label V : Type}
    (maskBit : Label → Bool) (Q : Label → Prop)
    (guardLabels : V → List Label) (base : V → Prop)
    (bitExact : ∀ i, maskBit i = true ↔ Q i)
    (guardExact : ∀ v, base v ↔ ∃ i, i ∈ guardLabels v ∧ Q i)
    (v : V) :
    guardCheck maskBit guardLabels v = true ↔ base v := by
  rw [guardExact v]
  simp only [guardCheck, List.any_eq_true, bitExact]

private def readFin {α : Type} {n : Nat} (xs : Array α)
    (sizeExact : xs.size = n) (i : Fin n) : α :=
  xs[i.val]'(by rw [sizeExact]; exact i.isLt)

@[simp] private theorem readFin_ofFn {α : Type} {n : Nat}
    (f : Fin n → α) (sizeExact : (Array.ofFn f).size = n) (i : Fin n) :
    readFin (Array.ofFn f) sizeExact i = f i := by
  simp [readFin]

/-- Charge one visit for every original occurrence, even in a deleted row. -/
private def scan {V : Type} (keep : V → Bool) : List V → List V × Nat
  | [] => ([], 0)
  | v :: vs =>
    let k := keep v
    let rest := scan keep vs
    (if k then v :: rest.1 else rest.1, rest.2 + 1)

private theorem scan_exact {V : Type} (keep : V → Bool) (xs : List V) :
    scan keep xs = (xs.filter keep, xs.length) := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    cases hv : keep v <;>
      simp [scan, List.filter_cons, hv, ih, Nat.succ_eq_add_one]

structure View (g : Digraph) where
  bits : Array Bool
  bitsSize : bits.size = g.vertexCount
  rows : Array (List (Fin g.vertexCount))
  rowsSize : rows.size = g.vertexCount
  arcScans : Nat

def View.deleted {g : Digraph} (r : View g) (v : Fin g.vertexCount) : Bool :=
  readFin r.bits r.bitsSize v

def View.row {g : Digraph} (r : View g) (u : Fin g.vertexCount) :
    List (Fin g.vertexCount) :=
  readFin r.rows r.rowsSize u

/-- The residual graph uses the view's row array directly as its adjacency. -/
abbrev View.graph {g : Digraph} (r : View g) : Digraph :=
  { vertexCount := g.vertexCount, adj := r.rows, adj_size := r.rowsSize }

/-- Cache one baseline check per ID and scan each original row once. -/
def build (g : Digraph) (check : Fin g.vertexCount → Bool) : View g :=
  let bits := Array.ofFn check
  have hb : bits.size = g.vertexCount := by simp [bits]
  let packed := Array.ofFn fun u : Fin g.vertexCount =>
    let sourceDeleted := readFin bits hb u
    scan (fun v => !(sourceDeleted || readFin bits hb v)) (g.outArcs u)
  have hp : packed.size = g.vertexCount := by simp [packed]
  let arcScans := packed.foldl (fun acc p => acc + p.2) 0
  let rows := Array.ofFn fun u : Fin g.vertexCount => (readFin packed hp u).1
  ⟨bits, hb, rows, by simp [rows], arcScans⟩

def View.vertexScans {g : Digraph} (r : View g) : Nat :=
  r.bits.size

private theorem foldlPackedCountsList {α : Type} (xs : List (α × Nat)) (n : Nat) :
    xs.foldl (fun acc p => acc + p.2) n = n + (xs.map Prod.snd).sum := by
  induction xs generalizing n with
  | nil => simp
  | cons p xs ih => simp [ih, Nat.add_assoc]

private theorem foldlPackedCountsOfFn {α : Type} {n : Nat} (f : Fin n → α × Nat) :
    (Array.ofFn f).foldl (fun acc p => acc + p.2) 0 =
      (List.ofFn fun i => (f i).2).sum := by
  rw [← Array.foldl_toList, foldlPackedCountsList, Nat.zero_add,
    Array.toList_ofFn, List.map_ofFn]
  rfl

@[simp] theorem deleted_build (g : Digraph) (check : Fin g.vertexCount → Bool)
    (v : Fin g.vertexCount) :
    (build g check).deleted v = check v := by
  simp [build, View.deleted]

theorem row_exact (g : Digraph) (check : Fin g.vertexCount → Bool)
    (u : Fin g.vertexCount) :
    (build g check).row u =
      (g.outArcs u).filter (fun v => !(check u || check v)) := by
  simp [build, View.row, scan_exact]

theorem build_scans (g : Digraph) (check : Fin g.vertexCount → Bool) :
    (build g check).vertexScans = g.vertexCount ∧
    (build g check).arcScans =
      (List.ofFn (fun u : Fin g.vertexCount => (g.outArcs u).length)).sum := by
  refine ⟨(build g check).bitsSize, ?_⟩
  simp only [build, foldlPackedCountsOfFn, scan_exact]

/-- List equality preserves order, target IDs and every surviving parallel arc. -/
theorem outArcs_exact (g : Digraph) (check : Fin g.vertexCount → Bool)
    (u : Fin g.vertexCount) :
    (build g check).graph.outArcs u =
      (g.outArcs u).filter (fun v => !(check u || check v)) := by
  change (build g check).row u = _
  exact row_exact g check u

theorem arc_subset (g : Digraph) (check : Fin g.vertexCount → Bool)
    {u v : Fin g.vertexCount} (h : (build g check).graph.HasArc u v) :
    g.HasArc u v := by
  change v ∈ (build g check).row u at h
  rw [row_exact] at h
  exact (List.mem_filter.mp h).1

private theorem mapEdges {V : Type} {E E' : V → V → Prop} {F : V → Prop}
    (sub : ∀ {u v : V}, E u v → E' u v)
    {s t : V} (p : AvoidPath E F s t) : AvoidPath E' F s t := by
  induction p with
  | refl a ha => exact AvoidPath.refl a ha
  | step a b c ha arc _ ih => exact AvoidPath.step a b c ha (sub arc) ih

/-- A nonempty directed cycle is an arc followed by a return path. -/
theorem acyclic_inherited (g : Digraph) (check : Fin g.vertexCount → Bool)
    (acyclic : ∀ u v : Fin g.vertexCount, g.HasArc u v →
      ¬ g.SurvivingPath (fun _ => False) v u) :
    ∀ u v : Fin g.vertexCount, (build g check).graph.HasArc u v →
      ¬ (build g check).graph.SurvivingPath (fun _ => False) v u := by
  intro u v arc p
  exact acyclic u v (arc_subset g check arc)
    (mapEdges (fun {_ _} e => arc_subset g check e) p)

/-- A supplied topological ranking also works unchanged. -/
theorem rank_inherited (g : Digraph) (check : Fin g.vertexCount → Bool)
    (rank : Fin g.vertexCount → Nat)
    (rises : ∀ u v, g.HasArc u v → rank u < rank v)
    (u v : Fin g.vertexCount) (arc : (build g check).graph.HasArc u v) :
    rank u < rank v :=
  rises u v (arc_subset g check arc)

private theorem alive_iff {V : Type} {check : V → Bool} {base : V → Prop}
    (refines : ∀ v, check v = true ↔ base v) (v : V) :
    check v = false ↔ ¬ base v := by
  rw [← refines v]
  cases check v <;> simp

theorem arc_iff (g : Digraph) (check : Fin g.vertexCount → Bool)
    {base : Fin g.vertexCount → Prop}
    (refines : ∀ v, check v = true ↔ base v) (u v : Fin g.vertexCount) :
    (build g check).graph.HasArc u v ↔
      g.HasArc u v ∧ ¬ base u ∧ ¬ base v := by
  change (v ∈ (build g check).row u) ↔
    (v ∈ g.outArcs u ∧ ¬ base u ∧ ¬ base v)
  rw [row_exact, List.mem_filter, ← alive_iff refines u, ← alive_iff refines v]
  cases hu : check u <;> cases hv : check v <;> simp [hu, hv]

/-- Filtering arcs isolates deleted IDs. The endpoint tests also exclude
length-zero paths at those IDs. -/
def View.Survives {g : Digraph} (r : View g)
    (failed : Fin g.vertexCount → Prop) (s t : Fin g.vertexCount) : Prop :=
  r.deleted s = false ∧ r.deleted t = false ∧
    AvoidPath r.graph.HasArc failed s t

theorem survives_self {g : Digraph} (r : View g)
    (failed : Fin g.vertexCount → Prop) (s : Fin g.vertexCount) :
    r.Survives failed s s ↔ r.deleted s = false ∧ ¬ failed s := by
  constructor
  · rintro ⟨hs, _, p⟩
    exact ⟨hs, (AvoidPath.endpoints_alive p).1⟩
  · rintro ⟨hs, ha⟩
    exact ⟨hs, hs, AvoidPath.refl s ha⟩

theorem no_survives_deleted_endpoint {g : Digraph} (r : View g)
    (failed : Fin g.vertexCount → Prop) (s t : Fin g.vertexCount)
    (h : r.deleted s = true ∨ r.deleted t = true) :
    ¬ r.Survives failed s t := by
  rintro ⟨hs, ht, _⟩
  rcases h with h | h
  · simp [h] at hs
  · simp [h] at ht

theorem survivingPath_iff (g : Digraph) (check : Fin g.vertexCount → Bool)
    {base : Fin g.vertexCount → Prop}
    (refines : ∀ v, check v = true ↔ base v)
    (failed : Fin g.vertexCount → Prop) (s t : Fin g.vertexCount) :
    (build g check).Survives failed s t ↔
      g.SurvivingPath (fun v => base v ∨ failed v) s t := by
  have project : ∀ {a b : Fin g.vertexCount},
      AvoidPath (build g check).graph.HasArc failed a b → ¬ base b →
      g.SurvivingPath (fun v => base v ∨ failed v) a b := by
    intro a b p
    induction p with
    | refl a ha =>
      intro hb
      exact AvoidPath.refl a (fun h => h.elim hb ha)
    | step a b c ha arc _ ih =>
      intro hc
      obtain ⟨orig, aliveA, _⟩ := (arc_iff g check refines a b).mp arc
      exact AvoidPath.step a b c (fun h => h.elim aliveA ha) orig (ih hc)
  have liftPath : ∀ {a b : Fin g.vertexCount},
      g.SurvivingPath (fun v => base v ∨ failed v) a b →
      AvoidPath (build g check).graph.HasArc failed a b := by
    intro a b p
    change AvoidPath g.HasArc (fun v => base v ∨ failed v) a b at p
    induction p with
    | refl a ha =>
      exact AvoidPath.refl a (fun h => ha (Or.inr h))
    | step a b c ha arc tail ih =>
      have hb := (AvoidPath.endpoints_alive tail).1
      have kept := (arc_iff g check refines a b).mpr
        ⟨arc, fun h => ha (Or.inl h), fun h => hb (Or.inl h)⟩
      exact AvoidPath.step a b c (fun h => ha (Or.inr h)) kept ih
  constructor
  · rintro ⟨_, ht, p⟩
    exact project p ((alive_iff refines t).mp (by simpa only [deleted_build] using ht))
  · intro p
    have ends := AvoidPath.endpoints_alive
      (edge := g.HasArc) (failed := fun v => base v ∨ failed v) p
    refine ⟨?_, ?_, liftPath p⟩
    · rw [deleted_build]
      exact (alive_iff refines s).mpr (fun h => ends.1 (Or.inl h))
    · rw [deleted_build]
      exact (alive_iff refines t).mpr (fun h => ends.2 (Or.inl h))

theorem two_failures_iff (g : Digraph) (check : Fin g.vertexCount → Bool)
    {base : Fin g.vertexCount → Prop}
    (refines : ∀ v, check v = true ↔ base v)
    (s t x y : Fin g.vertexCount) :
    (build g check).Survives (fun v => v = x ∨ v = y) s t ↔
      g.SurvivingPath (fun v => base v ∨ v = x ∨ v = y) s t :=
  survivingPath_iff g check refines (fun v => v = x ∨ v = y) s t

/-- Rewrite only the path test in an existing row interpretation. This also
works for negative tests and rows with multiple original target occurrences. -/
theorem queryRow_iff (g : Digraph) (check : Fin g.vertexCount → Bool)
    {base : Fin g.vertexCount → Prop}
    (refines : ∀ v, check v = true ↔ base v)
    (fail₁ fail₂ : Fin g.vertexCount → Prop)
    (rowSem : (Fin g.vertexCount → Fin g.vertexCount → Prop) → Prop) :
    rowSem ((build g check).Survives (fun v => fail₁ v ∨ fail₂ v)) ↔
      rowSem (g.SurvivingPath (fun v => base v ∨ fail₁ v ∨ fail₂ v)) := by
  have paths :
      (build g check).Survives (fun v => fail₁ v ∨ fail₂ v) =
        g.SurvivingPath (fun v => base v ∨ fail₁ v ∨ fail₂ v) :=
    funext fun s => funext fun t =>
      propext (survivingPath_iff g check refines (fun v => fail₁ v ∨ fail₂ v) s t)
  rw [paths]

end PaperB.EX62.SharedResidual
