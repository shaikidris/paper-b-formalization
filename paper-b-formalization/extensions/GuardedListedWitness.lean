set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.EX62.ListedWitness

/-- EX55 slots, interpreted as additional failures, not baseline deletions. -/
def slotFails {V : Type} (f : EX55.FailureSlots V) (v : V) : Prop :=
  f.first = some v ∨ f.second = some v

def slotsOf {V : Type} : List V → EX55.FailureSlots V
  | [] => ⟨none, none⟩
  | a :: [] => ⟨some a, none⟩
  | a :: b :: _ => ⟨some a, some b⟩

theorem slotsOf_exact {V : Type} (gs : List V) (h : gs.length ≤ 2) (v : V) :
    slotFails (slotsOf gs) v ↔ v ∈ gs := by
  cases gs with
  | nil => simp [slotsOf, slotFails]
  | cons a gs =>
    cases gs with
    | nil => simp [slotsOf, slotFails, eq_comm]
    | cons b gs =>
      cases gs with
      | nil => simp [slotsOf, slotFails, eq_comm]
      | cons c gs =>
        simp only [List.length_cons] at h
        omega

/-- Use the row's entire target list, without filtering or deduplicating it. -/
def jobOf {V : Type} (b : Bucket V) : EX55.Job V :=
  ⟨slotsOf b.guards, b.targets⟩

def jobsOf {L V : Type} (rs : List (L × Bucket V)) : List (EX55.Job V) :=
  rs.map fun e => jobOf e.2

/-- Supply one oracle for this particular residual view and source. The
contract includes the view's deleted-endpoint checks, even for a zero-edge path. -/
structure ResidualOracle {g : _} (r : SharedResidual.View g)
    (source : Fin g.vertexCount) where
  single : EX55.Oracle (Fin g.vertexCount)
  exactSingle : EX55.OracleCorrect single
    (fun f v => r.Survives (slotFails f) source v)

def firstPositive {A L : Type} (label : A → L) :
    List A → List Bool → Option L
  | a :: rs, b :: bs =>
      if b = true then some (label a) else firstPositive label rs bs
  | _, _ => none

structure Result (k : Nat) (V : Type) where
  jobs : List (EX55.Job V)
  batch : EX55.BatchRun
  first : Option (Fin k)

def Result.detectingSet {k : Nat} {V : Type} (z : Result k V)
    (Q : Fin k → Prop) : Option (Fin k → Prop) :=
  z.first.map fun i j => Q j ∨ j = i

variable {k : Nat} {g : _} {d : _} {Q : Fin k → Prop}
  (x : Input (g := g) d Q)

/-- Build once, then supply an oracle indexed by this view. -/
def prepare (check : Fin g.vertexCount → Bool) : SharedResidual.View g :=
  SharedResidual.build g check

def jobs : List (EX55.Job (Fin g.vertexCount)) :=
  jobsOf (rows x.result.1)

/-- `prepare check` is the caller's shared residual instance. `run` does not
build a graph or an oracle: it materializes the jobs and calls EX55 once.
The final pass reads only the returned Boolean cells and row labels. -/
def run (check : Fin g.vertexCount → Bool)
    (o : ResidualOracle (prepare check) d.root) : Result k (Fin g.vertexCount) :=
  let rs := rows x.result.1
  let js := jobsOf rs
  let br := EX55.runBatch o.single js
  ⟨js, br, firstPositive Prod.fst rs br.answers⟩

private def hit {L V : Type} (o : EX55.Oracle V) (e : L × Bucket V) : Bool :=
  (EX55.runList o (jobOf e.2).failures (jobOf e.2).targets).answer

section Correctness

variable (check : Fin g.vertexCount → Bool)
  (refines : ∀ v, check v = true ↔ d.GuardFailed Q v)
  (o : ResidualOracle (prepare check) d.root)

theorem row_job_exact {e : Fin k × Bucket (Fin g.vertexCount)}
    (he : e ∈ rows x.result.1) :
    e.2.guards.length ≤ 2 ∧
    (∀ v, slotFails (jobOf e.2).failures v ↔ d.RemainingFailed Q e.1 v) ∧
    (jobOf e.2).targets = e.2.targets ∧
    (∀ v, v ∈ (jobOf e.2).targets ↔ d.gate v = .terminal e.1) := by
  obtain ⟨_, hw, hg, _, _, ht⟩ := x.row_exact e.1 e.2 he
  exact ⟨hw, fun v => (slotsOf_exact e.2.guards hw v).trans (hg v), rfl, ht⟩

include refines in
private theorem row_hit_iff {e : Fin k × Bucket (Fin g.vertexCount)}
    (he : e ∈ rows x.result.1) :
    hit o.single e = true ↔ d.ResidualQuery Q e.1 := by
  obtain ⟨_, hf, _, ht⟩ := row_job_exact x he
  have hF : slotFails (jobOf e.2).failures = d.RemainingFailed Q e.1 :=
    funext fun v => propext (hf v)
  change (EX55.runList o.single (jobOf e.2).failures
    (jobOf e.2).targets).answer = true ↔ _
  rw [EX55.runList_correct o.single _ o.exactSingle, hF]
  constructor
  · rintro ⟨v, hv, hp⟩
    exact ⟨v, (ht v).mp hv,
      (SharedResidual.survivingPath_iff g check refines
        (d.RemainingFailed Q e.1) d.root v).mp hp⟩
  · rintro ⟨v, hv, hp⟩
    exact ⟨v, (ht v).mpr hv,
      (SharedResidual.survivingPath_iff g check refines
        (d.RemainingFailed Q e.1) d.root v).mpr hp⟩

include refines in
theorem answer_at (p : Nat) {e : Fin k × Bucket (Fin g.vertexCount)}
    (he : (rows x.result.1)[p]? = some e) :
    (run x check o).batch.answers[p]? = some true ↔ d.ResidualQuery Q e.1 := by
  have hm : e ∈ rows x.result.1 := List.mem_of_getElem? he
  have hj : (jobs x)[p]? = some (jobOf e.2) := by
    simp [jobs, jobsOf, List.getElem?_map, he]
  change (EX55.runBatch o.single (jobs x)).answers[p]? = some true ↔ _
  rw [EX55.runBatch_answers, List.getElem?_map, hj]
  simpa [hit] using row_hit_iff x check refines o hm

private theorem run_first_eq :
    (run x check o).first =
      firstPositive Prod.fst (rows x.result.1)
        ((rows x.result.1).map (hit o.single)) := by
  change firstPositive Prod.fst (rows x.result.1)
    (EX55.runBatch o.single (jobs x)).answers = _
  simp only [EX55.runBatch_answers, jobs, jobsOf, List.map_map,
    Function.comp_def]
  rfl

private theorem firstPositive_prefix {A L : Type} (label : A → L)
    (test : A → Bool) (rs : List A) {i : L} :
    firstPositive label rs (rs.map test) = some i →
    ∃ pre e post, rs = pre ++ e :: post ∧ label e = i ∧
      test e = true ∧ ∀ a ∈ pre, test a = false := by
  induction rs with
  | nil => simp [firstPositive]
  | cons a rs ih =>
    intro h
    cases ha : test a with
    | true =>
      have hi : label a = i := by simpa [firstPositive, ha] using h
      exact ⟨[], a, rs, rfl, hi, ha, by simp⟩
    | false =>
      have htail : firstPositive label rs (rs.map test) = some i := by
        simpa [firstPositive, ha] using h
      obtain ⟨pre, e, post, hr, hi, ht, hn⟩ := ih htail
      refine ⟨a :: pre, e, post, congrArg (List.cons a) hr, hi, ht, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · subst b
        exact ha
      · exact hn b hb

private theorem firstPositive_none_iff {A L : Type} (label : A → L)
    (test : A → Bool) (rs : List A) :
    firstPositive label rs (rs.map test) = none ↔
      ∀ a ∈ rs, test a = false := by
  induction rs with
  | nil => simp [firstPositive]
  | cons a rs ih =>
    cases ha : test a with
    | true =>
      constructor
      · simp [firstPositive, ha]
      · intro h
        have hf := h a (by simp)
        simp [ha] at hf
    | false =>
      have he : firstPositive label (a :: rs) ((a :: rs).map test) =
          firstPositive label rs (rs.map test) := by
        simp [firstPositive, ha]
      rw [he, ih]
      constructor
      · intro h b hb
        rcases List.mem_cons.mp hb with hba | hb
        · subst b
          exact ha
        · exact h b hb
      · intro h b hb
        exact h b (List.mem_cons.mpr (Or.inr hb))

include refines in
/-- The returned label is the label of the first positive row, not merely
the label of some positive query. -/
theorem first_spec {i : Fin k} (h : (run x check o).first = some i) :
    ∃ pre e post, rows x.result.1 = pre ++ e :: post ∧ e.1 = i ∧
      d.ResidualQuery Q i ∧ ∀ a ∈ pre, ¬ d.ResidualQuery Q a.1 := by
  rw [run_first_eq x check o] at h
  obtain ⟨pre, e, post, hr, hi, ht, hn⟩ :=
    firstPositive_prefix Prod.fst (hit o.single) (rows x.result.1) h
  have he : e ∈ rows x.result.1 := by
    rw [hr]
    exact List.mem_append.mpr (Or.inr (by simp))
  refine ⟨pre, e, post, hr, hi, ?_, ?_⟩
  · rw [← hi]
    exact (row_hit_iff x check refines o he).mp ht
  · intro a ha hq
    have hm : a ∈ rows x.result.1 := by
      rw [hr]
      exact List.mem_append.mpr (Or.inl ha)
    have hh := (row_hit_iff x check refines o hm).mpr hq
    simp [hn a ha] at hh

include refines in
theorem none_iff_no_query :
    (run x check o).first = none ↔ ∀ i, ¬ d.ResidualQuery Q i := by
  rw [run_first_eq x check o, firstPositive_none_iff]
  constructor
  · intro hn i hq
    have he : (i, x.bucket i) ∈ rows x.result.1 :=
      (mem_rows _ _ _).mpr rfl
    have ht := (row_hit_iff x check refines o he).mpr hq
    simp [hn _ he] at ht
  · intro hn e he
    cases hh : hit o.single e with
    | false => rfl
    | true => exact (hn e.1 ((row_hit_iff x check refines o he).mp hh)).elim

include refines in
/-- The first conjunct is `Admissible Q K`, written out. The returned set
is `withCandidate Q i`; no test that `i ∉ Q` is made. -/
theorem witness {t₀ i : Fin k} (healthy : d.HealthyZero t₀)
    (h : (run x check o).first = some i) :
    let K : Fin k → Prop := fun j => Q j ∨ j = i
    ((∃ j, K j) ∧ (∀ j, Q j → K j)) ∧
      ¬ (d.TrueAt K d.root ↔ d.TrueAt (fun j => j = t₀) d.root) := by
  obtain ⟨_, _, _, _, _, hq, _⟩ := first_spec x check refines o h
  exact ⟨⟨⟨i, Or.inr rfl⟩, fun _ hj => Or.inl hj⟩,
    (d.detects_iff_true healthy _).mpr (d.candidate_true_of_query hq)⟩

include refines in
/-- Completeness uses the existing semantic witness theorem to reduce an
arbitrary admissible detecting set to a positive residual query. -/
theorem none_iff_no_detection {t₀ : Fin k} (healthy : d.HealthyZero t₀) :
    (run x check o).first = none ↔
      ¬ ∃ K : Fin k → Prop, ((∃ j, K j) ∧ (∀ j, Q j → K j)) ∧
        ¬ (d.TrueAt K d.root ↔ d.TrueAt (fun j => j = t₀) d.root) := by
  constructor
  · intro hn hd
    obtain ⟨i, _, hq⟩ :=
      (d.exists_detecting_iff_residualQuery healthy Q).mp hd
    exact (none_iff_no_query x check refines o).mp hn i hq
  · intro hn
    apply (none_iff_no_query x check refines o).mpr
    intro i hq
    apply hn
    refine ⟨fun j => Q j ∨ j = i, ⟨⟨i, Or.inr rfl⟩, fun _ hj => Or.inl hj⟩, ?_⟩
    exact (d.detects_iff_true healthy _).mpr (d.candidate_true_of_query hq)

include refines in
/-- The actual optional set returned by the binder. `none` rules out every
admissible detecting set; `some K` gives an admissible detecting set. -/
theorem detectingSet_spec {t₀ : Fin k} (healthy : d.HealthyZero t₀) :
    match (run x check o).detectingSet Q with
    | none =>
        ¬ ∃ K : Fin k → Prop, ((∃ j, K j) ∧ (∀ j, Q j → K j)) ∧
          ¬ (d.TrueAt K d.root ↔ d.TrueAt (fun j => j = t₀) d.root)
    | some K =>
        ((∃ j, K j) ∧ (∀ j, Q j → K j)) ∧
          ¬ (d.TrueAt K d.root ↔ d.TrueAt (fun j => j = t₀) d.root) := by
  cases h : (run x check o).first with
  | none =>
    simpa [Result.detectingSet, h] using
      (none_iff_no_detection x check refines o healthy).mp h
  | some i =>
    simpa [Result.detectingSet, h] using witness x check refines o healthy h

include refines in
/-- No special early-exit assumption is needed for a deleted source. -/
theorem none_of_root_deleted (hdel : d.GuardFailed Q d.root) :
    (run x check o).first = none := by
  apply (none_iff_no_query x check refines o).mpr
  intro i hq
  exact (d.no_detection_of_root_deleted (K := fun j => Q j ∨ j = i)
    ⟨⟨i, Or.inr rfl⟩, fun _ hj => Or.inl hj⟩ hdel)
    (d.candidate_true_of_query hq)

/-- A positive row whose label is already prescribed returns `Q` itself. -/
theorem detectingSet_eq_base {i : Fin k} (hi : Q i)
    (h : (run x check o).first = some i) :
    (run x check o).detectingSet Q = some Q := by
  have he : (fun j => Q j ∨ j = i) = Q := by
    funext j
    apply propext
    constructor
    · rintro (hj | hj)
      · exact hj
      · subst j
        exact hi
    · exact Or.inl
  simp [Result.detectingSet, h, he]

end Correctness

theorem prepare_acyclic (check : Fin g.vertexCount → Bool)
    (h : ∀ u v : Fin g.vertexCount, g.HasArc u v →
      ¬ g.SurvivingPath (fun _ => False) v u) :
    ∀ u v : Fin g.vertexCount, (prepare check).graph.HasArc u v →
      ¬ (prepare check).graph.SurvivingPath (fun _ => False) v u :=
  SharedResidual.acyclic_inherited g check h

/- Resource accounting. `n,m` measure the shared residual graph (including
its isolated IDs); `q,M` measure the actual jobs. The EX55 operation budget
is for index construction plus the batch, not for residual filtering,
grouping, or the final Boolean/label pass. That pass makes no oracle calls. -/

def n (r : SharedResidual.View g) : Nat :=
  r.graph.vertexCount

def m (r : SharedResidual.View g) : Nat :=
  sumOn (labels r.graph.vertexCount) (fun v => (r.graph.outArcs v).length)

def q : Nat := (jobs x).length

def M : Nat := EX55.targetCount (jobs x)

private theorem targets_jobsOf {L V : Type} (rs : List (L × Bucket V)) :
    EX55.targetCount (jobsOf rs) = sumOn rs (fun e => e.2.targets.length) := by
  induction rs with
  | nil => rfl
  | cons e rs ih =>
    change e.2.targets.length + EX55.targetCount (jobsOf rs) =
      sumOn (e :: rs) (fun a => a.2.targets.length)
    rw [ih]
    simp [sumOn]

theorem incidence_totals :
    q x = k ∧ M x = x.terminals.length ∧
    sumOn (rows x.result.1) (fun e => e.2.guards.length) ≤ x.remaining.length ∧
    sumOn (rows x.result.1) (fun e => e.2.guards.length) ≤ 2 * q x ∧
    q x + sumOn (rows x.result.1) (fun e => e.2.guards.length) + M x ≤
      k + min x.remaining.length (2 * k) + x.terminals.length := by
  have hrows : q x = (rows x.result.1).length := by
    simp [q, jobs, jobsOf]
  have hq : q x = k := by rw [hrows, rows_length]
  have hM : M x = sumOn (rows x.result.1) (fun e => e.2.targets.length) :=
    targets_jobsOf _
  refine ⟨hq, hM.trans x.total_targets, x.total_guards_raw, ?_, ?_⟩
  · rw [hq]
    exact x.total_guards_width
  · rw [hrows, hM]
    exact x.total_list_size

section Resources

variable (check : Fin g.vertexCount → Bool)
  (o : ResidualOracle (prepare check) d.root)

theorem batch_mixed (Cq L : Nat)
    (hQ : EX55.OracleBound o.single (Cq * L)) :
    (run x check o).batch.scans ≤ M x ∧
    (run x check o).batch.oracleOps ≤ Cq * M x * L ∧
    (run x check o).batch.writes = q x :=
  EX55.runBatch_mixed_bounds o.single Cq L hQ (jobs x)

theorem operations_mixed (buildOps Cb Cq L : Nat) (hL : 1 ≤ L)
    (hBuild : buildOps ≤ Cb * (n (prepare check) + m (prepare check)) * L ^ 2)
    (hQ : EX55.OracleBound o.single (Cq * L)) :
    EX55.totalOperations buildOps (run x check o).batch ≤
      (Cb * (n (prepare check) + m (prepare check)) * L ^ 2 + 1) +
        3 * q x + (3 + Cq) * M x * L :=
  EX55.totalOperations_mixed o.single (n (prepare check)) (m (prepare check))
    buildOps Cb Cq L (jobs x) hL hBuild hQ

theorem words_mixed (A Cbuild Cret Cscratch buildPeak retained queryExtra : Nat)
    (hS : 0 < n (prepare check) + m (prepare check) + q x + M x)
    (hBuild : buildPeak ≤ Cbuild * (n (prepare check) + m (prepare check)))
    (hRetained : retained ≤ Cret * (n (prepare check) + m (prepare check)))
    (hScratch : queryExtra ≤ Cscratch * (n (prepare check) + m (prepare check))) :
    EX55.wordBudget A buildPeak retained queryExtra (q x) (M x) ≤
      (2 * A + (Cbuild + Cret + Cscratch)) *
        (n (prepare check) + m (prepare check) + q x + M x) :=
  EX55.wordBudget_mixed_le (n (prepare check)) (m (prepare check))
    A Cbuild Cret Cscratch buildPeak retained queryExtra (jobs x)
    hS hBuild hRetained hScratch

end Resources
end PaperB.EX62.ListedWitness
