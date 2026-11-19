import Lean

namespace PaperB.EX55

universe u

/-- Each occupied slot denotes one failed vertex. The two slots may coincide. -/
structure FailureSlots (V : Type u) where
  first  : Option V
  second : Option V

structure Job (V : Type u) where
  failures : FailureSlots V
  targets  : List V

structure QueryObservation where
  answer     : Bool
  operations : Nat
  deriving Repr

/-- The caller supplies a single-target query function for an already built index. -/
abbrev Oracle (V : Type u) :=
  FailureSlots V → V → QueryObservation

variable {V : Type u}

def OracleCorrect (oracle : Oracle V)
    (survives : FailureSlots V → V → Prop) : Prop :=
  ∀ f v, (oracle f v).answer = true ↔ survives f v

def OracleBound (oracle : Oracle V) (Q : Nat) : Prop :=
  ∀ f v, (oracle f v).operations ≤ Q

structure ListRun where
  answer    : Bool
  scans     : Nat
  oracleOps : Nat
  deriving Repr

/--
The online entry point. It needs only the fixed oracle and the current job.
Each occurrence examined causes exactly one oracle call. A true answer stops
the scan; an empty list causes no call and returns false.
-/
def runList (oracle : Oracle V) (f : FailureSlots V) :
    List V → ListRun
  | [] => ⟨false, 0, 0⟩
  | v :: vs =>
      let hit := oracle f v
      if hit.answer = true then
        ⟨true, 1, hit.operations⟩
      else
        let rest := runList oracle f vs
        ⟨rest.answer, 1 + rest.scans, hit.operations + rest.oracleOps⟩

@[simp] theorem runList_nil (oracle : Oracle V) (f : FailureSlots V) :
    runList oracle f [] = ⟨false, 0, 0⟩ := rfl

structure BatchRun where
  answers   : List Bool
  scans     : Nat
  oracleOps : Nat
  writes    : Nat
  deriving Repr

/--
Collect the online answers in input order. Each job gets one output cell,
including jobs with no targets. Neither jobs nor targets are deduplicated.
-/
def runBatch (oracle : Oracle V) : List (Job V) → BatchRun
  | [] => ⟨[], 0, 0, 0⟩
  | j :: js =>
      let head := runList oracle j.failures j.targets
      let rest := runBatch oracle js
      ⟨head.answer :: rest.answers, head.scans + rest.scans,
        head.oracleOps + rest.oracleOps, rest.writes + 1⟩

def targetCount : List (Job V) → Nat
  | [] => 0
  | j :: js => j.targets.length + targetCount js

/-- Explicit input size `S = n + m + q + M`. -/
def inputSize (n m : Nat) (jobs : List (Job V)) : Nat :=
  n + m + jobs.length + targetCount jobs

theorem runList_correct (oracle : Oracle V)
    (survives : FailureSlots V → V → Prop)
    (hcorrect : OracleCorrect oracle survives)
    (f : FailureSlots V) (ts : List V) :
    (runList oracle f ts).answer = true ↔ ∃ v ∈ ts, survives f v := by
  induction ts with
  | nil => simp [runList]
  | cons v vs ih =>
    cases h : (oracle f v).answer with
    | false =>
      have hn : ¬ survives f v := by
        intro hv
        have hh := (hcorrect f v).2 hv
        simp [h] at hh
      have htail :
          (runList oracle f (v :: vs)).answer = (runList oracle f vs).answer := by
        simp [runList, h]
      rw [htail, ih]
      constructor
      · rintro ⟨w, hw, hs⟩
        exact ⟨w, List.mem_cons.mpr (Or.inr hw), hs⟩
      · rintro ⟨w, hw, hs⟩
        rcases List.mem_cons.mp hw with he | hm
        · subst w
          exact (hn hs).elim
        · exact ⟨w, hm, hs⟩
    | true =>
      have hv := (hcorrect f v).1 h
      constructor
      · intro _
        exact ⟨v, by simp, hv⟩
      · intro _
        simp [runList, h]

theorem runBatch_answers (oracle : Oracle V) (jobs : List (Job V)) :
    (runBatch oracle jobs).answers =
      jobs.map (fun j => (runList oracle j.failures j.targets).answer) := by
  induction jobs with
  | nil => rfl
  | cons j js ih => simp [runBatch, ih]

theorem runBatch_answer_count (oracle : Oracle V) (jobs : List (Job V)) :
    (runBatch oracle jobs).answers.length = jobs.length := by
  simp [runBatch_answers]

theorem runBatch_correctAt (oracle : Oracle V)
    (survives : FailureSlots V → V → Prop)
    (hcorrect : OracleCorrect oracle survives)
    (jobs : List (Job V)) (i : Nat) (j : Job V) (hj : jobs[i]? = some j) :
    (runBatch oracle jobs).answers[i]? = some true ↔
      ∃ v ∈ j.targets, survives j.failures v := by
  rw [runBatch_answers, List.getElem?_map, hj]
  simpa using (runList_correct oracle survives hcorrect j.failures j.targets)

theorem runList_bounds (oracle : Oracle V) (Q : Nat)
    (hQ : OracleBound oracle Q) (f : FailureSlots V) (ts : List V) :
    (runList oracle f ts).scans ≤ ts.length ∧
      (runList oracle f ts).oracleOps ≤ (runList oracle f ts).scans * Q := by
  induction ts with
  | nil => simp [runList]
  | cons v vs ih =>
    cases h : (oracle f v).answer with
    | false =>
      have hs : 1 + (runList oracle f vs).scans ≤ vs.length + 1 := by
        have htail := ih.1
        omega
      have ho :
          (oracle f v).operations + (runList oracle f vs).oracleOps ≤
            Q + (runList oracle f vs).scans * Q :=
        Nat.add_le_add (hQ f v) ih.2
      simpa [runList, h, Nat.add_mul] using (And.intro hs ho)
    | true =>
      have hs : 1 ≤ vs.length + 1 := by omega
      simpa [runList, h] using (And.intro hs (hQ f v))

theorem runBatch_bounds (oracle : Oracle V) (Q : Nat)
    (hQ : OracleBound oracle Q) (jobs : List (Job V)) :
    (runBatch oracle jobs).scans ≤ targetCount jobs ∧
      (runBatch oracle jobs).oracleOps ≤ (runBatch oracle jobs).scans * Q := by
  induction jobs with
  | nil => simp [runBatch, targetCount]
  | cons j js ih =>
    have hhead := runList_bounds oracle Q hQ j.failures j.targets
    constructor
    · simpa [runBatch, targetCount] using (Nat.add_le_add hhead.1 ih.1)
    · simpa [runBatch, Nat.add_mul] using (Nat.add_le_add hhead.2 ih.2)

theorem runBatch_writes (oracle : Oracle V) (jobs : List (Job V)) :
    (runBatch oracle jobs).writes = jobs.length := by
  induction jobs with
  | nil => rfl
  | cons j js ih => simp [runBatch, ih]

/-
Logical charge convention:
* One unit to start a list; three per occurrence examined (scan, dispatch,
  and answer handling), plus the operations reported by that oracle call.
* One unit to start a batch; three per job (fetch, start its list, and write
  its answer), plus the occurrence and oracle charges above.

These are logical accounting functions, not counts of Lean runtime steps.
-/

def listOperations (r : ListRun) : Nat :=
  1 + 3 * r.scans + r.oracleOps

def batchOperations (r : BatchRun) : Nat :=
  1 + 3 * r.writes + 3 * r.scans + r.oracleOps

def totalOperations (buildOps : Nat) (r : BatchRun) : Nat :=
  buildOps + batchOperations r

def batchBudget (B Q q M : Nat) : Nat :=
  B + 1 + 3 * q + M * (3 + Q)

theorem runList_operations_le (oracle : Oracle V) (Q : Nat)
    (hQ : OracleBound oracle Q) (f : FailureSlots V) (ts : List V) :
    listOperations (runList oracle f ts) ≤ 1 + ts.length * (3 + Q) := by
  have h := runList_bounds oracle Q hQ f ts
  have hs := Nat.mul_le_mul_left 3 h.1
  have ho := Nat.le_trans h.2 (Nat.mul_le_mul_right Q h.1)
  rw [listOperations, Nat.mul_add, Nat.mul_comm ts.length 3]
  omega

/-- Transfer supplied build and per-query bounds without choosing exponents. -/
theorem totalOperations_le (oracle : Oracle V) (buildOps B Q : Nat)
    (hBuild : buildOps ≤ B) (hQ : OracleBound oracle Q)
    (jobs : List (Job V)) :
    totalOperations buildOps (runBatch oracle jobs) ≤
      batchBudget B Q jobs.length (targetCount jobs) := by
  have h := runBatch_bounds oracle Q hQ jobs
  have hs := Nat.mul_le_mul_left 3 h.1
  have ho := Nat.le_trans h.2 (Nat.mul_le_mul_right Q h.1)
  rw [totalOperations, batchOperations, batchBudget, runBatch_writes,
    Nat.mul_add, Nat.mul_comm (targetCount jobs) 3]
  omega

private theorem overhead_le (c d K : Nat) (hK : 1 ≤ K) :
    d + c * K ≤ (d + c) * K := by
  have hd := Nat.mul_le_mul_left d hK
  rw [Nat.mul_one] at hd
  rw [Nat.add_mul]
  exact Nat.add_le_add_right hd (c * K)

private theorem one_le_cube (L : Nat) (hL : 1 ≤ L) : 1 ≤ L ^ 3 := by
  have h0 : 1 ≤ L ^ 0 := by simp
  have step (i : Nat) (hi : 1 ≤ L ^ i) : 1 ≤ L ^ (i + 1) := by
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul_right L hi
    rw [Nat.one_mul] at h
    exact Nat.le_trans hL h
  exact step 2 (step 1 (step 0 h0))

/-- A later list uses the existing oracle and incurs no construction charge. -/
theorem laterList_scaled (oracle : Oracle V) (C K : Nat) (hK : 1 ≤ K)
    (hQ : OracleBound oracle (C * K)) (f : FailureSlots V) (ts : List V) :
    listOperations (runList oracle f ts) ≤
      (1 + ts.length) * ((3 + C) * K) := by
  have hu := overhead_le C 3 K hK
  have hstart : 1 ≤ (3 + C) * K := by omega
  calc
    _ ≤ 1 + ts.length * (3 + C * K) :=
      runList_operations_le oracle (C * K) hQ f ts
    _ ≤ (1 + ts.length) * ((3 + C) * K) := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add hstart (Nat.mul_le_mul_left ts.length hu)

theorem laterList_cubic (oracle : Oracle V) (C L : Nat) (hL : 1 ≤ L)
    (hQ : OracleBound oracle (C * L ^ 3)) (f : FailureSlots V) (ts : List V) :
    listOperations (runList oracle f ts) ≤
      (1 + ts.length) * ((3 + C) * L ^ 3) :=
  laterList_scaled oracle C (L ^ 3) (one_le_cube L hL) hQ f ts

/-- The positivity hypothesis absorbs the one batch-start charge into `S`. -/
theorem batchBudget_scaled (n m q M Cb Cq K : Nat) (hK : 1 ≤ K)
    (hS : 0 < n + m + q + M) :
    batchBudget ((n + m) * (Cb * K)) (Cq * K) q M ≤
      (n + m + q + M) * ((4 + Cb + Cq) * K) := by
  let D := (3 + Cb + Cq) * K
  have hcB : Cb ≤ 3 + Cb + Cq := by omega
  have hcQ : 3 + Cq ≤ 3 + Cb + Cq := by omega
  have hc3 : 3 ≤ 3 + Cb + Cq := by omega
  have hc4 : 1 + (3 + Cb + Cq) ≤ 4 + Cb + Cq := by omega
  have hb : Cb * K ≤ D := Nat.mul_le_mul_right K hcB
  have hq : 3 ≤ D := by
    have h := Nat.mul_le_mul_left 3 hK
    rw [Nat.mul_one] at h
    exact Nat.le_trans h (Nat.mul_le_mul_right K hc3)
  have hm : 3 + Cq * K ≤ D :=
    Nat.le_trans (overhead_le Cq 3 K hK) (Nat.mul_le_mul_right K hcQ)
  have hstep : 1 + D ≤ (4 + Cb + Cq) * K :=
    Nat.le_trans (overhead_le (3 + Cb + Cq) 1 K hK)
      (Nat.mul_le_mul_right K hc4)
  calc
    _ ≤ 1 + ((n + m) * D + q * D + M * D) := by
      have hb' := Nat.mul_le_mul_left (n + m) hb
      have hq' := Nat.mul_le_mul_left q hq
      have hm' := Nat.mul_le_mul_left M hm
      rw [batchBudget, Nat.mul_comm 3 q]
      omega
    _ = 1 + (n + m + q + M) * D := by simp only [Nat.add_mul]
    _ ≤ (n + m + q + M) * (1 + D) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ _ := Nat.mul_le_mul_left (n + m + q + M) hstep

/--
With the supplied cubic bounds, total charged operations are at most
`S * ((4 + Cb + Cq) * L^3)`, including one construction.
For a graph with a root, `S > 0` even if there are no jobs.
-/
theorem totalOperations_cubic (oracle : Oracle V)
    (n m buildOps Cb Cq L : Nat) (jobs : List (Job V))
    (hL : 1 ≤ L) (hS : 0 < inputSize n m jobs)
    (hBuild : buildOps ≤ (n + m) * (Cb * L ^ 3))
    (hQ : OracleBound oracle (Cq * L ^ 3)) :
    totalOperations buildOps (runBatch oracle jobs) ≤
      inputSize n m jobs * ((4 + Cb + Cq) * L ^ 3) := by
  exact Nat.le_trans
    (totalOperations_le oracle buildOps ((n + m) * (Cb * L ^ 3))
      (Cq * L ^ 3) hBuild hQ jobs)
    (batchBudget_scaled n m jobs.length (targetCount jobs) Cb Cq
      (L ^ 3) (one_le_cube L hL) hS)

/--
Conservative word-budget transfer, separate from the logical counters.
A word-machine implementation supplies `A` for resident job/target cells,
output cells, and constant-size frames: there are at most `q` batch frames
and at most `M` list frames. `buildPeak` includes the construction footprint;
`retained` includes the index and any other retained graph storage, and
`queryExtra` is scratch for one oracle call. The sum below is safe even
though construction and query scratch need not coexist.
-/
def wordBudget (A buildPeak retained queryExtra q M : Nat) : Nat :=
  A * (1 + q + M) + (buildPeak + retained + queryExtra)

theorem wordBudget_le (n m q M A C buildPeak retained queryExtra : Nat)
    (hS : 0 < n + m + q + M)
    (hOracle : buildPeak + retained + queryExtra ≤ C * (n + m)) :
    wordBudget A buildPeak retained queryExtra q M ≤
      (2 * A + C) * (n + m + q + M) := by
  let S := n + m + q + M
  have hw : 1 + q + M ≤ 2 * S := by dsimp [S]; omega
  have hn : n + m ≤ S := by dsimp [S]; omega
  have ho := Nat.le_trans hOracle (Nat.mul_le_mul_left C hn)
  calc
    _ ≤ A * (2 * S) + C * S :=
      Nat.add_le_add (Nat.mul_le_mul_left A hw) ho
    _ = _ := by
      change A * (2 * S) + C * S = (2 * A + C) * S
      rw [Nat.add_mul, Nat.mul_comm 2 A, Nat.mul_assoc]

end PaperB.EX55
