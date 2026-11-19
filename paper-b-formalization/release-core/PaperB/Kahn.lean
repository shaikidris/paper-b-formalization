import PaperB.Indegrees

namespace PaperB
namespace Kahn

open Digraph (indegreeScan indegrees_size)

/-- Executable scan state. The two size invariants are erased at runtime. -/
structure State (n : Nat) where
  remaining : Array Nat
  queue : Array (Fin n)
  head : Nat
  edgeVisits : Nat
  remaining_size : remaining.size = n
  head_le_queue : head ≤ queue.size

def State.degree {n : Nat} (s : State n) (v : Fin n) : Nat :=
  s.remaining[v.val]'(by rw [s.remaining_size]; exact v.isLt)

/-- Visit one arc occurrence. The old degree, not the new degree, gates
    enqueueing. Subtraction is on `Nat`; positivity is not proved here. -/
def visit {n : Nat} (s : State n) (v : Fin n) : State n :=
  let d := s.degree v
  { s with
    remaining := s.remaining.setIfInBounds v.val (d - 1)
    queue := if d = 1 then s.queue.push v else s.queue
    edgeVisits := s.edgeVisits + 1
    remaining_size := by simpa using s.remaining_size
    head_le_queue := by
      change s.head ≤ (if s.degree v = 1 then s.queue.push v else s.queue).size
      by_cases h : s.degree v = 1
      · simpa only [ite_eq_left h, Array.size_push] using
          Nat.le_trans s.head_le_queue (Nat.le_succ s.queue.size)
      · simpa only [ite_eq_right h] using s.head_le_queue }

theorem visit_queue_size {n : Nat} (s : State n) (v : Fin n) :
    (visit s v).queue.size =
      s.queue.size + (if s.degree v = 1 then 1 else 0) := by
  by_cases h : s.degree v = 1 <;> simp [visit, h]

/-- Consume the concrete row in list order, including all repeated entries. -/
def visitRow {n : Nat} : List (Fin n) → State n → State n
  | [], s => s
  | v :: vs, s => visitRow vs (visit s v)

theorem visitRow_spec {n : Nat} (row : List (Fin n)) (s : State n) :
    (visitRow row s).remaining.size = n ∧
    (visitRow row s).head = s.head ∧
    (visitRow row s).edgeVisits = s.edgeVisits + row.length ∧
    s.queue.size ≤ (visitRow row s).queue.size ∧
    (visitRow row s).queue.size ≤ s.queue.size + row.length := by
  induction row generalizing s with
  | nil =>
      exact ⟨s.remaining_size, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | cons v vs ih =>
      have hr := ih (visit s v)
      have hh : (visit s v).head = s.head := rfl
      have he : (visit s v).edgeVisits = s.edgeVisits + 1 := rfl
      have hlo : s.queue.size ≤ (visit s v).queue.size := by
        by_cases h : s.degree v = 1
        · simpa only [visit_queue_size, ite_eq_left h] using Nat.le_succ s.queue.size
        · simpa only [visit_queue_size, ite_eq_right h, Nat.add_zero] using
            Nat.le_refl s.queue.size
      have hhi : (visit s v).queue.size ≤ s.queue.size + 1 := by
        by_cases h : s.degree v = 1
        · simpa only [visit_queue_size, ite_eq_left h] using
            Nat.le_refl (s.queue.size + 1)
        · simpa only [visit_queue_size, ite_eq_right h, Nat.add_zero] using
            Nat.le_succ s.queue.size
      simp only [visitRow, List.length_cons]
      refine ⟨hr.1, hr.2.1.trans hh, ?_, Nat.le_trans hlo hr.2.2.2.1, ?_⟩
      · rw [hr.2.2.1, he]
        simp only [Nat.add_comm, Nat.add_left_comm]
      · calc
          _ ≤ (visit s v).queue.size + vs.length := hr.2.2.2.2
          _ ≤ (s.queue.size + 1) + vs.length := Nat.add_le_add_right hhi _
          _ = _ := by simp only [Nat.add_comm, Nat.add_left_comm]

/-- Process the row of the next queued vertex and advance the head once. -/
def processHead (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) : State g.vertexCount :=
  let row := g.outArcs (s.queue[s.head]'h)
  let t := visitRow row s
  { t with
    head := s.head + 1
    head_le_queue := Nat.le_trans (Nat.succ_le_of_lt h)
      (visitRow_spec row s).2.2.2.1 }

theorem processHead_spec (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) :
    let row := g.outArcs (s.queue[s.head]'h)
    let t := processHead g s h
    t.remaining.size = g.vertexCount ∧
    t.head = s.head + 1 ∧
    t.edgeVisits = s.edgeVisits + row.length ∧
    s.queue.size ≤ t.queue.size ∧
    t.queue.size ≤ s.queue.size + row.length := by
  have hr := visitRow_spec (g.outArcs (s.queue[s.head]'h)) s
  exact ⟨hr.1, rfl, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2⟩

inductive StopReason where
  | noNext
  | fuelExhausted
  deriving Repr, DecidableEq

/-- Fuel counts processed rows. At zero fuel, still distinguish an empty
    unread suffix from a queue with a pending vertex. -/
def scan (g : Digraph) :
    Nat → State g.vertexCount → State g.vertexCount × StopReason
  | 0, s => (s, if s.head < s.queue.size then .fuelExhausted else .noNext)
  | k + 1, s =>
      if h : s.head < s.queue.size then
        scan g k (processHead g s h)
      else
        (s, .noNext)

def StopReason.Valid {n : Nat} (reason : StopReason) (s : State n) : Prop :=
  match reason with
  | .noNext => s.head = s.queue.size
  | .fuelExhausted => s.head < s.queue.size

theorem scan_stop_spec (g : Digraph) (fuel : Nat) (s : State g.vertexCount) :
    StopReason.Valid (scan g fuel s).2 (scan g fuel s).1 := by
  induction fuel generalizing s with
  | zero =>
      by_cases h : s.head < s.queue.size
      · simp [scan, h, StopReason.Valid]
      · have he := Nat.le_antisymm s.head_le_queue (Nat.le_of_not_gt h)
        simp [scan, StopReason.Valid, he]
  | succ k ih =>
      by_cases h : s.head < s.queue.size
      · simpa only [scan, dite_eq_left h] using ih (processHead g s h)
      · have he := Nat.le_antisymm s.head_le_queue (Nat.le_of_not_gt h)
        simp [scan, StopReason.Valid, he]

/-- Enumerate original IDs and enqueue precisely those with computed degree 0. -/
private def seed {n : Nat} (a : Array Nat) (ha : a.size = n) :
    Array (Fin n) :=
  (List.ofFn (fun v : Fin n => v)).foldl
    (fun q v =>
      if a[v.val]'(by rw [ha]; exact v.isLt) = 0 then q.push v else q)
    #[]

structure Result (n : Nat) where
  state : State n
  indegreeVisits : Nat
  stop : StopReason

/-- Return the enqueue array itself, without copying or certifying its order. -/
def Result.order {n : Nat} (r : Result n) : Array (Fin n) :=
  r.state.queue

def Result.rowsProcessed {n : Nat} (r : Result n) : Nat :=
  r.state.head

def Result.edgeVisits {n : Nat} (r : Result n) : Nat :=
  r.state.edgeVisits

/-- Use the indegree prepass once, then give the row scan `vertexCount` fuel.
    `Array.push` is abstract here. An `n`-slot layout is deferred until the
    queue exactly-once invariant is proved; no amortized bound is claimed. -/
def run (g : Digraph) : Result g.vertexCount :=
  let pre := indegreeScan g
  let hs : pre.1.size = g.vertexCount := indegrees_size g
  let initial : State g.vertexCount :=
    { remaining := pre.1
      queue := seed pre.1 hs
      head := 0
      edgeVisits := 0
      remaining_size := hs
      head_le_queue := Nat.zero_le _ }
  let final := scan g g.vertexCount initial
  { state := final.1, indegreeVisits := pre.2, stop := final.2 }

theorem run_stop_spec (g : Digraph) :
    StopReason.Valid (run g).stop (run g).state := by
  unfold run
  exact scan_stop_spec g g.vertexCount _


open Digraph

private theorem remaining_getElem?_degree {n : Nat} (s : State n) (v : Fin n) :
    s.remaining[v.val]? = some (s.degree v) := by
  have hv : v.val < s.remaining.size := by
    simpa only [s.remaining_size] using v.isLt
  exact Array.getElem?_eq_getElem hv

/-- Only the visited vertex's degree is decremented, with `Nat` saturation. -/
theorem visit_degree {n : Nat} (s : State n) (w v : Fin n) :
    (visit s w).degree v = s.degree v - (if w = v then 1 else 0) := by
  apply Option.some.inj
  rw [← remaining_getElem?_degree (visit s w) v]
  change (s.remaining.setIfInBounds w.val (s.degree w - 1))[v.val]? =
    some (s.degree v - (if w = v then 1 else 0))
  by_cases h : w = v
  · subst w
    rw [ite_eq_left rfl]
    exact Array.getElem?_setIfInBounds_self_of_lt
      (by simpa only [s.remaining_size] using v.isLt)
  · have hval : w.val ≠ v.val := fun he => h (Fin.ext he)
    rw [ite_eq_right h, Nat.sub_zero, ← remaining_getElem?_degree s v]
    first
    | exact Array.getElem?_setIfInBounds_ne hval
    | exact Array.getElem?_setIfInBounds_ne (Ne.symm hval)

/-- Each occurrence contributes one to the total decrement, including repeats. -/
theorem visitRow_degree {n : Nat} (row : List (Fin n)) (s : State n)
    (v : Fin n) :
    (visitRow row s).degree v = s.degree v - countOccurrence v row := by
  induction row generalizing s with
  | nil => simp [visitRow, countOccurrence]
  | cons w ws ih =>
      simp only [visitRow, ih, visit_degree, Nat.sub_sub, countOccurrence]

theorem visit_queue_toList {n : Nat} (s : State n) (w : Fin n) :
    (visit s w).queue.toList =
      s.queue.toList ++ (if s.degree w = 1 then [w] else []) := by
  by_cases h : s.degree w = 1 <;> simp [visit, h, Array.toList_push]

/-- The old queue is an unchanged prefix. Every appended vertex occurs in the
    row, had positive degree before the row, and has degree zero afterward. -/
theorem visitRow_queue_tail {n : Nat} (row : List (Fin n)) (s : State n) :
    ∃ tail : List (Fin n),
      (visitRow row s).queue.toList = s.queue.toList ++ tail ∧
      ∀ v ∈ tail, v ∈ row ∧ 0 < s.degree v ∧ (visitRow row s).degree v = 0 := by
  induction row generalizing s with
  | nil =>
      exact ⟨[], by simp [visitRow], by simp⟩
  | cons w ws ih =>
      obtain ⟨tail, hq, ht⟩ := ih (visit s w)
      refine ⟨(if s.degree w = 1 then [w] else []) ++ tail, ?_, ?_⟩
      · change (visitRow ws (visit s w)).queue.toList = _
        rw [hq, visit_queue_toList, List.append_assoc]
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · by_cases h : s.degree w = 1
          · have he : v = w := by simpa [h] using hv
            subst v
            refine ⟨by simp, by simp [h], ?_⟩
            change (visitRow ws (visit s w)).degree w = 0
            simp [visitRow_degree, visit_degree, h]
          · simp [h] at hv
        · obtain ⟨hm, hp, hz⟩ := ht v hv
          rw [visit_degree] at hp
          exact ⟨List.mem_cons_of_mem _ hm,
            Nat.lt_of_lt_of_le hp (Nat.sub_le _ _), hz⟩

theorem visitRow_queue_prefix {n : Nat} (row : List (Fin n)) (s : State n)
    {i : Nat} (hi : i < s.queue.size) :
    (visitRow row s).queue[i]? = s.queue[i]? := by
  obtain ⟨tail, hq, _⟩ := visitRow_queue_tail row s
  have hi' : i < s.queue.toList.length := by simpa using hi
  have hp : (visitRow row s).queue.toList[i]? = s.queue.toList[i]? := by
    rw [hq]
    exact List.getElem?_append_left hi'
  simpa using hp

theorem processHead_degree (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) (v : Fin g.vertexCount) :
    (processHead g s h).degree v =
      s.degree v - countOccurrence v (g.outArcs (s.queue[s.head]'h)) :=
  visitRow_degree (g.outArcs (s.queue[s.head]'h)) s v

theorem processHead_queue_prefix (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) {i : Nat} (hi : i < s.queue.size) :
    (processHead g s h).queue[i]? = s.queue[i]? :=
  visitRow_queue_prefix (g.outArcs (s.queue[s.head]'h)) s hi


end Kahn
end PaperB
