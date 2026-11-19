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


/-- The entire queue is duplicate-free and contains exactly the vertices
    whose remaining degree is zero. -/
def State.QueueInv {n : Nat} (s : State n) : Prop :=
  s.queue.toList.Nodup ∧
    ∀ v : Fin n, v ∈ s.queue.toList ↔ s.degree v = 0

private theorem queue_nodup_append_singleton {α : Type _} {xs : List α}
    {x : α} (hn : xs.Nodup) (hx : x ∉ xs) : (xs ++ [x]).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
      have hax : a ≠ x := by
        intro he
        subst a
        exact hx (by simp)
      have hxt : x ∉ xs := fun hm => hx (List.mem_cons_of_mem _ hm)
      change (a :: (xs ++ [x])).Nodup
      exact List.nodup_cons.mpr
        ⟨by simpa [List.mem_append, hax] using ha, ih ht hxt⟩

/-- Outside the enqueue branch, subtraction preserves zero status:
    zero saturates, and a degree of at least two stays positive. -/
private theorem queue_sub_one_zero_iff (d : Nat) (h : d ≠ 1) :
    d = 0 ↔ d - 1 = 0 := by
  cases d with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => exact (h rfl).elim
      | succ k =>
          change Nat.succ (Nat.succ k) = 0 ↔ Nat.succ k = 0
          simp

theorem visit_queueInv {n : Nat} (s : State n) (w : Fin n)
    (hs : s.QueueInv) : (visit s w).QueueInv := by
  unfold State.QueueInv at hs ⊢
  obtain ⟨hn, hm⟩ := hs
  by_cases hw : s.degree w = 1
  · rw [visit_queue_toList, ite_eq_left hw]
    have hp : 0 < s.degree w := by simp [hw]
    have hfresh : w ∉ s.queue.toList := by
      intro hmem
      have hz := (hm w).mp hmem
      rw [hz] at hp
      exact (Nat.lt_irrefl 0) hp
    refine ⟨queue_nodup_append_singleton hn hfresh, ?_⟩
    intro v
    by_cases he : w = v
    · subst v
      simp [List.mem_append, visit_degree, hw]
    · simpa [List.mem_append, visit_degree, he, Ne.symm he] using (hm v)
  · rw [visit_queue_toList, ite_eq_right hw, List.append_nil]
    refine ⟨hn, ?_⟩
    intro v
    by_cases he : w = v
    · subst v
      rw [visit_degree, ite_eq_left rfl]
      exact (hm w).trans (queue_sub_one_zero_iff _ hw)
    · simpa [visit_degree, he] using (hm v)

theorem visitRow_queueInv {n : Nat} (row : List (Fin n)) (s : State n)
    (hs : s.QueueInv) : (visitRow row s).QueueInv := by
  induction row generalizing s with
  | nil => simpa only [visitRow] using hs
  | cons w ws ih =>
      simpa only [visitRow] using ih (visit s w) (visit_queueInv s w hs)

theorem processHead_queueInv (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) (hs : s.QueueInv) :
    (processHead g s h).QueueInv := by
  have ht := visitRow_queueInv (g.outArcs (s.queue[s.head]'h)) s hs
  unfold State.QueueInv at ht ⊢
  exact ht

private theorem queue_foldl_push_toList {α : Type _} (p : α → Prop)
    [DecidablePred p] (xs : List α) (q : Array α) :
    (xs.foldl (fun b x => if p x then b.push x else b) q).toList =
      q.toList ++ xs.filter (fun x => decide (p x)) := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x <;>
        simp [List.foldl, hx, ih, Array.toList_push,
          List.append_assoc]

theorem seed_queue_toList {n : Nat} (a : Array Nat) (ha : a.size = n) :
    (seed a ha).toList =
      (List.ofFn (fun v : Fin n => v)).filter
        (fun v => decide (a[v.val]'(by rw [ha]; exact v.isLt) = 0)) := by
  simpa [seed] using
    (queue_foldl_push_toList
      (fun v : Fin n => a[v.val]'(by rw [ha]; exact v.isLt) = 0)
      (List.ofFn (fun v : Fin n => v)) (#[] : Array (Fin n)))

private theorem queue_nodup_ofFn {α : Type _} {n : Nat} (f : Fin n → α)
    (hf : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hm
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
        have he : i.succ = (0 : Fin (n + 1)) := by
          apply hf
          first | exact hi | exact hi.symm
        have hv := congrArg Fin.val he
        change Nat.succ i.val = 0 at hv
        exact Nat.noConfusion hv
      · apply ih
        intro i j hij
        have hv := congrArg Fin.val (hf i.succ j.succ hij)
        exact Fin.ext (Nat.succ.inj hv)

private theorem queue_nodup_filter {α : Type _} (p : α → Bool)
    (xs : List α) (hn : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hx, ht⟩ := List.nodup_cons.mp hn
      cases hp : p x with
      | false => simpa [List.filter_cons, hp] using (ih ht)
      | true =>
          have hxf : x ∉ xs.filter p := fun hm => hx (List.mem_filter.mp hm).1
          have hf : (x :: xs.filter p).Nodup :=
            List.nodup_cons.mpr ⟨hxf, ih ht⟩
          simpa [List.filter_cons, hp] using hf

theorem seed_queueInv {n : Nat} (a : Array Nat) (ha : a.size = n) :
    State.QueueInv
      ({ remaining := a
         queue := seed a ha
         head := 0
         edgeVisits := 0
         remaining_size := ha
         head_le_queue := Nat.zero_le _ } : State n) := by
  let ids := List.ofFn (fun v : Fin n => v)
  let p : Fin n → Bool := fun v =>
    decide (a[v.val]'(by rw [ha]; exact v.isLt) = 0)
  have hq : (seed a ha).toList = ids.filter p := seed_queue_toList a ha
  have hn : ids.Nodup :=
    queue_nodup_ofFn (fun v : Fin n => v) (fun _ _ h => h)
  change (seed a ha).toList.Nodup ∧
    ∀ v : Fin n, v ∈ (seed a ha).toList ↔
      a[v.val]'(by rw [ha]; exact v.isLt) = 0
  rw [hq]
  refine ⟨queue_nodup_filter p ids hn, ?_⟩
  intro v
  have hv : v ∈ ids := by
    change v ∈ List.ofFn (fun w : Fin n => w)
    exact List.mem_ofFn.mpr ⟨v, rfl⟩
  simp [List.mem_filter, hv, p]

/-- The queue entries already consumed, in processing order. -/
def State.processedPrefix {n : Nat} (s : State n) : List (Fin n) :=
  s.queue.toList.take s.head

theorem processHead_processedPrefix (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) :
    (processHead g s h).processedPrefix =
      s.processedPrefix ++ [s.queue[s.head]'h] := by
  let t := processHead g s h
  obtain ⟨tail, hq, _⟩ :=
    visitRow_queue_tail (g.outArcs (s.queue[s.head]'h)) s
  change t.queue.toList = s.queue.toList ++ tail at hq
  have hb : s.head ≤ s.queue.toList.length := by
    simpa using s.head_le_queue
  have hp : t.queue.toList.take s.head = s.queue.toList.take s.head := by
    rw [hq, List.take_append_of_le_length hb]
  have he : t.queue.toList[s.head]? = some (s.queue[s.head]'h) := by
    have ha : t.queue[s.head]? = some (s.queue[s.head]'h) :=
      (processHead_queue_prefix g s h h).trans (Array.getElem?_eq_getElem h)
    simpa using ha
  change t.queue.toList.take (s.head + 1) =
    s.queue.toList.take s.head ++ [s.queue[s.head]'h]
  rw [List.take_add_one, hp, he] <;> rfl

/-- Count all incoming arc occurrences from processed vertices, including repeats. -/
def processedIncoming (g : Digraph) (s : State g.vertexCount)
    (v : Fin g.vertexCount) : Nat :=
  (s.processedPrefix.map (fun w => countOccurrence v (g.outArcs w))).sum

private theorem processed_sum_append_singleton (xs : List Nat) (a : Nat) :
    (xs ++ [a]).sum = xs.sum + a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, List.sum_cons, ih, Nat.add_assoc]

theorem processHead_processedIncoming (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) (v : Fin g.vertexCount) :
    processedIncoming g (processHead g s h) v =
      processedIncoming g s v + countOccurrence v (g.outArcs (s.queue[s.head]'h)) := by
  simp only [processedIncoming, processHead_processedPrefix, List.map_append,
    List.map_cons, List.map_nil, processed_sum_append_singleton]

/-- The initial indegree is read from the prepass array used by `run`. -/
def initialIndegree (g : Digraph) (v : Fin g.vertexCount) : Nat :=
  (indegreeScan g).1[v.val]'(by
    change v.val < (g.indegrees).size
    exact g.indegrees_size.symm ▸ v.isLt)

/-- Every remaining degree is the initial indegree minus the occurrences
    contributed by the processed prefix, with subtraction on `Nat`. -/
def State.DegreeInv (g : Digraph) (s : State g.vertexCount) : Prop :=
  ∀ v : Fin g.vertexCount,
    s.degree v = initialIndegree g v - processedIncoming g s v

theorem processHead_degreeInv (g : Digraph) (s : State g.vertexCount)
    (h : s.head < s.queue.size) (hs : State.DegreeInv g s) :
    State.DegreeInv g (processHead g s h) := by
  intro v
  rw [processHead_degree g s h v, hs v, Nat.sub_sub,
    processHead_processedIncoming g s h v]

theorem seed_degreeInv (g : Digraph) :
    State.DegreeInv g
      { remaining := (indegreeScan g).1
        queue := seed (indegreeScan g).1 (indegrees_size g)
        head := 0
        edgeVisits := 0
        remaining_size := indegrees_size g
        head_le_queue := Nat.zero_le _ } := by
  intro v
  change initialIndegree g v = initialIndegree g v - 0
  exact (Nat.sub_zero _).symm

/-- The original vertex IDs not yet consumed from the queue. -/
def State.unfinished {n : Nat} (s : State n) : List (Fin n) :=
  (List.ofFn (fun u : Fin n => u)).filter
    (fun u => decide (u ∉ s.processedPrefix))

private theorem ex11_mem_allIDs {n : Nat} (u : Fin n) :
    u ∈ List.ofFn (fun w : Fin n => w) := by
  rw [List.mem_ofFn]
  exact ⟨u, rfl⟩

theorem State.mem_unfinished {n : Nat} (s : State n) (u : Fin n) :
    u ∈ s.unfinished ↔ u ∉ s.processedPrefix := by
  simp only [State.unfinished, List.mem_filter, decide_eq_true_eq,
    ex11_mem_allIDs, true_and]

private theorem ex11_nodup_append {α : Type _} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hxy : ∀ a, a ∈ xs → a ∉ ys) : (xs ++ ys).Nodup := by
  induction xs with
  | nil => simpa using hy
  | cons a xs ih =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hx
      change (a :: (xs ++ ys)).Nodup
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact ha hm
        · exact hxy a (by simp) hm
      · exact ih ht (fun b hb => hxy b (List.mem_cons_of_mem _ hb))

theorem State.processedPrefix_append_unfinished_perm {n : Nat}
    (s : State n) (hq : s.QueueInv) :
    (s.processedPrefix ++ s.unfinished).Perm (List.ofFn (fun u : Fin n => u)) := by
  have hpre : s.processedPrefix.Nodup := by
    unfold State.processedPrefix
    exact List.Pairwise.sublist (by apply List.take_sublist) hq.1
  have hall : (List.ofFn (fun u : Fin n => u)).Nodup :=
    queue_nodup_ofFn (fun u : Fin n => u) (fun _ _ h => h)
  have hun : s.unfinished.Nodup := by
    unfold State.unfinished
    exact List.Pairwise.sublist (by apply List.filter_sublist) hall
  have hcat : (s.processedPrefix ++ s.unfinished).Nodup :=
    ex11_nodup_append hpre hun
      (fun u hu hf => ((State.mem_unfinished s u).mp hf) hu)
  apply (List.perm_ext_iff_of_nodup hcat hall).mpr
  intro u
  rw [List.mem_append, State.mem_unfinished]
  exact ⟨fun _ => ex11_mem_allIDs u, fun _ => Classical.em _⟩

private theorem ex11_map_ofFn {α β : Type _} (f : α → β)
    {n : Nat} (a : Fin n → α) :
    (List.ofFn a).map f = List.ofFn (fun i => f (a i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.map_cons, ih]

private theorem ex11_sum_map_perm {α : Type _} (f : α → Nat)
    {xs ys : List α} (h : xs.Perm ys) :
    (xs.map f).sum = (ys.map f).sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.map_cons, List.sum_cons, ih]
  | swap a b xs =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem ex11_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.cons_append, List.sum_cons, ih, Nat.add_assoc]

/-- The remaining degree counts occurrences from exactly the unprocessed tails. -/
theorem State.degree_eq_unfinished_sum (g : Digraph) (s : State g.vertexCount)
    (hq : s.QueueInv) (hd : State.DegreeInv g s) (v : Fin g.vertexCount) :
    s.degree v =
      (s.unfinished.map (fun u => countOccurrence v (g.outArcs u))).sum := by
  let f : Fin g.vertexCount → Nat := fun u => countOccurrence v (g.outArcs u)
  have hi : initialIndegree g v =
      ((List.ofFn (fun u : Fin g.vertexCount => u)).map f).sum := by
    calc
      initialIndegree g v =
          ((List.ofFn g.outArcs).map (countOccurrence v)).sum :=
        Digraph.indegrees_getElem g v
      _ = _ := by simp only [ex11_map_ofFn, f]
  have hp := ex11_sum_map_perm f (State.processedPrefix_append_unfinished_perm s hq)
  rw [List.map_append, ex11_sum_append] at hp
  have htotal : initialIndegree g v =
      processedIncoming g s v + (s.unfinished.map f).sum :=
    hi.trans hp.symm
  change s.degree v = (s.unfinished.map f).sum
  rw [hd v, htotal, Nat.add_sub_cancel_left]

theorem countOccurrence_pos_iff_row_mem {n : Nat} (v : Fin n)
    (row : List (Fin n)) :
    0 < countOccurrence v row ↔ v ∈ row := by
  induction row with
  | nil => simp [countOccurrence]
  | cons w ws ih =>
      by_cases h : w = v
      · subst w
        have hpos : 0 < 1 + countOccurrence v ws := by
          rw [Nat.add_comm]
          exact Nat.zero_lt_succ _
        exact ⟨fun _ => by simp, fun _ => by simpa [countOccurrence] using hpos⟩
      · simpa [countOccurrence, h, Ne.symm h] using ih

private theorem ex11_sum_map_eq_zero_iff {α : Type _} (f : α → Nat)
    (xs : List α) :
    (xs.map f).sum = 0 ↔ ∀ a ∈ xs, f a = 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, ih]
      constructor
      · intro ⟨ha, ht⟩ b hb
        rcases List.mem_cons.mp hb with he | hm
        · subst b
          exact ha
        · exact ht b hm
      · intro h
        exact ⟨h a (by simp), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- A vertex has degree zero exactly when no unprocessed tail has an arc to it. -/
theorem State.degree_eq_zero_iff_no_unprocessed_arc
    (g : Digraph) (s : State g.vertexCount)
    (hq : s.QueueInv) (hd : State.DegreeInv g s) (v : Fin g.vertexCount) :
    s.degree v = 0 ↔
      ¬ ∃ u : Fin g.vertexCount, u ∉ s.processedPrefix ∧ v ∈ g.outArcs u := by
  rw [State.degree_eq_unfinished_sum g s hq hd v, ex11_sum_map_eq_zero_iff]
  constructor
  · intro h hex
    obtain ⟨u, hu, ha⟩ := hex
    have hc := h u ((State.mem_unfinished s u).mpr hu)
    have hp := (countOccurrence_pos_iff_row_mem v (g.outArcs u)).mpr ha
    exact (Nat.lt_irrefl 0) (by simpa only [hc] using hp)
  · intro h u hu
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact h ⟨u, (State.mem_unfinished s u).mp hu,
      (countOccurrence_pos_iff_row_mem v (g.outArcs u)).mp hp⟩

end Kahn
end PaperB
