-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
import Std
import PaperB.WordOps

set_option autoImplicit false

namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add sub band ltb)

structure Layout (bits : Nat) where
  registerCount : Nat
  inputCap : Nat
  workCap : Nat
  inputFits : inputCap ≤ 2 ^ bits
  workFits : workCap ≤ 2 ^ bits

-- The full preallocated input array is readable. It is not part of mutable state.
structure Input {bits : Nat} (L : Layout bits) where
  words : Array (Word bits)
  size_eq : words.size = L.inputCap

structure State {bits : Nat} (L : Layout bits) where
  regs : Array (Word bits)
  data : Array (Word bits)
  pc : Nat
  regs_size : regs.size = L.registerCount
  data_size : data.size = L.workCap

inductive Instr (bits registerCount : Nat) where
  | imm (dst : Fin registerCount) (value : Word bits)
  | mov (dst src : Fin registerCount)
  | add (dst lhs rhs : Fin registerCount)
  | sub (dst lhs rhs : Fin registerCount)
  | band (dst lhs rhs : Fin registerCount)
  | loadInput (dst addr : Fin registerCount)
  | loadData (dst addr : Fin registerCount)
  | storeData (addr src : Fin registerCount)
  | branchLt (lhs rhs : Fin registerCount) (ltPC gePC : Nat)
  | goto (target : Nat)
  | halt

abbrev Program {bits : Nat} (L : Layout bits) :=
  Array (Instr bits L.registerCount)

inductive Transition {bits : Nat} (L : Layout bits) where
  | next (state : State L)
  | halted (state : State L)

variable {bits : Nat} {L : Layout bits}

private def readReg (s : State L) (r : Fin L.registerCount) : Word bits :=
  s.regs[r.val]'(by simpa only [s.regs_size] using r.isLt)

private def writeReg (s : State L) (r : Fin L.registerCount) (w : Word bits) :
    State L :=
  let h : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  { s with
    regs := s.regs.set r.val w h
    regs_size := by simp only [Array.size_set, s.regs_size] }

private def advance (code : Program L) (s : State L) (pc : Nat) :
    Option (Transition L) :=
  if pc < code.size then some (.next { s with pc := pc }) else none

/-- Reject an invalid fetch, memory access, or chosen successor PC. -/
def step (code : Program L) (input : Input L) (s : State L) :
    Option (Transition L) := do
  let instr ← code[s.pc]?
  let put (dst : Fin L.registerCount) (w : Word bits) :=
    advance code (writeReg s dst w) (s.pc + 1)
  match instr with
  | .imm dst w => put dst w
  | .mov dst src => put dst (readReg s src)
  | .add dst x y => put dst (add (readReg s x) (readReg s y))
  | .sub dst x y => put dst (sub (readReg s x) (readReg s y))
  | .band dst x y => put dst (band (readReg s x) (readReg s y))
  | .loadInput dst addr => do
    let w ← input.words[(readReg s addr).val]?
    put dst w
  | .loadData dst addr => do
    let w ← s.data[(readReg s addr).val]?
    put dst w
  | .storeData addr src =>
    let i := (readReg s addr).val
    if h : i < s.data.size then
      advance code
        { s with
          data := s.data.set i (readReg s src) h
          data_size := by simp only [Array.size_set, s.data_size] }
        (s.pc + 1)
    else none
  | .branchLt x y ltPC gePC =>
    advance code s (if ltb (readReg s x) (readReg s y) then ltPC else gePC)
  | .goto target => advance code s target
  | .halt => some (.halted s)

structure Result {bits : Nat} (L : Layout bits) where
  finalState : State L
  executed : Nat

/-- Return a result only on halt. Halt counts as one executed instruction. -/
def run (code : Program L) (input : Input L) :
    Nat → State L → Option (Result L)
  | 0, _ => none
  | n + 1, s =>
    match step code input s with
    | none => none
    | some (.halted t) => some ⟨t, 1⟩
    | some (.next t) =>
      match run code input n t with
      | none => none
      | some r => some { r with executed := r.executed + 1 }

theorem run_executed_le {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {r : Result L}
    (h : run code input fuel s = some r) : r.executed ≤ fuel := by
  induction fuel generalizing s r with
  | zero => simp [run] at h
  | succ n ih =>
    cases hs : step code input s with
    | none => simp [run, hs] at h
    | some out =>
      cases out with
      | halted t =>
        have hr : (⟨t, 1⟩ : Result L) = r := by simpa [run, hs] using h
        subst r
        exact Nat.succ_le_succ (Nat.zero_le n)
      | next t =>
        cases ht : run code input n t with
        | none => simp [run, hs, ht] at h
        | some q =>
          have hr : { q with executed := q.executed + 1 } = r := by
            simpa [run, hs, ht] using h
          subst r
          exact Nat.succ_le_succ (ih (s := t) (r := q) ht)

-- The input array is the same parameter throughout the run.
theorem run_preserves_lengths {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {r : Result L}
    (_ : run code input fuel s = some r) :
    r.finalState.data.size = s.data.size ∧ r.finalState.regs.size = s.regs.size :=
  ⟨r.finalState.data_size.trans s.data_size.symm,
   r.finalState.regs_size.trans s.regs_size.symm⟩

/-- Model word slots only: input, data, and registers; excludes code and PC. -/
def storageWords (input : Input L) (s : State L) : Nat :=
  input.words.size + s.data.size + s.regs.size

def footprint (L : Layout bits) : Nat :=
  L.inputCap + L.workCap + L.registerCount

theorem storageWords_eq (input : Input L) (s : State L) :
    storageWords input s = footprint L := by
  simp only [storageWords, footprint, input.size_eq, s.data_size, s.regs_size]

structure Observation {bits : Nat} (L : Layout bits) where
  result : Result L
  initialWords : Nat
  finalWords : Nat

def observe (code : Program L) (input : Input L) (fuel : Nat) (s : State L) :
    Option (Observation L) :=
  match run code input fuel s with
  | none => none
  | some r => some ⟨r, storageWords input s, storageWords input r.finalState⟩

theorem observe_footprint {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {o : Observation L}
    (h : observe code input fuel s = some o) :
    o.initialWords = footprint L ∧ o.finalWords = footprint L := by
  cases hr : run code input fuel s with
  | none => simp [observe, hr] at h
  | some r =>
    have ho : (⟨r, storageWords input s, storageWords input r.finalState⟩ :
        Observation L) = o := by simpa [observe, hr] using h
    subst o
    exact ⟨storageWords_eq input s, storageWords_eq input r.finalState⟩

/-- Extra fuel does not change a successful execution. -/
theorem run_stable_of_le {code : Program L} {input : Input L}
    {fuel more : Nat} {s : State L} {r : Result L}
    (hle : fuel ≤ more) (h : run code input fuel s = some r) :
    run code input more s = some r := by
  induction fuel generalizing more s r with
  | zero => simp [run] at h
  | succ n ih =>
    cases more with
    | zero => simp at hle
    | succ m =>
      cases hs : step code input s with
      | none => simp [run, hs] at h
      | some out =>
        cases out with
        | halted t => simpa [run, hs] using h
        | next t =>
          cases ht : run code input n t with
          | none => simp [run, hs, ht] at h
          | some q =>
            have hm : run code input m t = some q :=
              ih (more := m) (s := t) (r := q) (Nat.le_of_succ_le_succ hle) ht
            simpa [run, hs, ht, hm] using h

/-- The whole result, including the instruction count, is independent of fuel
whenever both runs succeed. -/
theorem run_success_unique {code : Program L} {input : Input L}
    {fuel₁ fuel₂ : Nat} {s : State L} {r₁ r₂ : Result L}
    (h₁ : run code input fuel₁ s = some r₁)
    (h₂ : run code input fuel₂ s = some r₂) : r₁ = r₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact Option.some.inj ((run_stable_of_le hle h₁).symm.trans h₂)
  · exact Option.some.inj (h₁.symm.trans (run_stable_of_le hle h₂))

/-- A successful trace records the initial state and one successor per
instruction, including the state returned by halt. -/
inductive SuccessfulTrace (code : Program L) (input : Input L) :
    State L → List (State L) → Result L → Prop where
  | halted {s t : State L} (hs : step code input s = some (.halted t)) :
      SuccessfulTrace code input s [s, t] ⟨t, 1⟩
  | next {s t : State L} {states : List (State L)} {r : Result L}
      (hs : step code input s = some (.next t))
      (tail : SuccessfulTrace code input t states r) :
      SuccessfulTrace code input s (s :: states)
        { r with executed := r.executed + 1 }

theorem SuccessfulTrace.unique {code : Program L} {input : Input L}
    {s : State L} {states states' : List (State L)} {r r' : Result L}
    (h : SuccessfulTrace code input s states r)
    (h' : SuccessfulTrace code input s states' r') :
    states = states' ∧ r = r' := by
  induction h generalizing states' r' with
  | halted hs =>
    cases h' with
    | halted hs' =>
      have he := Transition.halted.inj (Option.some.inj (hs.symm.trans hs'))
      cases he
      exact ⟨rfl, rfl⟩
    | next hs' ht' =>
      have he := Option.some.inj (hs.symm.trans hs')
      cases he
  | next hs ht ih =>
    cases h' with
    | halted hs' =>
      have he := Option.some.inj (hs.symm.trans hs')
      cases he
    | next hs' ht' =>
      have he := Transition.next.inj (Option.some.inj (hs.symm.trans hs'))
      cases he
      obtain ⟨hl, hr⟩ := @ih _ _ ht'
      cases hl
      cases hr
      exact ⟨rfl, rfl⟩

theorem run_has_successfulTrace {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {r : Result L}
    (h : run code input fuel s = some r) :
    ∃ states : List (State L), SuccessfulTrace code input s states r := by
  induction fuel generalizing s r with
  | zero => simp [run] at h
  | succ n ih =>
    cases hs : step code input s with
    | none => simp [run, hs] at h
    | some out =>
      cases out with
      | halted t =>
        have hr : (⟨t, 1⟩ : Result L) = r := by simpa [run, hs] using h
        subst r
        exact ⟨[s, t], SuccessfulTrace.halted hs⟩
      | next t =>
        cases ht : run code input n t with
        | none => simp [run, hs, ht] at h
        | some q =>
          have hr : { q with executed := q.executed + 1 } = r := by
            simpa [run, hs, ht] using h
          subst r
          obtain ⟨states, htail⟩ := ih (s := t) (r := q) ht
          exact ⟨s :: states, SuccessfulTrace.next hs htail⟩

theorem SuccessfulTrace.storage_eq {code : Program L} {input : Input L}
    {s t : State L} {states : List (State L)} {r : Result L}
    (_ : SuccessfulTrace code input s states r) (_ : t ∈ states) :
    storageWords input t = footprint L :=
  storageWords_eq input t

/-- Peak modeled word slots; excludes code, PC, and metadata charges. -/
def tracePeakWords (input : Input L) : List (State L) → Nat
  | [] => 0
  | s :: states => max (storageWords input s) (tracePeakWords input states)

theorem SuccessfulTrace.peak_eq {code : Program L} {input : Input L}
    {s : State L} {states : List (State L)} {r : Result L}
    (h : SuccessfulTrace code input s states r) :
    tracePeakWords input states = footprint L := by
  induction h with
  | halted hs =>
    simp [tracePeakWords, storageWords_eq, Nat.max_eq_left]
  | next hs ht ih =>
    simp [tracePeakWords, storageWords_eq, ih]

end PaperB.RamProgram
