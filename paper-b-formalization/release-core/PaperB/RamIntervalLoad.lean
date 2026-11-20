import PaperB.RamProgram

namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add)

abbrev sealedIntervalLayout (bits workCap : Nat)
    (fits : workCap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, workCap, 0, fits, Nat.zero_le _⟩

def sealedIntervalLookup {bits workCap : Nat} (fits : workCap ≤ 2 ^ bits) :
    Program (sealedIntervalLayout bits workCap fits) :=
  #[.add 5 3 1, .loadInput 5 5,
    .add 6 4 1, .loadInput 6 6,
    .add 7 3 2, .loadInput 7 7, .halt]

section
variable {bits : Nat} {L : Layout bits}

private def intervalReg (s : State L) (r : Fin L.registerCount) : Word bits :=
  s.regs[r.val]'(by rw [s.regs_size]; exact r.isLt)

private def intervalPut (s : State L) (d : Fin L.registerCount)
    (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem intervalReg_put (s : State L) (d r : Fin L.registerCount)
    (w : Word bits) :
    intervalReg (intervalPut s d w) r =
      if r = d then w else intervalReg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, Ne.symm hv]

private theorem intervalReg_put_twice_ne (s : State L)
    (d r : Fin L.registerCount) (addr w : Word bits) (hr : r ≠ d) :
    intervalReg (intervalPut (intervalPut s d addr) d w) r =
      intervalReg s r := by
  simp only [intervalReg_put, ite_eq_right hr]

private theorem intervalFetch
    {code : Program L} {input : Input L} {s : State L}
    {d x y : Fin L.registerCount} {a b w : Word bits}
    (ha : code[s.pc]? = some (.add d x y))
    (hl : code[s.pc + 1]? = some (.loadInput d d))
    (hn : s.pc + 2 < code.size)
    (hx : intervalReg s x = a) (hy : intervalReg s y = b)
    (hfit : a.val + b.val < 2 ^ bits)
    (hw : input.words[a.val + b.val]? = some w) :
    let u := intervalPut s d (add a b)
    step code input s = some (.next u) ∧
      step code input u = some (.next (intervalPut u d w)) := by
  let addr := add a b
  let u := intervalPut s d addr
  change step code input s = some (.next u) ∧
    step code input u = some (.next (intervalPut u d w))
  have hval : addr.val = a.val + b.val := by
    change (a.val + b.val) % (2 ^ bits) = a.val + b.val
    exact Nat.mod_eq_of_lt hfit
  constructor
  · have hs : s.pc + 1 < code.size :=
      Nat.lt_trans (Nat.lt_succ_self (s.pc + 1)) hn
    unfold step
    rw [ha]
    change (if s.pc + 1 < code.size then
      some (Transition.next
        (intervalPut s d (add (intervalReg s x) (intervalReg s y))))
      else none) = _
    rw [ite_eq_left hs, hx, hy]
  · have hl' : code[u.pc]? = some (.loadInput d d) := hl
    have hn' : u.pc + 1 < code.size := hn
    have hd : intervalReg u d = addr := by
      change intervalReg (intervalPut s d addr) d = addr
      rw [intervalReg_put, ite_eq_left rfl]
    have hw' : input.words[(intervalReg u d).val]? = some w := by
      rw [hd, hval]
      exact hw
    unfold step
    rw [hl']
    change Option.bind (input.words[(intervalReg u d).val]?) (fun v =>
      if u.pc + 1 < code.size then
        some (Transition.next (intervalPut u d v)) else none) = _
    rw [hw']
    change (if u.pc + 1 < code.size then
      some (Transition.next (intervalPut u d w)) else none) = _
    rw [ite_eq_left hn']

end

theorem sealedIntervalLookup_correct {bits workCap : Nat}
    (fits : workCap ≤ 2 ^ bits)
    (input : Input (sealedIntervalLayout bits workCap fits))
    (s : State (sealedIntervalLayout bits workCap fits))
    (ancestor target entryBase stopBase : Word bits)
    (hpc : s.pc = 0)
    (h1 : s.regs[1]'(by rw [s.regs_size]; change 1 < 16; decide) = ancestor)
    (h2 : s.regs[2]'(by rw [s.regs_size]; change 2 < 16; decide) = target)
    (h3 : s.regs[3]'(by rw [s.regs_size]; change 3 < 16; decide) = entryBase)
    (h4 : s.regs[4]'(by rw [s.regs_size]; change 4 < 16; decide) = stopBase)
    (hEA : entryBase.val + ancestor.val < workCap)
    (hSA : stopBase.val + ancestor.val < workCap)
    (hET : entryBase.val + target.val < workCap) :
    ∃ t : State (sealedIntervalLayout bits workCap fits),
      run (sealedIntervalLookup fits) input 7 s = some ⟨t, 7⟩ ∧
      t.regs[5]'(by rw [t.regs_size]; change 5 < 16; decide) =
        input.words[entryBase.val + ancestor.val]'(by rw [input.size_eq]; exact hEA) ∧
      t.regs[6]'(by rw [t.regs_size]; change 6 < 16; decide) =
        input.words[stopBase.val + ancestor.val]'(by rw [input.size_eq]; exact hSA) ∧
      t.regs[7]'(by rw [t.regs_size]; change 7 < 16; decide) =
        input.words[entryBase.val + target.val]'(by rw [input.size_eq]; exact hET) ∧
      (∀ (r : Fin 16), r ≠ 5 → r ≠ 6 → r ≠ 7 →
        t.regs[r.val]'(by rw [t.regs_size]; exact r.isLt) =
          s.regs[r.val]'(by rw [s.regs_size]; exact r.isLt)) ∧
      t.data = s.data := by
  let code := sealedIntervalLookup fits
  have hiEA : entryBase.val + ancestor.val < input.words.size := by
    rw [input.size_eq]; exact hEA
  have hiSA : stopBase.val + ancestor.val < input.words.size := by
    rw [input.size_eq]; exact hSA
  have hiET : entryBase.val + target.val < input.words.size := by
    rw [input.size_eq]; exact hET
  let w5 := input.words[entryBase.val + ancestor.val]'hiEA
  let w6 := input.words[stopBase.val + ancestor.val]'hiSA
  let w7 := input.words[entryBase.val + target.val]'hiET
  let a5 := add entryBase ancestor
  let a6 := add stopBase ancestor
  let a7 := add entryBase target
  let s1 := intervalPut s 5 a5
  let s2 := intervalPut s1 5 w5
  let s3 := intervalPut s2 6 a6
  let s4 := intervalPut s3 6 w6
  let s5 := intervalPut s4 7 a7
  let s6 := intervalPut s5 7 w7

  have hp2 : s2.pc = 2 := by
    change s.pc + 1 + 1 = 2
    rw [hpc] <;> rfl
  have hp4 : s4.pc = 4 := by
    change s2.pc + 1 + 1 = 4
    rw [hp2] <;> rfl
  have hp6 : s6.pc = 6 := by
    change s4.pc + 1 + 1 = 6
    rw [hp4] <;> rfl

  have hf0 : code[s.pc]? = some (.add 5 3 1) := by rw [hpc] <;> rfl
  have hf1 : code[s.pc + 1]? = some (.loadInput 5 5) := by rw [hpc] <;> rfl
  have hf2 : code[s2.pc]? = some (.add 6 4 1) := by rw [hp2] <;> rfl
  have hf3 : code[s2.pc + 1]? = some (.loadInput 6 6) := by rw [hp2] <;> rfl
  have hf4 : code[s4.pc]? = some (.add 7 3 2) := by rw [hp4] <;> rfl
  have hf5 : code[s4.pc + 1]? = some (.loadInput 7 7) := by rw [hp4] <;> rfl
  have hf6 : code[s6.pc]? = some .halt := by rw [hp6] <;> rfl
  have hn0 : s.pc + 2 < code.size := by rw [hpc]; change 2 < 7; decide
  have hn2 : s2.pc + 2 < code.size := by rw [hp2]; change 4 < 7; decide
  have hn4 : s4.pc + 2 < code.size := by rw [hp4]; change 6 < 7; decide

  have fr2 (r : Fin 16) (hr : r ≠ 5) : intervalReg s2 r = intervalReg s r :=
    intervalReg_put_twice_ne s 5 r a5 w5 hr
  have fr4 (r : Fin 16) (hr : r ≠ 6) : intervalReg s4 r = intervalReg s2 r :=
    intervalReg_put_twice_ne s2 6 r a6 w6 hr
  have fr6 (r : Fin 16) (hr : r ≠ 7) : intervalReg s6 r = intervalReg s4 r :=
    intervalReg_put_twice_ne s4 7 r a7 w7 hr
  have hr01 : intervalReg s 1 = ancestor := h1
  have hr02 : intervalReg s 2 = target := h2
  have hr03 : intervalReg s 3 = entryBase := h3
  have hr04 : intervalReg s 4 = stopBase := h4
  have hr21 : intervalReg s2 1 = ancestor := (fr2 1 (by decide)).trans hr01
  have hr24 : intervalReg s2 4 = stopBase := (fr2 4 (by decide)).trans hr04
  have hr42 : intervalReg s4 2 = target :=
    (fr4 2 (by decide)).trans ((fr2 2 (by decide)).trans hr02)
  have hr43 : intervalReg s4 3 = entryBase :=
    (fr4 3 (by decide)).trans ((fr2 3 (by decide)).trans hr03)

  have hs01 : step code input s = some (.next s1) ∧
      step code input s1 = some (.next s2) :=
    intervalFetch (code := code) (input := input) (s := s) (w := w5)
      hf0 hf1 hn0 hr03 hr01 (Nat.lt_of_lt_of_le hEA fits)
      (getElem?_pos input.words _ hiEA)
  have hs23 : step code input s2 = some (.next s3) ∧
      step code input s3 = some (.next s4) :=
    intervalFetch (code := code) (input := input) (s := s2) (w := w6)
      hf2 hf3 hn2 hr24 hr21 (Nat.lt_of_lt_of_le hSA fits)
      (getElem?_pos input.words _ hiSA)
  have hs45 : step code input s4 = some (.next s5) ∧
      step code input s5 = some (.next s6) :=
    intervalFetch (code := code) (input := input) (s := s4) (w := w7)
      hf4 hf5 hn4 hr43 hr42 (Nat.lt_of_lt_of_le hET fits)
      (getElem?_pos input.words _ hiET)
  have hh : step code input s6 = some (.halted s6) := by
    unfold step
    rw [hf6] <;> rfl
  have hprefix : Steps code input 6 s s6 :=
    Steps.cons hs01.1 <| Steps.cons hs01.2 <|
      Steps.cons hs23.1 <| Steps.cons hs23.2 <|
      Steps.cons hs45.1 <| Steps.cons hs45.2 <| Steps.zero s6

  refine ⟨s6, hprefix.halts hh, ?_, ?_, ?_, ?_, rfl⟩
  · change intervalReg s6 5 = w5
    rw [fr6 5 (by decide), fr4 5 (by decide)]
    change intervalReg (intervalPut s1 5 w5) 5 = w5
    rw [intervalReg_put, ite_eq_left rfl]
  · change intervalReg s6 6 = w6
    rw [fr6 6 (by decide)]
    change intervalReg (intervalPut s3 6 w6) 6 = w6
    rw [intervalReg_put, ite_eq_left rfl]
  · change intervalReg (intervalPut s5 7 w7) 7 = w7
    rw [intervalReg_put, ite_eq_left rfl]
  · intro r hr5 hr6 hr7
    change intervalReg s6 r = intervalReg s r
    rw [fr6 r hr7, fr4 r hr6, fr2 r hr5]

end PaperB.RamProgram
