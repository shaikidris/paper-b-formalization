import PaperB.ForestArrayMerge
import PaperB.PairDictionary

open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open PaperB.PairLookup.KeyMerge.Workspace (Span Frame)

namespace PaperB.PairDictionary.FixedBank

@[inline] def bankBase (k : Nat) (bank : Bool) : Nat :=
  if bank then k else 0

def InBank {k : Nat} (s : Span k) (bank : Bool) (q : Nat) : Prop :=
  bankBase k bank + s.base ≤ q ∧
    q < bankBase k bank + s.base + s.width

def InSpan {k : Nat} (s : Span k) (q : Nat) : Prop :=
  InBank s false q ∨ InBank s true q

private theorem inSpan_of_inBank {k : Nat} {s : Span k} {b : Bool}
    {q : Nat} (h : InBank s b q) : InSpan s q := by
  cases b
  · exact Or.inl h
  · exact Or.inr h

private theorem inSpan_mono {k : Nat} {s t : Span k} {q : Nat}
    (hbase : s.base ≤ t.base)
    (hend : t.base + t.width ≤ s.base + s.width)
    (h : InSpan t q) : InSpan s q := by
  have lift : ∀ b : Bool, InBank t b q → InBank s b q := by
    intro b hb
    unfold InBank at hb ⊢
    omega
  rcases h with h | h
  · exact Or.inl (lift false h)
  · exact Or.inr (lift true h)

private theorem left_inSpan {k : Nat} (s : Span k) {q : Nat}
    (h : InSpan s.left q) : InSpan s q :=
  inSpan_mono (s := s) (t := s.left) (Nat.le_refl s.base)
    (by
      change s.base + s.width / 2 ≤ s.base + s.width
      omega) h

private theorem right_inSpan {k : Nat} (s : Span k) {q : Nat}
    (h : InSpan s.right q) : InSpan s q :=
  inSpan_mono (s := s) (t := s.right)
    (by
      change s.base ≤ s.base + s.width / 2
      omega)
    (by
      change s.base + s.width / 2 + (s.width - s.width / 2) ≤
        s.base + s.width
      omega) h

theorem right_input_outside_left {k : Nat} (s : Span k) {q : Nat}
    (h : InBank s.right false q) : ¬ InSpan s.left q := by
  have hf := s.fits
  simp [InBank, bankBase] at h
  change s.base + s.width / 2 ≤ q ∧
    q < s.base + s.width / 2 + (s.width - s.width / 2) at h
  intro hleft
  rcases hleft with hleft | hleft
  · simp [InBank, bankBase] at hleft
    change s.base ≤ q ∧ q < s.base + s.width / 2 at hleft
    omega
  · simp [InBank, bankBase] at hleft
    change k + s.base ≤ q ∧ q < k + s.base + s.width / 2 at hleft
    omega

private theorem inputBound {k : Nat} (s : Span k) (h : 0 < s.width) :
    s.base < 2 * k := by
  have hf := s.fits
  omega

private theorem outputBound {k : Nat} (s : Span k) (dst : Bool)
    (h : 0 < s.width) : bankBase k dst + s.base < 2 * k := by
  have hf := s.fits
  cases dst <;> simp [bankBase] <;> omega

private theorem dstAddr_eq {k : Nat} (p : ArrayMerge.Plan k)
    (dst : Bool) (h : p.source = !dst) (v : Nat) :
    p.dstAddr v = bankBase k dst + (p.outBase + v) := by
  cases dst <;> simp [ArrayMerge.Plan.dstAddr, bankBase, h]

/-- Peak live sort frames. The parent stays live, but the children run
sequentially, so their peaks combine by `max`. This certificate is erased. -/
inductive Calls {k : Nat} : Nat → Span k → Nat → Prop where
  | leaf {fuel : Nat} {s : Span k} (h : s.width ≤ 1) :
      Calls fuel s 1
  | fork {fuel : Nat} {s : Span k} {l r : Nat} (h : 1 < s.width) :
      Calls fuel s.left l → Calls fuel s.right r →
      Calls (fuel + 1) s (max l r + 1)

theorem Calls.peak_le {k fuel peak : Nat} {s : Span k}
    (h : Calls fuel s peak) : peak ≤ fuel + 1 := by
  induction h with
  | leaf _ => omega
  | fork _ _ _ ihl ihr =>
    simp only [Nat.max_def] <;> split <;> omega

/-- The valid output occupies the first `count` slots of `s` in `dst`.
The frame condition applies to both banks. -/
structure SortResult {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (orig : Array Key) (hOrig : orig.size = 2 * k) where
  bank : Array Key
  count : Nat
  size_eq : bank.size = 2 * k
  count_le : count ≤ s.width
  count_pos : 0 < s.width → 0 < count
  leafCopy : ∀ h : s.width = 1,
    ArrayMerge.slot bank size_eq (bankBase k dst + s.base)
        (outputBound s dst (by omega)) =
      ArrayMerge.slot orig hOrig s.base (inputBound s (by omega))
  frame : ∀ (q : Nat) (hq : q < 2 * k), ¬ InSpan s q →
    ArrayMerge.slot bank size_eq q hq = ArrayMerge.slot orig hOrig q hq
  calls : ∃ peak : Nat, Calls fuel s peak

theorem SortResult.count_eq_zero_iff {k fuel : Nat} {s : Span k}
    {dst : Bool} {a : Array Key} {ha : a.size = 2 * k}
    (r : SortResult fuel s dst a ha) : r.count = 0 ↔ s.width = 0 := by
  constructor
  · intro hc
    by_cases hw : s.width = 0
    · exact hw
    · have hp := r.count_pos (by omega)
      omega
  · intro hw
    have hc := r.count_le
    omega

/-- The left call cannot change any bank-zero input of the pending right call. -/
theorem SortResult.pendingRight {k fuel : Nat} {s : Span k} {dst : Bool}
    {a : Array Key} {ha : a.size = 2 * k}
    (l : SortResult fuel s.left dst a ha)
    (q : Nat) (hq : q < 2 * k) (h : InBank s.right false q) :
    ArrayMerge.slot l.bank l.size_eq q hq = ArrayMerge.slot a ha q hq :=
  l.frame q hq (right_input_outside_left s h)

private def runLeaf {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 1) :
    SortResult fuel s dst a ha :=
  if hp : 0 < s.width then
    let j : Nat := bankBase k dst + s.base
    have hj : j < 2 * k := outputBound s dst hp
    have hjA : j < a.size := by omega
    let x : Key := ArrayMerge.slot a ha s.base (inputBound s hp)
    let b : Array Key := a.set j x hjA
    have hb : b.size = 2 * k := by simpa [b] using ha
    { bank := b
      count := 1
      size_eq := hb
      count_le := by omega
      count_pos := fun _ => Nat.zero_lt_succ 0
      leafCopy := by
        intro _
        change b[j]'(by omega) = x
        first
        | simpa [b]
        | simp [b, Array.getElem_set]
      frame := by
        intro q hq avoid
        have hin : InBank s dst j := by
          change j ≤ j ∧ j < j + s.width
          omega
        have hne : j ≠ q := by
          intro e
          exact avoid (inSpan_of_inBank (e ▸ hin))
        change b[q]'(by omega) = a[q]'(by omega)
        first
        | simpa [b, hne, Ne.symm hne]
        | simp [b, Array.getElem_set, hne, Ne.symm hne]
      calls := ⟨1, Calls.leaf hw⟩ }
  else
    { bank := a
      count := 0
      size_eq := ha
      count_le := Nat.zero_le _
      count_pos := by intro h; exact False.elim (hp h)
      leafCopy := by intro h; omega
      frame := by intro _ _ _; rfl
      calls := ⟨1, Calls.leaf hw⟩ }

/-- One structural recursion on fuel. Destructuring each child result
before the next call threads the array forward without retaining a second
bank handle for the parent. There are no bulk copies or runtime split lists. -/
def runSpan {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ fuel) :
    SortResult fuel s dst a ha :=
  match fuel with
  | 0 =>
    runLeaf 0 s dst a ha (by simpa using hw)
  | n + 1 =>
    if hs : s.width ≤ 1 then
      runLeaf (n + 1) s dst a ha hs
    else
      have hsplit : 1 < s.width := by omega
      have hpow : s.width ≤ 2 ^ n * 2 := by
        simpa only [Nat.pow_succ] using hw
      have hwL : s.left.width ≤ 2 ^ n := by
        change s.width / 2 ≤ 2 ^ n
        omega
      have hwR : s.right.width ≤ 2 ^ n := by
        change s.width - s.width / 2 ≤ 2 ^ n
        omega
      let ⟨lb, lc, hlb, hlc, hlpos, _, hlframe, hlcalls⟩ :=
        runSpan n s.left (!dst) a ha hwL
      let ⟨rb, rc, hrb, hrc, _, _, hrframe, hrcalls⟩ :=
        runSpan n s.right (!dst) lb hlb hwR
      have hL : lc ≤ s.width / 2 := hlc
      have hR : rc ≤ s.width - s.width / 2 := hrc
      let p : ArrayMerge.Plan k :=
        { source := !dst
          leftBase := s.base
          leftLen := lc
          rightBase := s.base + s.width / 2
          rightLen := rc
          outBase := s.base
          outWidth := s.width
          separated := by omega
          rightFits := by
            have hf := s.fits
            omega
          outFits := s.fits
          room := by omega }
      let m : ArrayMerge.Result p rb hrb := ArrayMerge.runPacked p rb hrb
      { bank := m.bank
        count := m.count
        size_eq := m.size_eq
        count_le := by
          obtain ⟨_, _, _, _, _, hfit, _⟩ := m.certified
          exact hfit
        count_pos := by
          intro _
          have hwLpos : 0 < s.left.width := by
            change 0 < s.width / 2
            omega
          have hl : 0 < lc := hlpos hwLpos
          obtain ⟨_, _, _, _, _, _, _, hcharge, _⟩ := m.certified
          change lc + rc ≤ 2 * m.count at hcharge
          omega
        leafCopy := by intro h; omega
        frame := by
          intro q hq avoid
          have hm : ArrayMerge.slot m.bank m.size_eq q hq =
              ArrayMerge.slot rb hrb q hq := by
            obtain ⟨_, _, _, t, _⟩ := m.certified
            apply t.frame hrb q hq
            intro v hv he
            have hc : m.count ≤ s.width := t.fits
            have hd : p.dstAddr v = bankBase k dst + (s.base + v) :=
              dstAddr_eq p dst rfl v
            apply avoid
            apply inSpan_of_inBank (b := dst)
            unfold InBank
            omega
          exact hm.trans
            ((hrframe q hq (fun h => avoid (right_inSpan s h))).trans
              (hlframe q hq (fun h => avoid (left_inSpan s h))))
        calls := by
          obtain ⟨lp, hLcalls⟩ := hlcalls
          obtain ⟨rp, hRcalls⟩ := hrcalls
          exact ⟨max lp rp + 1, Calls.fork hsplit hLcalls hRcalls⟩ }
termination_by structural fuel

/-- Run on a backing array of exactly `2 * k` slots. Bank zero supplies
the input, and `dst` selects the bank that receives the output prefix. -/
def runPacked (k : Nat) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) :
    SortResult (ceilBinaryLog k) (Span.root k) dst a ha :=
  runSpan (ceilBinaryLog k) (Span.root k) dst a ha (Frame.root k).width_budget

theorem runPacked_live_frames (k : Nat) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) :
    ∃ peak : Nat, Calls (ceilBinaryLog k) (Span.root k) peak ∧
      peak ≤ ceilBinaryLog k + 1 := by
  obtain ⟨peak, h⟩ := (runPacked k dst a ha).calls
  exact ⟨peak, h, h.peak_le⟩

end PaperB.PairDictionary.FixedBank
