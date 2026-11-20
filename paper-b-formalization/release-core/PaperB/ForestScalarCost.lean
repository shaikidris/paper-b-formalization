import PaperB.ForestHead

set_option autoImplicit false

namespace StepCostCertificate

universe u

private theorem extendCostBound (base rate n cost extra : Nat)
    (hcost : cost ≤ base + n * rate) (hextra : extra ≤ rate) :
    cost + extra ≤ base + n.succ * rate := by
  simpa only [Nat.succ_mul, Nat.add_assoc] using
    (Nat.add_le_add hcost hextra)

def listAny {α : Type u} (test : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => if test x then true else listAny test xs

def meteredListAny {α : Type u} (probe : α → Bool × Nat)
    (emptyCost nonemptyCost : Nat) : List α → Bool × Nat
  | [] => (false, emptyCost)
  | x :: xs =>
      let p := probe x
      if p.1 then
        (true, nonemptyCost + p.2)
      else
        let rest := meteredListAny probe emptyCost nonemptyCost xs
        (rest.1, rest.2 + (nonemptyCost + p.2))

theorem meteredListAny_output {α : Type u} (probe : α → Bool × Nat)
    (emptyCost nonemptyCost : Nat) (xs : List α) :
    (meteredListAny probe emptyCost nonemptyCost xs).1 =
      listAny (fun x => (probe x).1) xs := by
  induction xs with
  | nil => simp [meteredListAny, listAny]
  | cons x xs ih =>
      cases hp : (probe x).1 <;>
        simp [meteredListAny, listAny, hp, ih]

theorem meteredListAny_cost_le {α : Type u} (probe : α → Bool × Nat)
    (emptyCost nonemptyCost elemCap : Nat)
    (hcap : ∀ x : α, (probe x).2 ≤ elemCap) (xs : List α) :
    (meteredListAny probe emptyCost nonemptyCost xs).2 ≤
      emptyCost + xs.length * (nonemptyCost + elemCap) := by
  induction xs with
  | nil => simp [meteredListAny]
  | cons x xs ih =>
      have hprobe : nonemptyCost + (probe x).2 ≤ nonemptyCost + elemCap :=
        Nat.add_le_add_left (hcap x) nonemptyCost
      cases hp : (probe x).1 with
      | false =>
          simpa [meteredListAny, hp] using
            (extendCostBound emptyCost (nonemptyCost + elemCap) xs.length
              (meteredListAny probe emptyCost nonemptyCost xs).2
              (nonemptyCost + (probe x).2) ih hprobe)
      | true =>
          simpa [meteredListAny, hp] using
            (extendCostBound emptyCost (nonemptyCost + elemCap) xs.length
              0 (nonemptyCost + (probe x).2) (Nat.zero_le _) hprobe)

/-- Returns the final lower bound. Arguments after `test` are fuel, lo, and hi. -/
def binarySearch (test : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then
        lo
      else
        let mid := lo + (hi - lo) / 2
        if test mid then
          binarySearch test fuel mid hi
        else
          binarySearch test fuel lo mid

def meteredBinarySearch (probe : Nat → Bool × Nat)
    (stopCost stepCost : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, lo, _ => (lo, stopCost)
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then
        (lo, stopCost)
      else
        let mid := lo + (hi - lo) / 2
        let p := probe mid
        let next :=
          if p.1 then
            meteredBinarySearch probe stopCost stepCost fuel mid hi
          else
            meteredBinarySearch probe stopCost stepCost fuel lo mid
        (next.1, next.2 + (stepCost + p.2))

theorem meteredBinarySearch_output (probe : Nat → Bool × Nat)
    (stopCost stepCost fuel lo hi : Nat) :
    (meteredBinarySearch probe stopCost stepCost fuel lo hi).1 =
      binarySearch (fun n => (probe n).1) fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => simp [meteredBinarySearch, binarySearch]
  | succ fuel ih =>
      by_cases hstop : hi ≤ lo + 1
      · simp [meteredBinarySearch, binarySearch, hstop]
      · cases hp : (probe (lo + (hi - lo) / 2)).1 <;>
          simp [meteredBinarySearch, binarySearch, hstop, hp, ih]

theorem meteredBinarySearch_cost_le (probe : Nat → Bool × Nat)
    (stopCost stepCost probeCap : Nat)
    (hcap : ∀ n : Nat, (probe n).2 ≤ probeCap) (fuel lo hi : Nat) :
    (meteredBinarySearch probe stopCost stepCost fuel lo hi).2 ≤
      stopCost + fuel * (stepCost + probeCap) := by
  induction fuel generalizing lo hi with
  | zero => simp [meteredBinarySearch]
  | succ fuel ih =>
      by_cases hstop : hi ≤ lo + 1
      · simp [meteredBinarySearch, hstop]
      · have nextBound (a b : Nat) :
            (meteredBinarySearch probe stopCost stepCost fuel a b).2 +
                (stepCost + (probe (lo + (hi - lo) / 2)).2) ≤
              stopCost + fuel.succ * (stepCost + probeCap) :=
          extendCostBound stopCost (stepCost + probeCap) fuel
            (meteredBinarySearch probe stopCost stepCost fuel a b).2
            (stepCost + (probe (lo + (hi - lo) / 2)).2)
            (ih a b) (Nat.add_le_add_left (hcap (lo + (hi - lo) / 2)) stepCost)
        cases hp : (probe (lo + (hi - lo) / 2)).1 with
        | false =>
            simpa [meteredBinarySearch, hstop, hp] using
              (nextBound lo (lo + (hi - lo) / 2))
        | true =>
            simpa [meteredBinarySearch, hstop, hp] using
              (nextBound (lo + (hi - lo) / 2) hi)

end StepCostCertificate

namespace PaperB.ForestHead

open StepCostCertificate

/-- The scalar list meter follows the production scan and charges the visited
cells and ancestry calls. Only a successful scan reaches the empty-list case. -/
theorem scan_scalar_meter {α : Type} (test : α → Bool × Nat)
    (emptyCost testCost ancestryCost : Nat) (xs : List α) :
    meteredListAny (fun x => (!(test x).1, (test x).2 * ancestryCost))
        emptyCost testCost xs =
      let r := scan test xs
      (!r.ok, (if r.ok then emptyCost else 0) +
        r.tests * testCost + r.ancestryCalls * ancestryCost) := by
  induction xs with
  | nil => simp [meteredListAny, scan]
  | cons x xs ih =>
    cases h : (test x).1 with
    | false => simp [meteredListAny, scan, h]
    | true =>
      simp only [meteredListAny, scan, h, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rw [ih]
      dsimp only
      simp only [Nat.add_mul, Nat.one_mul, Prod.mk.injEq, true_and]
      omega

/-- The search meter uses the same midpoint tests and final cut as the
production search. The named unit costs are parameters of this model. -/
theorem search_scalar_meter (p : Nat → Probe)
    (stopCost stepCost testCost depthCost ancestryCost fuel lo hi : Nat) :
    meteredBinarySearch
      (fun i => let q := p i
                (q.ok, q.tests * testCost + q.depthCalls * depthCost +
                  q.ancestryCalls * ancestryCost))
      stopCost stepCost fuel lo hi =
      let r := measuredSearch p fuel lo hi
      (r.cut, stopCost + r.comparisons * stepCost + r.tests * testCost +
        r.depthCalls * depthCost + r.ancestryCalls * ancestryCost) := by
  induction fuel generalizing lo hi with
  | zero => simp [meteredBinarySearch, measuredSearch]
  | succ fuel ih =>
    by_cases hstop : hi ≤ lo + 1
    · simp [meteredBinarySearch, measuredSearch, hstop]
    · cases hok : (p (lo + (hi - lo) / 2)).ok with
      | false =>
        simp only [meteredBinarySearch, measuredSearch, hstop, hok,
          ite_false, Bool.false_eq_true, addProbe]
        rw [ih]
        simp only [Nat.add_mul, Nat.one_mul, Prod.mk.injEq, true_and]
        omega
      | true =>
        simp only [meteredBinarySearch, measuredSearch, hstop, hok, ite_false,
          ite_true, addProbe]
        rw [ih]
        simp only [Nat.add_mul, Nat.one_mul, Prod.mk.injEq, true_and]
        omega

end PaperB.ForestHead
