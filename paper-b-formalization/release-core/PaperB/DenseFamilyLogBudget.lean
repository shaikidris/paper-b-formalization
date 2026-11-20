import PaperB.DenseFamilyVertexBudget
import PaperB.OracleContract

namespace PaperB.RankedDenseLocal

open Digraph EX16Assembly StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open DenseQuotientRows DenseQuotientLocalOrder

section

private theorem sum_ofFn_le {n : Nat} (a b : Fin n → Nat)
    (h : ∀ i, a i ≤ b i) :
    (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, Function.comp_def]
    exact Nat.add_le_add (h 0)
      (ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ))

private theorem sum_ofFn_add {n : Nat} (a b : Fin n → Nat) :
    (List.ofFn (fun i => a i + b i)).sum =
      (List.ofFn a).sum + (List.ofFn b).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, Function.comp_def]
    rw [ih (fun i => a i.succ) (fun i => b i.succ)]
    omega

private theorem sum_ofFn_one (n : Nat) :
    (List.ofFn (fun _ : Fin n => 1)).sum = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, Function.comp_def, ih] <;> omega

private theorem sum_ofFn_scale {n : Nat} (k : Nat) (a : Fin n → Nat) :
    (List.ofFn (fun i => k * a i)).sum = k * (List.ofFn a).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons, Function.comp_def, Nat.mul_add]
    rw [ih (fun i => a i.succ)]

private theorem le_sum_of_mem {x : Nat} {xs : List Nat} (h : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with he | ht
    · omega
    · have htail := ih ht
      omega

private theorem le_sum_ofFn_at {n : Nat} (a : Fin n → Nat) (i : Fin n) :
    a i ≤ (List.ofFn a).sum := by
  apply le_sum_of_mem
  apply List.mem_iff_getElem.mpr
  refine ⟨i.val, ?_, ?_⟩
  · simpa only [List.length_ofFn] using i.isLt
  · simp only [List.getElem_ofFn] <;> rfl

private theorem logWidth_mono {a b : Nat} (h : a ≤ b) :
    OracleContract.L a ≤ OracleContract.L b := by
  have hs : a + 1 ≤ b + 1 := Nat.add_le_add_right h 1
  have hl : Nat.log2 (a + 1) ≤ Nat.log2 (b + 1) := by
    exact (Nat.le_log2 (by omega : b + 1 ≠ 0)).mpr
      (Nat.le_trans (Nat.log2_self_le (by omega)) hs)
  exact Nat.add_le_add_right hl 1

private theorem sum_log_bound {n : Nat} (v w cost : Fin n → Nat) (c B : Nat)
    (hv : ∀ i, v i ≤ n)
    (hw : (List.ofFn w).sum ≤ B)
    (hc : ∀ i, cost i ≤ c * w i * OracleContract.L (v i)) :
    (List.ofFn cost).sum ≤ c * B * OracleContract.L n := by
  have hpoint (i : Fin n) : cost i ≤ (c * OracleContract.L n) * w i := by
    calc
      cost i ≤ c * w i * OracleContract.L (v i) := hc i
      _ ≤ c * w i * OracleContract.L n :=
        Nat.mul_le_mul_left _ (logWidth_mono (hv i))
      _ = (c * OracleContract.L n) * w i := by ac_rfl
  calc
    (List.ofFn cost).sum ≤
        (List.ofFn (fun i => (c * OracleContract.L n) * w i)).sum :=
      sum_ofFn_le cost _ hpoint
    _ = (c * OracleContract.L n) * (List.ofFn w).sum :=
      sum_ofFn_scale (c * OracleContract.L n) w
    _ ≤ (c * OracleContract.L n) * B := Nat.mul_le_mul_left _ hw
    _ = c * B * OracleContract.L n := by ac_rfl

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r)
variable {buckets : ChildLists q.count} (rows : DenseQuotientRows.Layout buckets)
variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
variable (p : KahnLocals q rows childOK)
variable (progress : ∀ x y : Fin g.vertexCount,
  g.HasArc x y → p.bound.rankRead x < p.bound.rankRead y)
variable (injective : ∀ ⦃x y : Fin g.vertexCount⦄,
  p.bound.rankRead x = p.bound.rankRead y → x = y)
variable (spec : ParentSpec g r q.parent)

local notation "installed" => ofPrepared q rows childOK p progress injective spec

private theorem installed_vertex_sum :
    (List.ofFn (fun u : Fin q.count => ((installed).get u).graph.vertexCount)).sum =
      (installed).totalVertices := by
  change _ =
    ((List.ofFn (id : Fin q.count → Fin q.count)).map
      (fun u => ((installed).get u).graph.vertexCount)).sum
  rw [List.map_ofFn] <;> rfl

/-- Remove one root bundle per owner. The exact canonical budget leaves
`q.count - 1` child copies across the family, so any one owner has at most
that many child copies in addition to its own root bundle. -/
theorem installed_vertexCount_le_reachable
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read)
    (u : Fin q.count) :
    ((installed).get u).graph.vertexCount ≤ q.count := by
  let v : Fin q.count → Nat := fun i => ((installed).get i).graph.vertexCount
  let kids : Fin q.count → Nat := fun i => v i - 1
  have hsplit (i : Fin q.count) : 1 + kids i = v i := by
    have hpos : 0 < v i := by
      change 0 < ((installed).get i).graph.vertexCount
      rw [get_ofPrepared_vertexCount, rows.length_exact] <;> omega
    dsimp only [kids]
    omega
  have htotal : (List.ofFn v).sum = q.count + (q.count - 1) :=
    (installed_vertex_sum q rows childOK p progress injective spec).trans
      (totalVertices_ofPrepared_exact q rows childOK p progress injective spec hg)
  have hdecomp : (List.ofFn v).sum = q.count + (List.ofFn kids).sum := by
    calc
      (List.ofFn v).sum = (List.ofFn (fun i => 1 + kids i)).sum :=
        congrArg (fun f : Fin q.count → Nat => (List.ofFn f).sum)
          (funext fun i => (hsplit i).symm)
      _ = (List.ofFn (fun _ : Fin q.count => 1)).sum + (List.ofFn kids).sum :=
        sum_ofFn_add (fun _ : Fin q.count => 1) kids
      _ = q.count + (List.ofFn kids).sum := by rw [sum_ofFn_one]
  have hkids : (List.ofFn kids).sum = q.count - 1 := by omega
  have huKids := le_sum_ofFn_at kids u
  have huSplit := hsplit u
  have hn : 0 < q.count := by have hi := u.isLt; omega
  change v u ≤ q.count
  omega

/-- One uniform per-owner selected-site certificate gives one sum bound
in terms of the reachable original vertex count. -/
theorem selected_sites_sum_ofPrepared_le
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read)
    (c : Nat) (selected : Fin q.count → Nat)
    (hselected : ∀ u,
      selected u ≤ c * ((installed).get u).graph.vertexCount *
        OracleContract.L ((installed).get u).graph.vertexCount) :
    (List.ofFn selected).sum ≤ (2 * c) * q.count * OracleContract.L q.count := by
  let v : Fin q.count → Nat := fun u => ((installed).get u).graph.vertexCount
  have hv : ∀ u, v u ≤ q.count :=
    installed_vertexCount_le_reachable q rows childOK p progress injective spec hg
  have hbudget : (List.ofFn v).sum ≤ 2 * q.count := by
    calc
      (List.ofFn v).sum = (installed).totalVertices :=
        installed_vertex_sum q rows childOK p progress injective spec
      _ ≤ 2 * q.count :=
        totalVertices_ofPrepared_le q rows childOK p progress injective spec hg
  calc
    (List.ofFn selected).sum ≤ c * (2 * q.count) * OracleContract.L q.count :=
      sum_log_bound v v selected c (2 * q.count) hv hbudget hselected
    _ = (2 * c) * q.count * OracleContract.L q.count := by ac_rfl

/-- Aggregate any verified per-owner build charges for the installed graphs.
This consumes the local charge witnesses; it does not construct them or
certify a complete compiler. -/
theorem build_log_cost_sum_ofPrepared_le
    (hg : HasCanonicalBuckets rows q.input.root q.input.parent.read)
    (c : Nat) (cost : Fin q.count → Nat)
    (hcost : ∀ u,
      cost u ≤ c * (((installed).get u).graph.vertexCount +
        ((installed).get u).graph.arcCount) *
        OracleContract.L ((installed).get u).graph.vertexCount) :
    (List.ofFn cost).sum ≤
      (2 * c) * (q.count + g.arcCount) * OracleContract.L q.count := by
  let v : Fin q.count → Nat := fun u => ((installed).get u).graph.vertexCount
  let a : Fin q.count → Nat := fun u => ((installed).get u).graph.arcCount
  have hv : ∀ u, v u ≤ q.count :=
    installed_vertexCount_le_reachable q rows childOK p progress injective spec hg
  have hbudget :
      (List.ofFn (fun u => v u + a u)).sum ≤ 2 * q.count + g.arcCount := by
    calc
      (List.ofFn (fun u => v u + a u)).sum =
          (List.ofFn v).sum + (List.ofFn a).sum := sum_ofFn_add v a
      _ = (installed).totalVertices + (List.ofFn a).sum :=
        congrArg (fun s : Nat => s + (List.ofFn a).sum)
          (installed_vertex_sum q rows childOK p progress injective spec)
      _ ≤ 2 * q.count + g.arcCount :=
        totalVertices_add_totalArcs_ofPrepared_le
          q rows childOK p progress injective spec hg
  have horig : 2 * q.count + g.arcCount ≤ 2 * (q.count + g.arcCount) := by
    omega
  calc
    (List.ofFn cost).sum ≤
        c * (2 * q.count + g.arcCount) * OracleContract.L q.count :=
      sum_log_bound v (fun u => v u + a u) cost c
        (2 * q.count + g.arcCount) hv hbudget hcost
    _ ≤ c * (2 * (q.count + g.arcCount)) * OracleContract.L q.count :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c horig)
    _ = (2 * c) * (q.count + g.arcCount) * OracleContract.L q.count := by
      ac_rfl

end

end PaperB.RankedDenseLocal
