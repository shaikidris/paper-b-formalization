import PaperB.ExitLinearSchedule
import PaperB.ExitPhysicalPass

set_option maxHeartbeats 2000000

namespace EX42.ArraySweep.Packed

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite PaperB.ExitPhysicalOneSlot

universe u v

structure Packing (n m slots : Nat) (M : Type u) where
  addr : Fin m → Fin slots
  view : Fin m → Stored → M
  job : Fin n → Fin m → M → Job

def Packing.jobAt {n m slots : Nat} {M : Type u}
    (K : Packing n m slots M) (y : Fin n) (i : Fin m) (x : M) : Job :=
  { K.job y i x with slot := (K.addr i).val }

structure PhysicalState (n bits words : Nat) (B : Type v) where
  bank : WriteResult bits words
  bases : Slots B n

variable {n m bits words slots : Nat} {M : Type u} {B : Type v}
variable {P : Plan n m} {D : Reads n m}

/-- Reference states are indexed by visits, not ranks. `occ 0` may contain
seeded records. The bridges translate logical read permissions to occupancy. -/
structure Contract (tags : TagsFit bits) (S : Schedule P) (C : Callbacks D M B)
    (K : Packing n m slots M) (occ : Nat → Nat → Prop) (old : Nat → Store)
    (wm : Fin m → M) (wb : Fin n → B) : Prop where
  ready : Ready P D
  correct : Exact P C wm wb
  prior : ∀ (a : Fin n) (i : Fin m), P.mapBefore (P.rank (S.vertex a)) i →
    occ a.val (K.addr i).val
  staged : ∀ (a : Fin n) (i : Fin m),
    (P.mapBefore (P.rank (S.vertex a)) i ∨ P.observe (S.vertex a) i = true) →
    occ (a.val + 1) (K.addr i).val
  values : ∀ k i, occ k (K.addr i).val → K.view i (old k (K.addr i).val) = wm i
  keep : ∀ a : Fin n, S.mapSlot.read (S.vertex a) = none →
    occ (a.val + 1) = occ a.val ∧ old (a.val + 1) = old a.val
  put : ∀ (a : Fin n) (i : Fin m), S.mapSlot.read (S.vertex a) = some i →
    let j := K.jobAt (S.vertex a) i (wm i)
    PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) ∧
      occ (a.val + 1) = j.occupy (occ a.val) ∧
      old (a.val + 1) = j.overlay (old a.val)

structure Inv (tags : TagsFit bits) (base : Word bits) (L : Layout base words slots)
    (S : Schedule P) (occ : Nat → Nat → Prop) (old : Nat → Store)
    (wb : Fin n → B) (k : Nat) (s : PhysicalState n bits words B) : Prop where
  maps : OccupiedExact tags base L s.bank (occ k) (old k)
  bases : ∀ a : Fin n,
    Cell (a.val < k) (s.bases.read (S.vertex a)) (wb (S.vertex a))

variable (tags : TagsFit bits) (base : Word bits) (L : Layout base words slots)
variable (K : Packing n m slots M)

/-- A decoded callback value can retain the block, but not the bank via
the decoder's cell reader. -/
private def readMap (bank : WriteResult bits words) (i : Fin m) : M :=
  let k := K.addr i
  let cells := Array.ofFn (readStoredBlockAt bank.mem base k.val
    (L.addrAt k.isLt) (bank.le_size (L.memAt k.isLt)))
  K.view i ((storedCodec tags).decode (fun p : Fin 18 =>
    cells[p.val]'(by simpa [cells] using p.isLt)))

private theorem readMap_eq (bank : WriteResult bits words) (i : Fin m) :
    readMap tags base L K bank i =
      K.view i (readSlot tags base L bank (K.addr i).val (K.addr i).isLt) := by
  unfold readMap readSlot readStoredAt
  apply congrArg (K.view i)
  apply congrArg (storedCodec tags).decode
  funext p
  simp only [Array.getElem_ofFn]

variable (S : Schedule P) (C : Callbacks D M B)
variable {occ : Nat → Nat → Prop} {old : Nat → Store}
variable {wm : Fin m → M} {wb : Fin n → B}

section
variable {tags base L K S C}

private theorem base_ok {a : Fin n} {s : PhysicalState n bits words B}
    (h : Inv tags base L S occ old wb a.val s) (z : Fin n)
    (hz : P.rank z < P.rank (S.vertex a)) :
    s.bases.read z = some (wb z) := by
  obtain ⟨b, rfl⟩ := S.covers z
  exact (h.bases b).1 ((S.rank_lt_rank_iff b a).mp hz)

private theorem map_ok (H : Contract tags S C K occ old wm wb)
    {k : Nat} {bank : WriteResult bits words}
    (h : OccupiedExact tags base L bank (occ k) (old k))
    (i : Fin m) (hi : occ k (K.addr i).val) :
    some (readMap tags base L K bank i) = some (wm i) := by
  obtain ⟨_, he⟩ := h _ hi
  rw [readMap_eq, he, H.values k i hi]

end

private theorem read_write {α : Type v} (s : Slots α n) (a b : Fin n) (x : α) :
    (s.write a x).read b = if b = a then some x else s.read b := by
  by_cases h : b = a
  · subst b
    simp [Slots.read, Slots.write, Array.getElem_set]
  · have hv : b.val ≠ a.val := fun e => h (Fin.ext e)
    simp [Slots.read, Slots.write, Array.getElem_set, h, Ne.symm h, hv, Ne.symm hv]

private def stage (H : Contract tags S C K occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) :
    {bank : WriteResult bits words //
      OccupiedExact tags base L bank (occ (a.val + 1)) (old (a.val + 1))} := by
  cases ho : S.mapSlot.read (S.vertex a) with
  | none =>
    have t := H.keep a ho
    exact ⟨s.bank, by rw [t.1, t.2]; exact h.maps⟩
  | some i =>
    let rb := fun (p : Fin n) (_ : D.installBase i p) => s.bases.read p
    let rm := fun (j : Fin m) (_ : D.installMap i j) =>
      some (readMap tags base L K s.bank j)
    let j := K.jobAt (S.vertex a) i (C.install (S.vertex a) i rb rm)
    have first := (S.slot_exact (S.vertex a) i).mp ho
    have r := H.ready.install (S.vertex a) i first
    have he : C.install (S.vertex a) i rb rm = wm i :=
      H.correct.install (S.vertex a) i rb rm first
        (fun p hp => base_ok h p (r.1 p hp))
        (fun q hq => map_ok H h.maps q (H.prior a q (r.2 q hq)))
    have hj : j = K.jobAt (S.vertex a) i (wm i) :=
      congrArg (K.jobAt (S.vertex a) i) he
    have t := H.put a i ho
    have rj : PaperB.ExitPhysicalPass.Ready tags slots j (occ a.val) (old a.val) := by
      rw [hj]
      exact t.1
    have fit := buildFromBank_fit tags base L s.bank j h.maps rj.deps rj.fit
    refine ⟨PaperB.ExitPhysicalOneSlot.step tags base L s.bank j rj.bound fit, ?_⟩
    rw [t.2.1, t.2.2, ← hj]
    exact step_exact tags base L s.bank j rj.bound fit h.maps rj.fresh rj.deps

/-- The installer sees the input bank; the base builder sees the staged bank.
Both read the same input base column. -/
def event (H : Contract tags S C K occ old wm wb)
    (a : Fin n) (s : PhysicalState n bits words B)
    (h : Inv tags base L S occ old wb a.val s) :
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb (a.val + 1) t} :=
  let bank := stage tags base L K S C H a s h
  let rb := fun (z : Fin n) (_ : D.vertexBase (S.vertex a) z) => s.bases.read z
  let rm := fun (i : Fin m) (_ : D.vertexMap (S.vertex a) i) =>
    some (readMap tags base L K bank.val i)
  let value := C.base (S.vertex a) rb rm
  ⟨⟨bank.val, s.bases.write (S.vertex a) value⟩, by
    have r := H.ready.vertex (S.vertex a)
    have hv : value = wb (S.vertex a) :=
      H.correct.vertex (S.vertex a) rb rm
        (fun z hz => base_ok h z (r.1 z hz))
        (fun i hi => map_ok H bank.property i (H.staged a i (r.2 i hi)))
    refine ⟨bank.property, ?_⟩
    intro b
    change Cell (b.val < a.val + 1)
      ((s.bases.write (S.vertex a) value).read (S.vertex b)) (wb (S.vertex b))
    rw [read_write]
    by_cases e : b = a
    · subst b
      simp [Cell, hv, Nat.lt_succ_self]
    · have hn : S.vertex b ≠ S.vertex a := fun eq => e (S.vertex_inj eq)
      have hne : b.val ≠ a.val := fun eq => e (Fin.ext eq)
      have hp : b.val < a.val + 1 ↔ b.val < a.val := by omega
      simpa only [if_neg hn, hp] using h.bases b⟩

/-- One tail call per order-array entry. Contracts and prefix proofs erase. -/
def foldTo (H : Contract tags S C K occ old wm wb) (dst : Nat) (hd : dst ≤ n) :
    (fuel start : Nat) → start + fuel = dst → (s : PhysicalState n bits words B) →
    Inv tags base L S occ old wb start s →
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb dst t}
  | 0, start, hk, s, h => ⟨s, by rw [← hk, Nat.add_zero]; exact h⟩
  | fuel + 1, start, hk, s, h =>
    let a : Fin n := ⟨start, by omega⟩
    let t := event tags base L K S C H a s h
    foldTo H dst hd fuel (start + 1) (by omega) t.val t.property
termination_by structural fuel => fuel

def runPrefix (H : Contract tags S C K occ old wm wb) (j : Nat) (hj : j ≤ n)
    (bank : WriteResult bits words)
    (hb : OccupiedExact tags base L bank (occ 0) (old 0)) :
    {t : PhysicalState n bits words B // Inv tags base L S occ old wb j t} :=
  foldTo tags base L K S C H j hj j 0 (Nat.zero_add j) ⟨bank, Slots.empty B n⟩
    ⟨hb, fun a => ⟨fun ha => (Nat.not_lt_zero a.val ha).elim,
      fun _ => by simp [Slots.empty, Slots.read]⟩⟩

end EX42.ArraySweep.Packed
