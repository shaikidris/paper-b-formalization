import PaperB.StaticOracleTree
import Lean.Elab.Tactic.Omega

namespace PaperB.EX16Assembly.OriginalIdTranslation

/-- One contiguous image: forward words at `[0, n)`, inverse words at
`[n, n + m)`. The size and inverse bounds are erased proofs. -/
structure Payload (n m : Nat) where
  words : Array Nat
  size_eq : words.size = n + m
  inverse_lt : ∀ (x : Fin m) (h : n + x.val < words.size),
    words[n + x.val]'h < n

def encode {m : Nat} : Option (Fin m) → Nat
  | none => 0
  | some x => x.val + 1

private def decode (m : Nat) : Nat → Option (Fin m)
  | 0 => none
  | Nat.succ k => if h : k < m then some ⟨k, h⟩ else none

private theorem decode_encode {m : Nat} (o : Option (Fin m)) :
    decode m (encode o) = o := by
  cases o with
  | none => rfl
  | some x =>
    rcases x with ⟨k, hk⟩
    simp [encode, decode, hk]

private theorem encode_le {m : Nat} (o : Option (Fin m)) :
    encode o ≤ m := by
  cases o with
  | none => exact Nat.zero_le m
  | some x => exact Nat.succ_le_of_lt x.isLt

namespace Payload

variable {n m : Nat}

theorem forwardIndex_lt (p : Payload n m) (i : Fin n) :
    i.val < p.words.size := by
  rw [p.size_eq]
  have hi := i.isLt
  omega

theorem inverseIndex_lt (p : Payload n m) (x : Fin m) :
    n + x.val < p.words.size := by
  rw [p.size_eq]
  exact Nat.add_lt_add_left x.isLt n

def forwardWord (p : Payload n m) (i : Fin n) : Nat :=
  p.words[i.val]'(p.forwardIndex_lt i)

def inverseWord (p : Payload n m) (x : Fin m) : Nat :=
  p.words[n + x.val]'(p.inverseIndex_lt x)

/-- One array read followed by decoding; no reader or graph is needed. -/
def find (p : Payload n m) (i : Fin n) : Option (Fin m) :=
  decode m (p.forwardWord i)

/-- One array read. The bound proof adds no runtime check. -/
def original (p : Payload n m) (x : Fin m) : Fin n :=
  ⟨p.inverseWord x, p.inverse_lt x (p.inverseIndex_lt x)⟩

end Payload

variable {g : Digraph} {r : Fin g.vertexCount}

private def cell (q : OriginalReader g r)
    (k : Fin (g.vertexCount + q.count)) : Nat :=
  if h : k.val < g.vertexCount then
    encode (q.ids.find ⟨k.val, h⟩)
  else
    (q.ids.originals.read ⟨k.val - g.vertexCount, by
      have hk := k.isLt
      omega⟩).val

private theorem cell_inverse (q : OriginalReader g r) (x : Fin q.count)
    (h : g.vertexCount + x.val < g.vertexCount + q.count) :
    cell q ⟨g.vertexCount + x.val, h⟩ =
      (q.ids.originals.read x).val := by
  have hn : ¬ g.vertexCount + x.val < g.vertexCount := by omega
  have hs : g.vertexCount + x.val - g.vertexCount = x.val := by omega
  have hk : g.vertexCount + x.val - g.vertexCount < q.count := by
    rw [hs]
    exact x.isLt
  have he :
      (⟨g.vertexCount + x.val - g.vertexCount, hk⟩ : Fin q.count) = x :=
    Fin.ext hs
  simpa only [cell, dite_eq_right hn] using
    congrArg (fun y : Fin q.count => (q.ids.originals.read y).val) he

private theorem image_read_inverse (q : OriginalReader g r)
    (x : Fin q.count)
    (h : g.vertexCount + x.val < (Array.ofFn (cell q)).size) :
    (Array.ofFn (cell q))[g.vertexCount + x.val]'h =
      (q.ids.originals.read x).val := by
  simpa only [Array.getElem_ofFn] using
    (cell_inverse q x (Nat.add_lt_add_left x.isLt g.vertexCount))

/-- Materialize both rows. The result stores neither `q` nor `g`. -/
def pack (q : OriginalReader g r) : Payload g.vertexCount q.count where
  words := Array.ofFn (cell q)
  size_eq := by simp
  inverse_lt := by
    intro x h
    rw [image_read_inverse q x h]
    exact (q.ids.originals.read x).isLt

@[simp] theorem pack_size (q : OriginalReader g r) :
    (pack q).words.size = g.vertexCount + q.count :=
  (pack q).size_eq

/-- Exact physical read at the original ID. -/
theorem pack_read_forward (q : OriginalReader g r)
    (i : Fin g.vertexCount) (h : i.val < (pack q).words.size) :
    (pack q).words[i.val]'h = encode (q.ids.find i) := by
  have read := Array.getElem_ofFn (f := cell q) (i := i.val) (h := h)
  exact read.trans (dif_pos i.isLt)

/-- Exact physical read at the dense ID plus the forward-row length. -/
theorem pack_read_inverse (q : OriginalReader g r)
    (x : Fin q.count) (h : g.vertexCount + x.val < (pack q).words.size) :
    (pack q).words[g.vertexCount + x.val]'h =
      (q.ids.originals.read x).val :=
  image_read_inverse q x h

theorem pack_forwardWord (q : OriginalReader g r) (i : Fin g.vertexCount) :
    (pack q).forwardWord i = encode (q.ids.find i) :=
  pack_read_forward q i ((pack q).forwardIndex_lt i)

theorem pack_inverseWord (q : OriginalReader g r) (x : Fin q.count) :
    (pack q).inverseWord x = (q.ids.originals.read x).val :=
  pack_read_inverse q x ((pack q).inverseIndex_lt x)

theorem pack_forwardWord_fits (q : OriginalReader g r) {alphabet : Nat}
    (hCount : q.count < alphabet) (i : Fin g.vertexCount) :
    (pack q).forwardWord i < alphabet := by
  rw [pack_forwardWord]
  exact Nat.lt_of_le_of_lt (encode_le _) hCount

theorem pack_inverseWord_fits (q : OriginalReader g r) {alphabet : Nat}
    (hVertex : g.vertexCount ≤ alphabet) (x : Fin q.count) :
    (pack q).inverseWord x < alphabet := by
  rw [pack_inverseWord]
  exact Nat.lt_of_lt_of_le (q.ids.originals.read x).isLt hVertex

/-- Every physical cell fits in the alphabet, including forward misses. -/
theorem pack_word_fits (q : OriginalReader g r) {alphabet : Nat}
    (hVertex : g.vertexCount ≤ alphabet) (hCount : q.count < alphabet)
    (k : Nat) (hk : k < (pack q).words.size) :
    (pack q).words[k]'hk < alphabet := by
  have read := Array.getElem_ofFn (f := cell q) (i := k) (h := hk)
  change (Array.ofFn (cell q))[k]'hk < alphabet
  rw [read]
  unfold cell
  split
  · exact Nat.lt_of_le_of_lt (encode_le _) hCount
  · exact Nat.lt_of_lt_of_le (Fin.isLt _) hVertex

@[simp] theorem pack_find (q : OriginalReader g r) (i : Fin g.vertexCount) :
    (pack q).find i = q.ids.find i := by
  rw [Payload.find, pack_forwardWord]
  exact decode_encode _

@[simp] theorem pack_original (q : OriginalReader g r) (x : Fin q.count) :
    (pack q).original x = q.ids.originals.read x := by
  apply Fin.ext
  exact pack_inverseWord q x

theorem pack_find_eq_some_iff_original (q : OriginalReader g r)
    (i : Fin g.vertexCount) (x : Fin q.count) :
    (pack q).find i = some x ↔ (pack q).original x = i := by
  rw [pack_find, pack_original]
  exact q.find_eq_some_iff_original i x

theorem pack_original_of_find (q : OriginalReader g r)
    (i : Fin g.vertexCount) (x : Fin q.count) (h : (pack q).find i = some x) :
    (pack q).original x = i :=
  (pack_find_eq_some_iff_original q i x).mp h

theorem pack_find_original (q : OriginalReader g r) (x : Fin q.count) :
    (pack q).find ((pack q).original x) = some x := by
  rw [pack_original, pack_find]
  exact q.ids.slot_of_original x

theorem pack_find_eq_none_iff (q : OriginalReader g r) (i : Fin g.vertexCount) :
    (pack q).find i = none ↔ ¬ g.InitiallyReachable r i := by
  rw [pack_find]
  exact q.ids.miss_iff i

theorem pack_find_slot (q : OriginalReader g r) (i : Fin g.vertexCount)
    (hi : g.InitiallyReachable r i) :
    (pack q).find i = some (q.slot i hi) :=
  (pack_find q i).trans (q.find_slot i hi)

theorem pack_original_reachable (q : OriginalReader g r) (x : Fin q.count) :
    g.InitiallyReachable r ((pack q).original x) := by
  rw [pack_original]
  exact q.ids.original_reachable x

theorem pack_has_slot_iff_reachable (q : OriginalReader g r)
    (i : Fin g.vertexCount) :
    (∃ x : Fin q.count, (pack q).find i = some x) ↔
      g.InitiallyReachable r i := by
  constructor
  · rintro ⟨x, hx⟩
    rw [← pack_original_of_find q i x hx]
    exact pack_original_reachable q x
  · intro hi
    exact ⟨q.slot i hi, pack_find_slot q i hi⟩

end PaperB.EX16Assembly.OriginalIdTranslation
