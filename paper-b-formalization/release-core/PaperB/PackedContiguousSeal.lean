import PaperB.PackedSectionSeal

namespace PaperB.PairLookup.ColumnReduction.EX52Seal.Contiguous

variable {bits : Nat}

/-- Use the source bank's word type, without introducing a new encoding. -/
private abbrev arrayElement {α : Type} (_ : Array α) : Type := α

abbrev Word (bits : Nat) : Type :=
  arrayElement ((⟨#[], #[]⟩ : Packed bits).header)

abbrev Block (bits : Nat) : Type := Array (Word bits)

def packedBase (p : Packed bits) : Nat := p.header.size + 1

def retained (p : Packed bits) : Nat := packedBase p + p.data.size

/-- `words` is the only runtime field. The offset header includes the source
sentinel, and all stored offsets remain relative to the data region. -/
structure Sealed (bits : Nat) where
  words : Array (Word bits)
  fits : words.size ≤ 2 ^ bits
  nonempty : 0 < words.size
  headerRoom : (words[0]'nonempty).val + 1 ≤ words.size

@[inline] def Sealed.headerLength (s : Sealed bits) : Nat :=
  (s.words[0]'s.nonempty).val

@[inline] def Sealed.dataBase (s : Sealed bits) : Nat :=
  s.headerLength + 1

theorem Sealed.headerIndex_bound (s : Sealed bits) (q : Nat)
    (hq : q < s.headerLength) : q + 1 < s.words.size := by
  have hr : s.headerLength + 1 ≤ s.words.size := s.headerRoom
  omega

theorem Sealed.index_fits (s : Sealed bits) {a : Nat}
    (ha : a < s.words.size) : a < 2 ^ bits :=
  Nat.lt_of_lt_of_le ha s.fits

theorem Sealed.headerIndex_fits (s : Sealed bits) (q : Nat)
    (hq : q < s.headerLength) : q + 1 < 2 ^ bits :=
  s.index_fits (s.headerIndex_bound q hq)

@[inline] def Sealed.headerWord (s : Sealed bits) (q : Nat)
    (hq : q < s.headerLength) : Word bits :=
  s.words[q + 1]'(s.headerIndex_bound q hq)

@[inline] def Sealed.start (s : Sealed bits) (q : Nat)
    (hq : q < s.headerLength) : Nat :=
  (s.headerWord q hq).val

@[inline] def Sealed.address (s : Sealed bits) (q i : Nat)
    (hq : q < s.headerLength) : Nat :=
  s.dataBase + s.start q hq + i

theorem Sealed.address_fits (s : Sealed bits) (q i : Nat)
    (hq : q < s.headerLength) (hi : s.address q i hq < s.words.size) :
    s.address q i hq < 2 ^ bits :=
  s.index_fits hi

/-- Two direct header loads (length and offset) and one direct data load.
No content search; the bounds arguments erase. -/
@[inline] def Sealed.read (s : Sealed bits) (q i : Nat)
    (hq : q < s.headerLength) (hi : s.address q i hq < s.words.size) :
    Word bits :=
  s.words[s.address q i hq]'hi

private def cell (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (j : Fin (retained p)) : Word bits :=
  if hz : j.val = 0 then
    ⟨p.header.size, by
      have h := hc
      unfold retained packedBase at h
      omega⟩
  else if hh : j.val < packedBase p then
    p.header[j.val - 1]'(by
      unfold packedBase at hh
      omega)
  else
    p.data[j.val - packedBase p]'(by
      have hj := j.isLt
      unfold retained at hj
      omega)

private def raw (p : Packed bits) (hc : retained p ≤ 2 ^ bits) :
    Array (Word bits) :=
  Array.ofFn (cell p hc)

private theorem raw_size (p : Packed bits) (hc : retained p ≤ 2 ^ bits) :
    (raw p hc).size = retained p := by
  simp [raw]

private theorem raw_at (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (j : Nat) (hj : j < retained p) (hr : j < (raw p hc).size) :
    (raw p hc)[j]'hr = cell p hc ⟨j, hj⟩ := by
  simp [raw]

private theorem raw_zero (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (hz : 0 < (raw p hc).size) :
    ((raw p hc)[0]'hz).val = p.header.size := by
  have hj : 0 < retained p := by simpa only [raw_size] using hz
  rw [raw_at p hc 0 hj] <;> simp [cell]

/-- Build `[header length | header offsets | data]` in one `Array.ofFn`.
The generator is not retained in the result. -/
def pack (p : Packed bits) (hc : retained p ≤ 2 ^ bits) : Sealed bits := by
  have hz : 0 < (raw p hc).size := by
    rw [raw_size]
    unfold retained packedBase
    omega
  refine ⟨raw p hc, ?_, hz, ?_⟩
  · simpa only [raw_size] using hc
  · rw [raw_zero p hc hz, raw_size]
    unfold retained packedBase
    omega

@[simp] theorem pack_size (p : Packed bits) (hc : retained p ≤ 2 ^ bits) :
    (pack p hc).words.size = retained p :=
  raw_size p hc

@[simp] theorem pack_headerLength (p : Packed bits)
    (hc : retained p ≤ 2 ^ bits) :
    (pack p hc).headerLength = p.header.size :=
  raw_zero p hc (pack p hc).nonempty

@[simp] theorem pack_dataBase (p : Packed bits) (hc : retained p ≤ 2 ^ bits) :
    (pack p hc).dataBase = packedBase p := by
  simp [Sealed.dataBase, packedBase]

theorem pack_header_bound (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (q : Nat) (hq : q < p.header.size) : q < (pack p hc).headerLength := by
  simpa only [pack_headerLength] using hq

theorem pack_header (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (q : Nat) (hq : q < p.header.size) :
    (pack p hc).headerWord q (pack_header_bound p hc q hq) = p.header[q]'hq := by
  have hn : q + 1 ≠ 0 := by omega
  have hh : q + 1 < packedBase p := by
    unfold packedBase
    omega
  have hj : q + 1 < retained p := by
    unfold retained
    omega
  have hr : q + 1 < (raw p hc).size := by simpa only [raw_size] using hj
  change (raw p hc)[q + 1]'hr = p.header[q]'hq
  rw [raw_at p hc (q + 1) hj] <;> simp [cell, hn, hh]

private theorem arrayIndexEq {α : Type} (a : Array α) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (e : i = j) :
    a[i]'hi = a[j]'hj := by
  subst j
  rfl

theorem pack_dataIndex_bound (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (j : Nat) (hj : j < p.data.size) :
    packedBase p + j < (pack p hc).words.size := by
  rw [pack_size]
  unfold retained
  omega

theorem pack_data (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (j : Nat) (hj : j < p.data.size) :
    (pack p hc).words[packedBase p + j]'(pack_dataIndex_bound p hc j hj) =
      p.data[j]'hj := by
  have hn : packedBase p + j ≠ 0 := by
    unfold packedBase
    omega
  have hh : ¬ packedBase p + j < packedBase p := by omega
  have hk : packedBase p + j < retained p := by
    unfold retained
    omega
  have hr : packedBase p + j < (raw p hc).size := by
    simpa only [raw_size] using hk
  have e := arrayIndexEq p.data
    (i := packedBase p + j - packedBase p) (j := j) (by omega) hj (by omega)
  change (raw p hc)[packedBase p + j]'hr = p.data[j]'hj
  rw [raw_at p hc (packedBase p + j) hk]
  simpa only [cell, Fin.val_mk, dite_eq_right hn, dite_eq_right hh] using e

theorem pack_start (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (q : Nat) (hq : q < p.header.size) :
    (pack p hc).start q (pack_header_bound p hc q hq) = p.start q hq :=
  congrArg (fun w : Word bits => w.val) (pack_header p hc q hq)

theorem pack_address (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (q i : Nat) (hq : q < p.header.size) :
    (pack p hc).address q i (pack_header_bound p hc q hq) =
      packedBase p + (p.start q hq + i) := by
  simp only [Sealed.address, pack_dataBase, Nat.add_assoc]
  rw [pack_start p hc q hq]

theorem pack_read_bound (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (q i : Nat) (hq : q < p.header.size) (hi : p.start q hq + i < p.data.size) :
    (pack p hc).address q i (pack_header_bound p hc q hq) <
      (pack p hc).words.size := by
  rw [pack_address p hc q i hq]
  exact pack_dataIndex_bound p hc _ hi

theorem pack_read (p : Packed bits) (hc : retained p ≤ 2 ^ bits)
    (q i : Nat) (hq : q < p.header.size) (hi : p.start q hq + i < p.data.size) :
    (pack p hc).read q i (pack_header_bound p hc q hq)
      (pack_read_bound p hc q i hq hi) = p.read q i hq hi :=
  (arrayIndexEq (pack p hc).words
    (pack_read_bound p hc q i hq hi)
    (pack_dataIndex_bound p hc (p.start q hq + i) hi)
    (pack_address p hc q i hq)).trans (pack_data p hc (p.start q hq + i) hi)

theorem serialize_retained (bs : List (Bank bits)) (h : cells bs < 2 ^ bits) :
    retained (serialize bs h) = bs.length + cells bs + 2 := by
  unfold retained packedBase
  rw [seal_header_size, seal_data_size]
  omega

private theorem source_cells_fit (bs : List (Bank bits))
    (hc : bs.length + cells bs + 2 ≤ 2 ^ bits) : cells bs < 2 ^ bits := by
  omega

private theorem source_retained_fit (bs : List (Bank bits))
    (hc : bs.length + cells bs + 2 ≤ 2 ^ bits) :
    retained (serialize bs (source_cells_fit bs hc)) ≤ 2 ^ bits := by
  simpa only [serialize_retained] using hc

/-- The whole-buffer bound permits equality: only live indices must fit in a
word. In particular, an empty data region can have a one-past-end base. -/
def serializeContiguous (bs : List (Bank bits)) (hc : bs.length + cells bs + 2 ≤ 2 ^ bits) :
    Sealed bits :=
  pack (serialize bs (source_cells_fit bs hc)) (source_retained_fit bs hc)

theorem seal_size (bs : List (Bank bits)) (hc : bs.length + cells bs + 2 ≤ 2 ^ bits) :
    (serializeContiguous bs hc).words.size = bs.length + cells bs + 2 :=
  (pack_size _ _).trans (serialize_retained bs (source_cells_fit bs hc))

theorem seal_header_bound (bs : List (Bank bits))
    (hc : bs.length + cells bs + 2 ≤ 2 ^ bits) (q : Nat) (hq : q ≤ bs.length) :
    q < (serializeContiguous bs hc).headerLength :=
  pack_header_bound _ _ q (header_bound bs (source_cells_fit bs hc) q hq)

theorem seal_word_bound (bs : List (Bank bits))
    (hc : bs.length + cells bs + 2 ≤ 2 ^ bits)
    (q : Nat) (hq : q < bs.length) (i : Nat) (hi : i < (bs[q]'hq).size) :
    (serializeContiguous bs hc).address q i (seal_header_bound bs hc q (Nat.le_of_lt hq)) <
      (serializeContiguous bs hc).words.size :=
  pack_read_bound _ _ q i
    (header_bound bs (source_cells_fit bs hc) q (Nat.le_of_lt hq))
    (read_bound bs (source_cells_fit bs hc) q hq i hi)

theorem seal_word (bs : List (Bank bits))
    (hc : bs.length + cells bs + 2 ≤ 2 ^ bits)
    (q : Nat) (hq : q < bs.length) (i : Nat) (hi : i < (bs[q]'hq).size) :
    (serializeContiguous bs hc).read q i (seal_header_bound bs hc q (Nat.le_of_lt hq))
      (seal_word_bound bs hc q hq i hi) = (bs[q]'hq)[i]'hi := by
  let h := source_cells_fit bs hc
  exact (pack_read (serialize bs h) (source_retained_fit bs hc) q i
    (header_bound bs h q (Nat.le_of_lt hq)) (read_bound bs h q hq i hi)).trans
      (seal_read bs h q hq i hi)

end PaperB.PairLookup.ColumnReduction.EX52Seal.Contiguous
