import PaperB.DenseLocalRankFit
import PaperB.ForestKnownProbe

namespace CountedProbe

universe u v w z
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

def probe4
    (a₀ : Array α) (a₁ : Array β) (a₂ : Array γ) (a₃ : Array δ)
    (i₀ : Nat) (next₁ : α → Nat) (next₂ : β → Nat) (next₃ : γ → Nat)
    (d₀ : α) (d₁ : β) (d₂ : γ) (d₃ : δ) : δ × Nat :=
  bindC (readD a₀ i₀ d₀) fun x₀ =>
    bindC (readD a₁ (next₁ x₀) d₁) fun x₁ =>
      bindC (readD a₂ (next₂ x₁) d₂) fun x₂ =>
        readD a₃ (next₃ x₂) d₃

theorem probe4_exact
    (a₀ : Array α) (a₁ : Array β) (a₂ : Array γ) (a₃ : Array δ)
    (i₀ : Nat) (next₁ : α → Nat) (next₂ : β → Nat) (next₃ : γ → Nat)
    (d₀ : α) (d₁ : β) (d₂ : γ) (d₃ : δ) :
    probe4 a₀ a₁ a₂ a₃ i₀ next₁ next₂ next₃ d₀ d₁ d₂ d₃ =
      (let x₀ := (a₀[i₀]?).getD d₀
       let x₁ := (a₁[next₁ x₀]?).getD d₁
       let x₂ := (a₂[next₂ x₁]?).getD d₂
       let x₃ := (a₃[next₃ x₂]?).getD d₃
       (x₃, 4)) :=
  rfl

end CountedProbe

namespace PaperB.DenseQuotientLocalOrder

open PaperB.EX16Assembly PaperB.DenseQuotientRows
open PaperB.ForestLayout (ChildLists)
open PaperB.StaticHeadSweep (Slots)

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : OriginalReader g r) {buckets : ChildLists q.count}
variable (rows : DenseQuotientRows.Layout buckets) (b : BoundKahnOrder g)

def rankProbed (u : Fin q.count) (i : Fin (rows.length u)) : Nat × Nat :=
  CountedProbe.mapC Fin.val
    (CountedProbe.probe4 rows.directory rows.cells q.ids.originals.data b.slots.data u.val
      (fun descriptor => descriptor.1 + i.val)
      (fun cell => (Sum.elim id id cell.key).val) Fin.val (0, 0) (.root u) r r)

private theorem optional_eq_read {α : Type} {xs : Array α} {i : Nat}
    {hi : i < xs.size} {v : α} (h : v = xs[i]'hi) : xs[i]? = some v := by
  rw [getElem?_pos xs i hi, h]

/-- Directory, flat occurrence, original ID and inverse topological-rank
record are each probed exactly once, with the actual address at every step. -/
theorem rankProbed_exact (u : Fin q.count) (i : Fin (rows.length u)) :
    rankProbed q rows b u i = (slotRank q rows b.rankRead u i, 4) := by
  have hd : u.val < rows.directory.size := rows.directory_size.symm ▸ u.isLt
  have hstart : (rows.directory[u.val]'hd).1 = rows.start u := rfl
  have hcell := optional_eq_read (DenseQuotientRows.Layout.cell.eq_def rows u i)
  let k : Fin q.count := Sum.elim id id (rows.key u i)
  let id : Fin g.vertexCount := q.ids.originals.read k
  have hi : k.val < q.ids.originals.data.size := q.ids.originals.size_eq.symm ▸ k.isLt
  have hb : id.val < b.slots.data.size := b.slots.len.symm ▸ id.isLt
  have hread : q.ids.originals.data[k.val]? = some id :=
    getElem?_pos q.ids.originals.data k.val hi
  unfold rankProbed
  rw [CountedProbe.probe4_exact]
  dsimp only
  simp only [getElem?_pos rows.directory u.val hd, Option.getD_some, hstart, hcell]
  change CountedProbe.mapC Fin.val (((q.ids.originals.data[k.val]?).getD r |> fun j =>
    (b.slots.data[j.val]?).getD r), 4) = _
  rw [hread]
  simp only [Option.getD_some, getElem?_pos b.slots.data id.val hb]
  rfl

end PaperB.DenseQuotientLocalOrder
