import PaperB.ForestPreparedBuild
import PaperB.ForestLayoutTreeCost

namespace PaperB.StaticGroupedTreeReader

open PackedStaticLayout StaticLinearHead
open PaperB.EX15.WholeScan.PackedInput PaperB.EX24.FinalDFS
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestLayout PaperB.ForestHead

variable {N : Nat}

private theorem finishingEntryBound (x : Input N) (ht : InputOK x) :
    ∀ u : Fin N, (build x ht).layout.endpoints.entry.read u < N := by
  change ∀ u : Fin N, (buildLayout x).endpoints.entry.read u < N
  rw [buildLayout_eq]
  exact entry_lt x ht

/--
Source-site accounting for the occupied-prefix input and the grouped reader.

The length vector, in order, counts:
* packed parent and depth cells;
* zero-fuel DFS entry and stop cells, then completed entry and stop cells;
* size cells, heavy cells, bucket rows, and range rows;
* inverse fill cells, scattered inverse cells, and inverse-order cons records;
* head fill cells and completed head cells.

`C` counts child records in the physical buckets. Each heavy row consumes
its bucket, and the completed range row has one output record per child.
The pointwise equalities identify those two sites and the size tabulation.
The two `writes` witnesses count only scatter and head-step writes:
neither includes its fill. The zero-fuel DFS witness identifies the endpoint
fills; the completed endpoint lengths do not count DFS writes.

`reads` is a conservative **indexed-slot** charge, in source order:
* one occupied-header read at the packing boundary;
* at most two parent-word and two depth-word reads per vertex: allow the
  pair-producing callback to be evaluated separately for each projection;
* one stop and one entry read per size cell;
* one bucket-row read per heavy row and one size read per candidate;
* one bucket-row read per range row and two endpoint reads per child;
* one entry read per scatter and one inverse-cell read per list record;
* at most two parent reads, one heavy read, and one head read per sweep step.
  The second parent read is in the inheriting branch of `nextHead`.

The indexed-read charge does not count list traversal as array indexing:
the heavy and range passes each consume `C` child records, and the head
pass consumes `N` order records. Root projections, comparisons, option
inspection, scalar state, allocation, copying, and DFS execution are not
indexed reads in this model. In particular, no traversal of the *semantic*
preorder is charged to the grouped head pass.

The last inequality is a slot envelope for packing and finishing, not a
heap bound. It assumes uniquely updated arrays and counts retained cells
and records once, including the shared parent and depth columns. It adds
both inverse temporaries, a completed-row staging budget, and a DFS pending
command budget even though they need not coexist. Supply the DFS budget
from the existing **prefix** bound, not from the final empty stack.
Grouping-construction scratch, allocator capacity, and fixed-size state
are outside this envelope.
-/
theorem packedGrouped_finish
    {H} {c : Config H} {rank out} (h : OutputOK c rank out) :
    let N := nodeCount c out
    let x := packedInput h
    let ht := packedInput_ok h
    let r := build x ht
    let b := r.layout
    let z := layout b.buckets x.root 0
    let d := layout b.buckets x.root (2 * N)
    let ok := finishingEntryBound x ht
    let inv := inverseSlots b.packed.root b.endpoints.entry ok
    let order := inverseOrder b.packed.root b.endpoints.entry ok
    let heads := sweepEntries b.packed b.endpoints.entry ok
    let C := childScanLength b.buckets
    let reads :=
      1 + (2 * N + 2 * N) + (N + N) +
        (N + C) + (N + 2 * C) + N + N + (2 * N + N + N)
    x.root.val = 0 ∧
    b.packed.parent = x.parent ∧ b.packed.depth = x.depth ∧
    (∃ a e : Nat, z.entries = Array.replicate N a ∧
      z.ends = Array.replicate N e) ∧
    b.endpoints.entry.data = d.entries ∧
    b.endpoints.stop.data = d.ends ∧
    [x.parent.data.size, x.depth.data.size,
      z.entries.size, z.ends.size,
      b.endpoints.entry.data.size, b.endpoints.stop.data.size,
      b.packed.size.data.size, b.packed.heavy.data.size,
      b.buckets.rows.size, r.ranges.data.size,
      (StaticHeadSweep.Slots.fill N b.packed.root).data.size,
      inv.slots.data.size, order.length,
      (StaticHeadSweep.initial b.packed).heads.data.size,
      heads.heads.data.size] = List.replicate 15 N ∧
    C = N - 1 ∧
    (∀ u : Fin N,
      b.packed.size.read u = b.endpoints.stop.read u - b.endpoints.entry.read u ∧
      b.packed.heavy.read u =
        (ForestHeavyPath.scan b.packed.size.read (b.buckets.get u)).best.map
          (fun w => w.node) ∧
      r.ranges.read u =
        ExactOrderedChildIntervals.fromCompleted b.buckets
          b.endpoints.entry.data b.endpoints.stop.data
          b.endpoints.entry.len b.endpoints.stop.len u ∧
      (r.ranges.read u).size = (b.buckets.get u).length ∧
      r.tables.head u = heads.heads.read u) ∧
    inv.writes = N ∧
    (StaticHeadSweep.initial b.packed).writes = 0 ∧
    heads.writes = N ∧
    reads ≤ 1 + 17 * N ∧
    (∀ dfsPending rowStaging : Nat,
      dfsPending ≤ 2 * N → rowStaging ≤ C →
      (9 * N + 2 * C) + (N + N + dfsPending + rowStaging) ≤ 16 * N) := by
  intro N x ht r b z d ok inv order heads C reads
  have hchildren : C = N - 1 := buildLayout_childScanLength x
  have horder : order.length = N := inverse_list_records _ _ _
  have hinv : inv.writes = N := inverse_scatter_writes _ _ _
  have hheads : heads.writes = N := by
    -- Reduce the actual entry-order adapter, not `StaticHeadSweep.build`.
    change (StaticHeadSweep.sweep b.packed order).writes = N
    simp only [StaticHeadSweep.sweep, StaticHeadSweep.fold_write_count,
      StaticHeadSweep.initial, horder, Nat.zero_add]
  have hrow (u : Fin N) :
      r.ranges.read u =
        ExactOrderedChildIntervals.fromCompleted b.buckets
          b.endpoints.entry.data b.endpoints.stop.data
          b.endpoints.entry.len b.endpoints.stop.len u :=
    read_tabulate _ u
  have hrowSize (u : Fin N) :
      (r.ranges.read u).size = (b.buckets.get u).length := by
    rw [hrow u]
    first
    | (simp [ExactOrderedChildIntervals.fromCompleted]; done)
    | exact?
  refine ⟨packedInput_root h, rfl, rfl, ⟨_, _, rfl, rfl⟩,
    rfl, rfl, ?_, hchildren, ?_, hinv, rfl, hheads, ?_, ?_⟩
  · have hfill :
        (StaticHeadSweep.Slots.fill N b.packed.root).data.size = N :=
      (StaticHeadSweep.Slots.fill N b.packed.root).len
    have hheadFill :
        (StaticHeadSweep.initial b.packed).heads.data.size = N :=
      (StaticHeadSweep.initial b.packed).heads.len
    simp only [x.parent.len, x.depth.len, z.entries_size, z.ends_size,
      b.endpoints.entry.len, b.endpoints.stop.len, b.packed.size.len,
      b.packed.heavy.len, b.buckets.rows_size, r.ranges.len, hfill,
      inv.slots.len, horder, hheadFill, heads.heads.len] <;> rfl
  · intro u
    exact ⟨read_tabulate _ u, read_tabulate _ u, hrow u, hrowSize u, rfl⟩
  · dsimp only [reads]
    rw [hchildren]
    omega
  · intro dfsPending rowStaging hdfs hrowTmp
    rw [hchildren] at hrowTmp ⊢
    omega

end PaperB.StaticGroupedTreeReader
