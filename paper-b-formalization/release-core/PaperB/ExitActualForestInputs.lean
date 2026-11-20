import PaperB.ExitDriverCoverage
import PaperB.GenericRawExitModel

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB.OrderedFreshHeads

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable {r : _root_.PaperB.OrderedReaderResult p data size_data rank large}

variable {F : JumpForest} {up : Fin F.size → Fin F.size}
variable {g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}

variable
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))

private def compactDriverAt (j : Fin (exitTransferDrivers r).size) :
    ExitTransferDriver H :=
  (exitTransferDrivers r)[j.val]'(j.isLt)

include full ch G hUp E

private theorem compactDriverAt_provenance
    (j : Fin (exitTransferDrivers r).size) :
    ∃ a : Fin F.size,
      a.val = (compactDriverAt (r := r) j).address ∧
      (buildProperLossForest H rank).nodeKey? (E.image a) =
        some (compactDriverAt (r := r) j).child ∧
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent (E.image a)) =
        some (compactDriverAt (r := r) j).parent := by
  have hd : compactDriverAt (r := r) j ∈ exitTransferDrivers r :=
    Array.mem_iff_getElem.mpr ⟨j.val, j.isLt, rfl⟩
  obtain ⟨_, _, a, _, _, _, ha, _, _, _, _, hc, hp⟩ :=
    exitTransferDrivers_provenance (r := r) full ch G hUp E hd
  exact ⟨a, ha, hc, hp⟩

private theorem compactDriverAt_address_lt
    (j : Fin (exitTransferDrivers r).size) :
    (compactDriverAt (r := r) j).address < F.size := by
  obtain ⟨a, ha, _, _⟩ :=
    compactDriverAt_provenance (r := r) full ch G hUp E j
  rw [← ha]
  exact a.isLt

/-- Proof-only view of the physical drivers, in their original array order.
Only the slot projection passes through the final embedding. -/
noncomputable def actualForestInputs :
    GenericRawExitModel.ForestInputs H (buildProperLossForest H rank)
      (exitTransferDrivers r).size where
  owner := exitDenseOwnerKey? r
  slots := Array.ofFn fun j : Fin (exitTransferDrivers r).size =>
    E.image
      ⟨(compactDriverAt (r := r) j).address,
        compactDriverAt_address_lt (r := r) full ch G hUp E j⟩
  size_eq := by simp
  child := fun j => (compactDriverAt (r := r) j).child
  parent := fun j => (compactDriverAt (r := r) j).parent

private theorem actualForestInputs_edgeNode_eq_image
    (j : Fin (exitTransferDrivers r).size) (a : Fin F.size)
    (ha : a.val = (compactDriverAt (r := r) j).address) :
    (actualForestInputs (r := r) full ch G hUp E).edgeNode j = E.image a := by
  simp only [GenericRawExitModel.ForestInputs.edgeNode, actualForestInputs,
    Array.getElem_ofFn]
  exact congrArg E.image (Fin.ext ha.symm)

/-- Owner agreement includes the root; driver key agreement comes from
the exact provenance of the physical record at each array index. -/
theorem actualForestInputs_keyAgreement :
    GenericRawExitModel.KeyAgreement
      (actualForestInputs (r := r) full ch G hUp E) := by
  constructor
  · intro y
    exact exitDenseOwnerKey?_eq_canonical (r := r) E y
  · intro j
    obtain ⟨a, ha, hc, _⟩ :=
      compactDriverAt_provenance (r := r) full ch G hUp E j
    rw [actualForestInputs_edgeNode_eq_image (r := r) full ch G hUp E j a ha]
    exact hc
  · intro j
    obtain ⟨a, ha, _, hp⟩ :=
      compactDriverAt_provenance (r := r) full ch G hUp E j
    rw [actualForestInputs_edgeNode_eq_image (r := r) full ch G hUp E j a ha]
    exact hp

/-- Every canonical edge with two real keys is represented by an actual
driver index, with both keys read from that same physical driver. -/
theorem actualForestInputs_covers_realEdge
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {k : Fin ((buildProperLossForest H rank).realNodeCount + 1)}
    {child parent : CutPair H}
    (hk : (buildProperLossForest H rank).nodeKey? k = some child)
    (hp : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent k) = some parent) :
    ∃ j : Fin (exitTransferDrivers r).size,
      (actualForestInputs (r := r) full ch G hUp E).edgeNode j = k ∧
      (actualForestInputs (r := r) full ch G hUp E).child j = child ∧
      (actualForestInputs (r := r) full ch G hUp E).parent j = parent := by
  obtain ⟨d, a, hd, hc, hp', haddr, himage⟩ :=
    exitTransferDrivers_covers_realEdge (r := r)
      full rankArc flat ch G hUp E hk hp
  obtain ⟨i, hi, hread⟩ := Array.mem_iff_getElem.mp hd
  let j : Fin (exitTransferDrivers r).size := ⟨i, hi⟩
  have hj : compactDriverAt (r := r) j = d := hread
  have ha : a.val = (compactDriverAt (r := r) j).address := by
    rw [hj]
    exact haddr.symm
  refine ⟨j, ?_, ?_, ?_⟩
  · exact
      (actualForestInputs_edgeNode_eq_image (r := r)
        full ch G hUp E j a ha).trans himage
  · change (compactDriverAt (r := r) j).child = child
    exact (congrArg (fun d : ExitTransferDriver H => d.child) hj).trans hc
  · change (compactDriverAt (r := r) j).parent = parent
    exact (congrArg (fun d : ExitTransferDriver H => d.parent) hj).trans hp'

/-- Build the proof model over the already prepared raw rows. `raw_eq` is
a certificate about `R`, not a second call to `prepare`. -/
noncomputable def actualRawExitModel
    (R : GenericRawExitModel.Runtime H)
    (raw_eq : R.raw = ForestIncomingRaw.prepare H)
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (rankInjective : Function.Injective rank)
    (flatLaw : GenericRawExitModel.FlatLaw H rank rankArc rankInjective) :
    BuiltExit.Model H (exitTransferDrivers r).size :=
  GenericRawExitModel.model R raw_eq rank rankArc rankInjective flatLaw
    (actualForestInputs (r := r) full ch G hUp E)
    (actualForestInputs_keyAgreement (r := r) full ch G hUp E)

/-- Node-only coverage for the driver-coverage premise of
`RoutePathEdgeLive.of_driverCoverage`. The witness is a physical driver
index, not an index into a separately enumerated forest. -/
theorem actualRawExitModel_driverCoverage
    (R : GenericRawExitModel.Runtime H)
    (raw_eq : R.raw = ForestIncomingRaw.prepare H)
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (rankInjective : Function.Injective rank)
    (flatLaw : GenericRawExitModel.FlatLaw H rank rankArc rankInjective)
    (flat : H.IsFlat)
    {k : Fin ((buildProperLossForest H rank).realNodeCount + 1)}
    {child parent : CutPair H}
    (hk : (buildProperLossForest H rank).nodeKey? k = some child)
    (hp : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent k) = some parent) :
    ∃ j : Fin (exitTransferDrivers r).size,
      (actualRawExitModel (r := r) full ch G hUp E
        R raw_eq rankArc rankInjective flatLaw).edgeNode j = k := by
  obtain ⟨j, hj, _, _⟩ :=
    actualForestInputs_covers_realEdge (r := r)
      full ch G hUp E rankArc flat hk hp
  exact ⟨j, hj⟩

end PaperB.Exit.OrderedReaderResult
