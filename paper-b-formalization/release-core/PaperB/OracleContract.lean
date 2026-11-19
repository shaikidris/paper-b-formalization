-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
import Challenge

/-! File: PaperB/OracleContract.lean -/
namespace PaperB.OracleContract

def L (n : Nat) : Nat :=
  Nat.log2 (n + 1) + 1

theorem one_le_L (n : Nat) : 1 ≤ L n :=
  Nat.succ_le_succ (Nat.zero_le (Nat.log2 (n + 1)))

/-- Two guard bits for a constant-factor adjacency-list layout. Here `m`
counts arc occurrences, including parallel arcs. -/
def wordBits (n m : Nat) : Nat :=
  L (n + m) + 2

/-- The immutable index has only layout metadata and a flat word payload. -/
structure WordIndex where
  vertices : Nat
  bits : Nat
  words : Array (Fin (2 ^ bits))

structure BuildObservation (bits : Nat) where
  words : Array (Fin (2 ^ bits))
  operations : Nat
  peakLiveWords : Nat
  retainedWords : Nat

def BuildObservation.index {bits : Nat}
    (b : BuildObservation bits) (n : Nat) : WordIndex :=
  ⟨n, bits, b.words⟩

structure QueryObservation where
  answer : Bool
  operations : Nat

/--
Candidate interface, not an executable word-machine semantics. The build
observer takes the graph itself, which stores its explicit adjacency lists.
EX0.3 must justify the layout and the interpretation of each observation as
a machine run. In particular, the build observation must charge for the
index header and the full retained footprint, not just the logical length
of the payload. `none` supplies no completed-run observation.
-/
structure CandidateInterface where
  BuildProgram : Type
  QueryProgram : Type
  observeBuild : BuildProgram → (g : Digraph) → Fin g.vertexCount →
    Option (BuildObservation (wordBits g.vertexCount g.arcCount))
  observeQuery : QueryProgram → (I : WordIndex) →
    FailureSet I.vertices → Fin I.vertices → Option QueryObservation

/--
EX0.2 candidate theorem type relative to `M`. The same deterministic build
and query programs and the same constant work for every acyclic graph and
root. The quantification over the two-slot failure sets and original targets
is after the single build observation.
-/
def Candidate (M : CandidateInterface) (buildExp queryExp : Nat) : Prop :=
  ∃ (build : M.BuildProgram) (query : M.QueryProgram) (C : Nat),
    0 < C ∧
    ∀ (g : Digraph) (r : Fin g.vertexCount),
      g.IsAcyclic →
      ∃ b : BuildObservation (wordBits g.vertexCount g.arcCount),
        M.observeBuild build g r = some b ∧
        b.operations ≤ C * ((g.vertexCount + g.arcCount) * L g.vertexCount ^ buildExp) ∧
        b.peakLiveWords ≤ C * (g.vertexCount + g.arcCount) ∧
        b.words.size ≤ b.retainedWords ∧
        b.retainedWords ≤ C * g.vertexCount ∧
        ∀ (F : FailureSet g.vertexCount) (t : Fin g.vertexCount),
          ∃ q : QueryObservation,
            M.observeQuery query (b.index g.vertexCount) F t = some q ∧
            q.operations ≤ C * L g.vertexCount ^ queryExp ∧
            (q.answer = true ↔ g.ReachableAvoiding F r t)

def CandidateV13 (M : CandidateInterface) : Prop :=
  Candidate M 2 1

def CandidateV12 (M : CandidateInterface) : Prop :=
  Candidate M 3 3

private theorem pow_le_next (n k : Nat) :
    L n ^ k ≤ L n ^ (k + 1) := by
  calc
    L n ^ k = L n ^ k * 1 := (Nat.mul_one _).symm
    _ ≤ L n ^ k * L n := Nat.mul_le_mul_left _ (one_le_L n)
    _ = L n ^ (k + 1) := (Nat.pow_succ (L n) k).symm

/-- Relaxing the exponents changes neither the programs nor their observations. -/
theorem v13_implies_v12 (M : CandidateInterface) :
    CandidateV13 M → CandidateV12 M := by
  intro h
  unfold CandidateV13 Candidate at h
  unfold CandidateV12 Candidate
  rcases h with ⟨build, query, C, hC, h⟩
  refine ⟨build, query, C, hC, ?_⟩
  intro g r hDAG
  rcases h g r hDAG with
    ⟨b, hBuild, hTime, hPeak, hPayload, hRetained, hQuery⟩
  refine ⟨b, hBuild, ?_, hPeak, hPayload, hRetained, ?_⟩
  · exact Nat.le_trans hTime
      (Nat.mul_le_mul_left C
        (Nat.mul_le_mul_left (g.vertexCount + g.arcCount) (pow_le_next g.vertexCount 2)))
  · intro F t
    rcases hQuery F t with ⟨q, hRun, hTimeQuery, hAnswer⟩
    exact ⟨q, hRun, Nat.le_trans hTimeQuery
      (Nat.mul_le_mul_left C
        (Nat.le_trans (pow_le_next g.vertexCount 1) (pow_le_next g.vertexCount 2))),
      hAnswer⟩

end PaperB.OracleContract
