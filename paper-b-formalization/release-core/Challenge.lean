import Std

/-! Raw finite graph data, bounded failures, and physical exit-tail membership for Paper B. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

/-- Directed path over an explicit step relation `edge`, avoiding `failed` at every
    visited vertex including both endpoints (`refl` has length zero). -/
inductive AvoidPath {V : Type} (edge : V → V → Prop) (failed : V → Prop) :
    V → V → Prop where
  | refl (u : V) (alive : ¬ failed u) :
      AvoidPath edge failed u u
  | step (u w v : V)
      (alive : ¬ failed u)
      (arc : edge u w)
      (rest : AvoidPath edge failed w v) :
      AvoidPath edge failed u v

/-- Sum of list lengths, counting parallel arc occurrences with multiplicity. -/
def listLengthSum {α : Type} : List (List α) → Nat
  | [] => 0
  | xs :: xss => xs.length + listLengthSum xss

/-- Explicit query failure specification of at most two original vertex IDs.
    Two equal IDs `two a a` denote a singleton failure. -/
inductive FailureSet (n : Nat) : Type where
  | none : FailureSet n
  | one (a : Fin n) : FailureSet n
  | two (a b : Fin n) : FailureSet n
  deriving DecidableEq

namespace FailureSet

def Mem {n : Nat} (F : FailureSet n) (x : Fin n) : Prop :=
  match F with
  | .none => False
  | .one a => x = a
  | .two a b => x = a ∨ x = b

end FailureSet

/-- Explicit finite directed multigraph on original `Fin vertexCount` identifiers.
    Adjacency lists are concrete data (`Array` of `List`), with parallel arcs
    preserved as repeated list entries. -/
structure Digraph where
  vertexCount : Nat
  adj : Array (List (Fin vertexCount))
  adj_size : adj.size = vertexCount

namespace Digraph

/-- Outgoing adjacency list of `u`, preserving parallel arcs. -/
def outArcs (g : Digraph) (u : Fin g.vertexCount) : List (Fin g.vertexCount) :=
  g.adj[u.val]'(by rw [g.adj_size]; exact u.isLt)

/-- Existence of at least one arc `u → v` in `g`. -/
def HasArc (g : Digraph) (u v : Fin g.vertexCount) : Prop :=
  v ∈ g.outArcs u

/-- Total directed arc count `m = |E(G)|`, counting parallel arcs. -/
def arcCount (g : Digraph) : Nat :=
  listLengthSum g.adj.toList

/-- Separate acyclicity condition witnessed in `Prop` by a topological rank. -/
def IsAcyclic (g : Digraph) : Prop :=
  ∃ rank : Fin g.vertexCount → Nat,
    ∀ u v : Fin g.vertexCount, g.HasArc u v → rank u < rank v

/-- Surviving directed path in `g` avoiding `failed` (includes both endpoints and length zero). -/
abbrev SurvivingPath (g : Digraph) (failed : Fin g.vertexCount → Prop) :
    Fin g.vertexCount → Fin g.vertexCount → Prop :=
  AvoidPath g.HasArc failed

/-- Surviving `r`-to-`t` reachability in `g - F`. -/
def ReachableAvoiding (g : Digraph) (F : FailureSet g.vertexCount)
    (r t : Fin g.vertexCount) : Prop :=
  g.SurvivingPath F.Mem r t

end Digraph

/-- Concrete quotient arc carrying both its quotient head and the original physical
    tail `origTail` of the underlying DAG arc. -/
structure QuotientArc (origVertexCount vertexCount : Nat) where
  head : Fin vertexCount
  origTail : Fin origVertexCount
  deriving DecidableEq

/-- Explicit labelled sibling quotient `H_d` on `Fin vertexCount` with root `root`
    and an original physical tail in `Fin origVertexCount` on every quotient arc. -/
structure LabelledQuotient where
  origVertexCount : Nat
  vertexCount : Nat
  root : Fin vertexCount
  adj : Array (List (QuotientArc origVertexCount vertexCount))
  adj_size : adj.size = vertexCount

namespace LabelledQuotient

/-- Concrete list of labelled quotient arcs leaving `u`. -/
def outArcs (H : LabelledQuotient) (u : Fin H.vertexCount) :
    List (QuotientArc H.origVertexCount H.vertexCount) :=
  H.adj[u.val]'(by rw [H.adj_size]; exact u.isLt)

/-- Total number of labelled quotient arcs `m_H`, counting parallel exits. -/
def arcCount (H : LabelledQuotient) : Nat :=
  listLengthSum H.adj.toList

/-- Existence of a quotient arc `u → w` (for unlabelled suffix reachability). -/
def HasQuotientArc (H : LabelledQuotient) (u w : Fin H.vertexCount) : Prop :=
  ∃ e : QuotientArc H.origVertexCount H.vertexCount,
    e ∈ H.outArcs u ∧ e.head = w

/-- Acyclicity of the quotient witnessed in `Prop` by a topological rank. -/
def IsAcyclic (H : LabelledQuotient) : Prop :=
  ∃ rank : Fin H.vertexCount → Nat,
    ∀ u w : Fin H.vertexCount, H.HasQuotientArc u w → rank u < rank w

/-- Surviving path in `H` avoiding `failed` at all visited vertices (including endpoints). -/
abbrev SurvivingPath (H : LabelledQuotient) (failed : Fin H.vertexCount → Prop) :
    Fin H.vertexCount → Fin H.vertexCount → Prop :=
  AvoidPath H.HasQuotientArc failed

/-- Flat dominator structure of a sibling quotient (Lemma 2.1 / Section 3):
    every vertex is reachable from `H.root`, and deleting any single nonroot
    vertex `u` loses only `u`. -/
def IsFlat (H : LabelledQuotient) : Prop :=
  (∀ v : Fin H.vertexCount, H.SurvivingPath (fun _ => False) H.root v) ∧
  (∀ u v : Fin H.vertexCount, u ≠ H.root → v ≠ u →
    H.SurvivingPath (fun z => z = u) H.root v)

/-- Pair `B = {fst, snd}` of distinct nonroot vertices in `H`. -/
structure CutPair (H : LabelledQuotient) where
  fst : Fin H.vertexCount
  snd : Fin H.vertexCount
  fst_ne_root : fst ≠ H.root
  snd_ne_root : snd ≠ H.root
  ne : fst ≠ snd

namespace CutPair

def Mem {H : LabelledQuotient} (B : CutPair H) (v : Fin H.vertexCount) : Prop :=
  v = B.fst ∨ v = B.snd

instance instDecidableMem {H : LabelledQuotient} (B : CutPair H)
    (v : Fin H.vertexCount) : Decidable (B.Mem v) :=
  if h₁ : v = B.fst then
    isTrue (Or.inl h₁)
  else if h₂ : v = B.snd then
    isTrue (Or.inr h₂)
  else
    isFalse (fun h =>
      match h with
      | Or.inl h₁' => h₁ h₁'
      | Or.inr h₂' => h₂ h₂')

end CutPair

/-- `Z(B)`: vertices of `H` lost upon deleting `B` (including `B` itself). -/
def Lost (H : LabelledQuotient) (B : CutPair H) (v : Fin H.vertexCount) : Prop :=
  ¬ H.SurvivingPath B.Mem H.root v

/-- `J(B) = Z(B) \ B`: proper losses of `B` in `H`. -/
def ProperLoss (H : LabelledQuotient) (B : CutPair H) (v : Fin H.vertexCount) : Prop :=
  H.Lost B v ∧ ¬ B.Mem v

/-- Fresh endpoint membership `p ∈ P \ B`. -/
def IsFreshEndpoint {H : LabelledQuotient} (B P : CutPair H)
    (p : Fin H.vertexCount) : Prop :=
  P.Mem p ∧ ¬ B.Mem p

/-- Usable exit-tail membership `x ∈ X^B_s(y)` (Section 2):
    there exists a concrete labelled quotient arc `e` out of `s` with original
    physical tail `e.origTail = x` whose head `e.head` reaches `y` in `H - B`.
    Parallel quotient exits with distinct original tails remain distinct. -/
def ExitTailMem (H : LabelledQuotient) (B : CutPair H)
    (s y : Fin H.vertexCount) (x : Fin H.origVertexCount) : Prop :=
  ∃ e : QuotientArc H.origVertexCount H.vertexCount,
    e ∈ H.outArcs s ∧
    e.origTail = x ∧
    H.SurvivingPath B.Mem e.head y

end LabelledQuotient

end PaperB
