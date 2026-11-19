import PaperB.CompactGraph
import PaperB.Graph

namespace PaperB.CompactGraph

open Digraph

theorem survivingPath_iff (g : Digraph) (marks : Array Bool)
    (idx : Index g marks) (r : Fin g.vertexCount)
    (mark_iff : ∀ (a : Fin g.vertexCount),
      IsMarked idx a ↔ g.InitiallyReachable r a)
    (failed : Fin g.vertexCount → Prop) (u v : Vertex idx) :
    (build idx).SurvivingPath
        (fun (k : Vertex idx) => failed (decode idx k)) u v ↔
      g.SurvivingPath failed (decode idx u) (decode idx v) := by
  have closed : OutgoingClosed idx := by
    intro a b ha arc
    exact (mark_iff b).mpr
      (initiallyReachable_extend (g := g) (r := r) ((mark_iff a).mp ha) arc)
  change
    AvoidPath (build idx).HasArc
        (fun (k : Vertex idx) => failed (decode idx k)) u v ↔
      AvoidPath g.HasArc failed (decode idx u) (decode idx v)
  constructor
  · intro p
    induction p with
    | refl a alive =>
        exact AvoidPath.refl (decode idx a) alive
    | step a b c alive arc _ ih =>
        exact AvoidPath.step (decode idx a) (decode idx b) (decode idx c)
          alive ((hasArc_iff idx closed a b).mp arc) ih
  · intro p
    have transport :
        ∀ (a b : Fin g.vertexCount), AvoidPath g.HasArc failed a b →
          ∀ (i : Vertex idx), encode idx a = some i →
            ∃ (j : Vertex idx), encode idx b = some j ∧
              AvoidPath (build idx).HasArc
                (fun (k : Vertex idx) => failed (decode idx k)) i j := by
      intro a b q
      induction q with
      | refl a alive =>
          intro i hi
          have da : decode idx i = a := decode_encode idx a i hi
          exact ⟨i, hi, AvoidPath.refl i (by simpa only [da] using alive)⟩
      | step a b c alive arc _ ih =>
          intro i hi
          have da : decode idx i = a := decode_encode idx a i hi
          have head : g.HasArc (decode idx i) b := by
            simpa only [da] using arc
          obtain ⟨j, hj⟩ := encode_head idx closed i b head
          have db : decode idx j = b := decode_encode idx b j hj
          have compactArc : (build idx).HasArc i j :=
            (hasArc_iff idx closed i j).mpr (by simpa only [da, db] using arc)
          obtain ⟨k, hk, tail⟩ := ih j hj
          exact ⟨k, hk, AvoidPath.step i j k
            (by simpa only [da] using alive) compactArc tail⟩
    obtain ⟨k, hk, q⟩ :=
      transport (decode idx u) (decode idx v) p u (encode_decode idx u)
    have hkv : k = v := Option.some.inj (hk.symm.trans (encode_decode idx v))
    subst k
    exact q

end PaperB.CompactGraph
