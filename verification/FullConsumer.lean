import FgStrip

namespace FgStrip.PublicationConsumer
open TriangleShell AmbientTriangulation

/-- A fresh consumer with the full arbitrary complementary block. -/
theorem ambient_consumer {n N : ℕ} (hn : 2 ≤ n) (hN : max (n/2) 2 ≤ N)
    {V : Type*} [Finite V] [DecidableEq V] (i : Strip.Vertex n N ↪ V)
    (E : Matrix V V ℤ) (hE : SkewSymmetric E)
    (hz : ∀ x ∈ Strip.internal (show 0 < N by omega), ∀ v, E (i x) v=0) :
    ∃ Z : Set V,
      i '' Strip.middle (show 0 < N by omega) ⊆ Z ∧
      Z ⊆ i '' Strip.internal (show 0 < N by omega) ∧
      Sequence (zeroExtension i (Strip.matrix n N)+E)
        (i '' Strip.internal (show 0 < N by omega)) Set.univ Zᶜ ∧
      Execution (i '' Strip.internal (show 0 < N by omega))
        (restrictMatrix (zeroExtension i (Strip.matrix n N)+E) (Subtype.val : Set.univ → V))
        (restrictMatrix (zeroExtension i (Strip.matrix n N)+E) (Subtype.val : ↥(Zᶜ) → V)) :=
  Proposition74.ambient hn hN i E hE hz

theorem triangulation_consumer {n N : ℕ} (hn : 2 ≤ n) (hN : max (n/2) 2 ≤ N)
    {X O : Type*} [Fintype O] (d : AmbientTriangulation.Data N X O)
    (hb : d.BoundaryCompatible n) (hi : d.FaceIncidence n) :
    ∃ Z : Set (d.Vertex n),
      d.embedding hb '' Strip.middle (show 0 < N by omega) ⊆ Z ∧
      Z ⊆ d.embedding hb '' Strip.internal (show 0 < N by omega) ∧
      Sequence (d.matrix n) (d.embedding hb '' Strip.internal (show 0 < N by omega)) Set.univ Zᶜ ∧
      Execution (d.embedding hb '' Strip.internal (show 0 < N by omega))
        (restrictMatrix (d.matrix n) (Subtype.val : Set.univ → d.Vertex n))
        (restrictMatrix (d.matrix n) (Subtype.val : ↥(Zᶜ) → d.Vertex n)) :=
  Proposition74.triangulation hn hN d hb hi

end FgStrip.PublicationConsumer


#print axioms FgStrip.PublicationConsumer.ambient_consumer
#print axioms FgStrip.PublicationConsumer.triangulation_consumer
