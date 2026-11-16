import FgStrip.CommonEdge.Local
import FgStrip.CommonEdge.Ambient

/-!
# Concrete common-edge deletion

The local sequence implements proof-blueprint Sections 3–5. Its two distinct
endpoint moves use independently calculated diagonal intervals; the second
interval omits the first pivot. The coincident case uses one empty-word move.
All sign conditions range over the entire live subtype.
-/
namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

/-- The unrestricted local sequence, its actual mutate/delete/reverse execution,
and the exact set of removed common-edge endpoints. -/
theorem common_edge_deletion {n p : ℕ} (hp : p < n/2) :
    Sequence (matrix n) (support n) (live p) (finish p) ∧
    Execution (support n)
      (restrictMatrix (matrix n) (Subtype.val : live p → Grid n))
      (restrictMatrix (matrix n) (Subtype.val : finish p → Grid n)) ∧
    live (n := n) p \ finish p=endpoints p :=
  ⟨common_edge_sequence hp, (common_edge_sequence hp).execution, deleted_exact (by omega)⟩

/-- Additional interface deletions preserve the concrete supported sequence. -/
theorem common_edge_restrict {n p : ℕ} (hp : p < n/2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n) :
    Sequence (matrix n) (support n) (live p \ F) (finish p \ F) :=
  sequence_restrict (common_edge_sequence hp) F (interface_disjoint F hF)

/-- Arrow reversal preserves the same deletion endpoints and pivot support. -/
theorem common_edge_reverse {n p : ℕ} (hp : p < n/2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n) :
    Sequence (-matrix n) (support n) (live p \ F) (finish p \ F) :=
  sequence_neg (common_edge_restrict hp F hF)

/-- Arbitrary exterior vertices and arbitrary skew attachment off the two
interiors/common edge. No entry of the complementary ambient block is discarded. -/
theorem common_edge_ambient {n p : ℕ} (hp : p < n/2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n)
    {Z : Type*} [DecidableEq Z]
    (E : Matrix (Grid n ⊕ Z) (Grid n ⊕ Z) ℤ) (hE : SkewSymmetric E)
    (hz : ∀ u ∈ support n, ∀ z, E (.inl u) z=0) :
    Sequence (extendMatrix (matrix n)+E) (ambientSupport (support n))
      (ambientLive (live p \ F)) (ambientLive (finish p \ F)) ∧
    Execution (ambientSupport (support n))
      (restrictMatrix (extendMatrix (matrix n)+E)
        (Subtype.val : ambientLive (F := Z) (live p \ F) → Grid n ⊕ Z))
      (restrictMatrix (extendMatrix (matrix n)+E)
        (Subtype.val : ambientLive (F := Z) (finish p \ F) → Grid n ⊕ Z)) := by
  have h := sequence_ambient (common_edge_restrict hp F hF) E hE hz
  exact ⟨h,h.execution⟩

/-- The reversed local orientation admits the same unrestricted ambient block. -/
theorem common_edge_reverse_ambient {n p : ℕ} (hp : p < n/2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n)
    {Z : Type*} [DecidableEq Z]
    (E : Matrix (Grid n ⊕ Z) (Grid n ⊕ Z) ℤ) (hE : SkewSymmetric E)
    (hz : ∀ u ∈ support n, ∀ z, E (.inl u) z=0) :
    Sequence (extendMatrix (-matrix n)+E) (ambientSupport (support n))
      (ambientLive (live p \ F)) (ambientLive (finish p \ F)) ∧
    Execution (ambientSupport (support n))
      (restrictMatrix (extendMatrix (-matrix n)+E)
        (Subtype.val : ambientLive (F := Z) (live p \ F) → Grid n ⊕ Z))
      (restrictMatrix (extendMatrix (-matrix n)+E)
        (Subtype.val : ambientLive (F := Z) (finish p \ F) → Grid n ⊕ Z)) := by
  have h := sequence_ambient (common_edge_reverse hp F hF) E hE hz
  exact ⟨h,h.execution⟩

end FgStrip.CommonEdge
