import FgStrip.Rounds.Transport

namespace FgStrip.Rounds
open TriangleShell CommonEdge AmbientTriangulation TwoTriangle

/-- The sign dictated by the cyclic orders of the actual adjacent strip faces. -/
noncomputable def pairMatrix {n N} (s : Pair N) : Matrix (Grid n) (Grid n) ℤ :=
  fun x y => s.sign * TwoTriangle.matrix n x y

theorem pairMatrix_skew {n N} (s : Pair N) : SkewSymmetric (pairMatrix (n := n) s) := by
  intro x y
  dsimp [pairMatrix]
  rw [TwoTriangle.matrix_skew]
  ring

/-- The selected two-face contribution is the zero extension of the signed grid
matrix, including the entries at both interface edges. -/
theorem pair_contribution_extension {n N} (s : Pair N) :
    s.contribution = zeroExtension (s.embedding (n := n)) (pairMatrix s) := by
  classical
  funext u v
  by_cases hu : u ∈ Set.range s.embed
  · obtain ⟨x,rfl⟩ := hu
    by_cases hv : v ∈ Set.range s.embed
    · obtain ⟨y,rfl⟩ := hv
      change s.contribution (s.embedding x) (s.embedding y) =
        zeroExtension s.embedding (pairMatrix s) (s.embedding x) (s.embedding y)
      rw [zeroExtension_apply]
      exact s.contribution_eq x y
    · rw [s.contribution_skew, s.contribution_zero_of_not_range _ _ hv, neg_zero]
      exact (zeroExtension_col_zero s.embedding _ _ _ hv).symm
  · rw [s.contribution_zero_of_not_range _ _ hu]
    exact (zeroExtension_row_zero s.embedding _ _ _ hu).symm

/-- Every supported local row is the complete strip row, also at columns outside
this pair. No equality is imposed on other rows of the strip. -/
theorem pair_supported_rows {n N} (s : Pair N) (x : Grid n)
    (hx : x ∈ support n) (y : Strip.Vertex n N) :
    Strip.matrix n N (s.embedding x) y =
      zeroExtension s.embedding (pairMatrix s) (s.embedding x) y := by
  rw [← pair_contribution_extension]
  exact s.strip_row_eq_contribution x hx.1 hx.2 y

/-- Both pair orientations have the same concrete endpoints and support. -/
theorem pair_local_sequence {n N p} (s : Pair N) (hp : p < n/2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n) :
    Sequence (pairMatrix s) (support n) (live p \ F) (finish p \ F) := by
  cases s with
  | odd i =>
    have hm : pairMatrix (n := n) (Pair.odd i)=TwoTriangle.matrix n := by
      funext x y
      simp [pairMatrix, Pair.sign]
    rw [hm]
    exact common_edge_restrict hp F hF
  | even i hi =>
    have hm : pairMatrix (n := n) (Pair.even i hi) = -TwoTriangle.matrix n := by
      funext x y
      simp [pairMatrix, Pair.sign]
    rw [hm]
    exact common_edge_reverse hp F hF

/-- Concrete common-edge moves on an arbitrary exact strip live set. The only
live-set premise describes its preimage; it assumes no deletion certificate. -/
theorem pair_sequence_on_live {n N p} (s : Pair N) (hp : p < n/2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n)
    (U : Set (Strip.Vertex n N)) (hU : s.embed ⁻¹' U=live p \ F) :
    Sequence (Strip.matrix n N) (s.embed '' support n) U
      (U \ s.embed '' endpoints p) := by
  classical
  have h := sequence_of_rows (pair_local_sequence s hp F hF) (pairMatrix_skew s)
    s.embedding (Strip.matrix n N) Strip.matrix_skew (pair_supported_rows s) U hU
  have hdel : (live (n := n) p \ F) \ (finish p \ F)=endpoints p := by
    ext x
    have he := endpoints_live (n := n) (p := p) (by omega)
    have hd := endpoints_supported (n := n) (p := p)
    have hf := interface_disjoint F hF
    simp only [Set.mem_sdiff, finish]
    constructor
    · tauto
    · intro hx
      exact ⟨⟨he hx,hf x (hd hx)⟩,fun hh => hh.1.2 hx⟩
  rw [hdel] at h
  exact h

end FgStrip.Rounds
