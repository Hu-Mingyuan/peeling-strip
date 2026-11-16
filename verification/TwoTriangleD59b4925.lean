import FgStrip.TwoTriangle

namespace FgStrip.TwoTriangleD59b4925
open Triangle TwoTriangle

theorem complete_entries {n} (u v : Grid n) :
    TwoTriangle.matrix n u v = (arrows u v : ℤ) - arrows v u := matrix_formula u v

theorem halfturn {n} (u v : Grid n) :
    TwoTriangle.matrix n (H u) (H v) = TwoTriangle.matrix n u v := matrix_halfturn u v

theorem odd_pair {n N} (i : Fin N) (u v : Grid n) :
    (Pair.odd i).contribution ((Pair.odd i).embed u) ((Pair.odd i).embed v) =
      TwoTriangle.matrix n u v := by
  simpa [Pair.sign] using (Pair.odd i).contribution_eq u v

theorem even_pair {n N} (i : Fin N) (hi : i.val+1 < N) (u v : Grid n) :
    (Pair.even i hi).contribution ((Pair.even i hi).embed u) ((Pair.even i hi).embed v) =
      -TwoTriangle.matrix n u v := by
  simpa [Pair.sign] using (Pair.even i hi).contribution_eq u v

theorem full_strip_split {n N} (s : Pair N) :
    Strip.matrix n N = s.contribution + s.remainder := s.strip_decomposition

theorem all_columns {n N} (s : Pair N) (u : Grid n)
    (hi : 0 < u.i) (hin : u.i < n) (v : Strip.Vertex n N) :
    s.remainder (s.embed u) v = 0 := s.remainder_row_zero u hi hin v

theorem every_common_edge {N} (j : Strip.EdgeIndex N)
    (h0 : 0 < j.val) (hN : j.val < 2*N) :
    (Pair.ofEdge j h0 hN).commonEdge = j := Pair.commonEdge_ofEdge j h0 hN

theorem all_three_labels {n N} (s : Pair N) (hN : 0 < N) (k : EdgeWeight n) :
    s.embed (L k) = Strip.edgeEmbedding hN s.lastEdge (s.stripWeight k) ∧
    s.embed (D k) = Strip.edgeEmbedding hN s.commonEdge (s.stripWeight k) ∧
    s.embed (R k) = Strip.edgeEmbedding hN s.firstEdge (s.stripWeight k) :=
  ⟨s.embed_L_edge hN k, s.embed_D_edge hN k, s.embed_R_edge hN k⟩

def rankTwoWeight : EdgeWeight 2 := ⟨⟨1, by decide⟩, by decide⟩
theorem rank_two_interfaces :
    TwoTriangle.matrix 2 (D rankTwoWeight) (L rankTwoWeight) = -1 ∧
    TwoTriangle.matrix 2 (D rankTwoWeight) (R rankTwoWeight) = -1 ∧
    TwoTriangle.matrix 2 (L rankTwoWeight) (R rankTwoWeight) = 0 := by
  simp [matrix_formula, arrows, D, L, R, Grid.i, Grid.j, rankTwoWeight, EdgeWeight.val]

end FgStrip.TwoTriangleD59b4925

#print axioms FgStrip.TwoTriangleD59b4925.complete_entries
#print axioms FgStrip.TwoTriangleD59b4925.halfturn
#print axioms FgStrip.TwoTriangleD59b4925.odd_pair
#print axioms FgStrip.TwoTriangleD59b4925.even_pair
#print axioms FgStrip.TwoTriangleD59b4925.full_strip_split
#print axioms FgStrip.TwoTriangleD59b4925.all_columns
#print axioms FgStrip.TwoTriangleD59b4925.every_common_edge
#print axioms FgStrip.TwoTriangleD59b4925.all_three_labels
#print axioms FgStrip.TwoTriangleD59b4925.rank_two_interfaces
#print axioms FgStrip.TwoTriangle.faceContribution
#print axioms FgStrip.TwoTriangle.Pair.contribution
#print axioms FgStrip.TwoTriangle.Pair.remainder
#print axioms FgStrip.TwoTriangle.Pair.sign
#print axioms FgStrip.TwoTriangle.Pair.mapped_x
#print axioms FgStrip.TwoTriangle.Pair.mapped_y
#print axioms FgStrip.TwoTriangle.Pair.contribution_eq
#print axioms FgStrip.TwoTriangle.Pair.strip_decomposition
#print axioms FgStrip.TwoTriangle.Pair.gx_ne_outside
#print axioms FgStrip.TwoTriangle.Pair.gy_ne_outside
#print axioms FgStrip.TwoTriangle.Pair.embed_ne_outside
#print axioms FgStrip.TwoTriangle.Pair.remainder_row_zero
#print axioms FgStrip.TwoTriangle.Pair.contribution_skew
#print axioms FgStrip.TwoTriangle.Pair.remainder_skew
#print axioms FgStrip.TwoTriangle.Square
#print axioms FgStrip.TwoTriangle.Grid
#print axioms FgStrip.TwoTriangle.x
#print axioms FgStrip.TwoTriangle.y
#print axioms FgStrip.TwoTriangle.x_injective
#print axioms FgStrip.TwoTriangle.y_injective
#print axioms FgStrip.TwoTriangle.x_eq_y_iff
#print axioms FgStrip.TwoTriangle.x_retained_iff
#print axioms FgStrip.TwoTriangle.y_retained_iff
#print axioms FgStrip.TwoTriangle.Grid.i
#print axioms FgStrip.TwoTriangle.Grid.j
#print axioms FgStrip.TwoTriangle.Grid.i_le
#print axioms FgStrip.TwoTriangle.Grid.j_pos
#print axioms FgStrip.TwoTriangle.Grid.j_lt
#print axioms FgStrip.TwoTriangle.Grid.ext
#print axioms FgStrip.TwoTriangle.Grid.lower
#print axioms FgStrip.TwoTriangle.Grid.upper
#print axioms FgStrip.TwoTriangle.Grid.x_lower
#print axioms FgStrip.TwoTriangle.Grid.y_upper
#print axioms FgStrip.TwoTriangle.Grid.covered
#print axioms FgStrip.TwoTriangle.L
#print axioms FgStrip.TwoTriangle.D
#print axioms FgStrip.TwoTriangle.R
#print axioms FgStrip.TwoTriangle.X
#print axioms FgStrip.TwoTriangle.Y
#print axioms FgStrip.TwoTriangle.HSquare
#print axioms FgStrip.TwoTriangle.HSquare_HSquare
#print axioms FgStrip.TwoTriangle.HSquare_injective
#print axioms FgStrip.TwoTriangle.H
#print axioms FgStrip.TwoTriangle.H_i
#print axioms FgStrip.TwoTriangle.H_j
#print axioms FgStrip.TwoTriangle.H_H
#print axioms FgStrip.TwoTriangle.reverseWeight
#print axioms FgStrip.TwoTriangle.H_D
#print axioms FgStrip.TwoTriangle.H_L
#print axioms FgStrip.TwoTriangle.H_R
#print axioms FgStrip.TwoTriangle.H_X
#print axioms FgStrip.TwoTriangle.H_Y
#print axioms FgStrip.TwoTriangle.EdgeDepth
#print axioms FgStrip.TwoTriangle.BarycentricC
#print axioms FgStrip.TwoTriangle.CX
#print axioms FgStrip.TwoTriangle.CY
#print axioms FgStrip.TwoTriangle.CX_x_iff
#print axioms FgStrip.TwoTriangle.CY_y_iff
#print axioms FgStrip.TwoTriangle.edgeDepth_reverse
#print axioms FgStrip.TwoTriangle.rot
#print axioms FgStrip.TwoTriangle.swap
#print axioms FgStrip.TwoTriangle.rot_rot_rot
#print axioms FgStrip.TwoTriangle.swap_swap
#print axioms FgStrip.TwoTriangle.cellRot
#print axioms FgStrip.TwoTriangle.cellSwap
#print axioms FgStrip.TwoTriangle.cellRotEquiv
#print axioms FgStrip.TwoTriangle.cellSwapEquiv
#print axioms FgStrip.TwoTriangle.rot_first
#print axioms FgStrip.TwoTriangle.rot_second
#print axioms FgStrip.TwoTriangle.rot_third
#print axioms FgStrip.TwoTriangle.swap_first
#print axioms FgStrip.TwoTriangle.swap_second
#print axioms FgStrip.TwoTriangle.swap_third
#print axioms FgStrip.TwoTriangle.cycleEntry_cyclic
#print axioms FgStrip.TwoTriangle.cycleEntry_reverse
#print axioms FgStrip.TwoTriangle.cycleEntry_map
#print axioms FgStrip.TwoTriangle.mapMatrix_rot
#print axioms FgStrip.TwoTriangle.mapMatrix_swap
#print axioms FgStrip.TwoTriangle.mapMatrix_map
#print axioms FgStrip.TwoTriangle.HSquare_x
#print axioms FgStrip.TwoTriangle.HSquare_y
#print axioms FgStrip.TwoTriangle.squareMatrix
#print axioms FgStrip.TwoTriangle.matrix
#print axioms FgStrip.TwoTriangle.matrix_cycle_sum
#print axioms FgStrip.TwoTriangle.entry
#print axioms FgStrip.TwoTriangle.matrix_entry
#print axioms FgStrip.TwoTriangle.matrix_skew
#print axioms FgStrip.TwoTriangle.squareMatrix_halfturn
#print axioms FgStrip.TwoTriangle.matrix_halfturn
#print axioms FgStrip.TwoTriangle.Pair.firstEdge
#print axioms FgStrip.TwoTriangle.Pair.lastEdge
#print axioms FgStrip.TwoTriangle.Pair.stripWeight
#print axioms FgStrip.TwoTriangle.Pair.edges_consecutive
#print axioms FgStrip.TwoTriangle.Pair.depth_stripWeight
#print axioms FgStrip.TwoTriangle.Pair.embed_D_edge
#print axioms FgStrip.TwoTriangle.Pair.embed_R_edge
#print axioms FgStrip.TwoTriangle.Pair.embed_L_edge
#print axioms FgStrip.TwoTriangle.Pair
#print axioms FgStrip.TwoTriangle.Pair.faceX
#print axioms FgStrip.TwoTriangle.Pair.faceY
#print axioms FgStrip.TwoTriangle.Pair.tx
#print axioms FgStrip.TwoTriangle.Pair.ty
#print axioms FgStrip.TwoTriangle.Pair.gx
#print axioms FgStrip.TwoTriangle.Pair.gy
#print axioms FgStrip.TwoTriangle.Pair.faces_ne
#print axioms FgStrip.TwoTriangle.Pair.tx_injective
#print axioms FgStrip.TwoTriangle.Pair.ty_injective
#print axioms FgStrip.TwoTriangle.Pair.gx_injective
#print axioms FgStrip.TwoTriangle.Pair.gy_injective
#print axioms FgStrip.TwoTriangle.Pair.gx_eq_gy_iff
#print axioms FgStrip.TwoTriangle.Pair.gx_mixed
#print axioms FgStrip.TwoTriangle.Pair.gy_mixed
#print axioms FgStrip.TwoTriangle.Pair.embed
#print axioms FgStrip.TwoTriangle.Pair.gx_eq_embed_iff
#print axioms FgStrip.TwoTriangle.Pair.gy_eq_embed_iff
#print axioms FgStrip.TwoTriangle.Pair.embed_injective
#print axioms FgStrip.TwoTriangle.Pair.embedding
#print axioms FgStrip.TwoTriangle.Pair.mem_range_embed_iff
#print axioms FgStrip.TwoTriangle.cell_ext
#print axioms FgStrip.TwoTriangle.first_injective
#print axioms FgStrip.TwoTriangle.second_injective
#print axioms FgStrip.TwoTriangle.third_injective
#print axioms FgStrip.TwoTriangle.cellOfBC
#print axioms FgStrip.TwoTriangle.indicator_sum
#print axioms FgStrip.TwoTriangle.x_first_second_iff
#print axioms FgStrip.TwoTriangle.x_second_third_iff
#print axioms FgStrip.TwoTriangle.x_third_first_iff
#print axioms FgStrip.TwoTriangle.y_first_second_iff
#print axioms FgStrip.TwoTriangle.y_second_third_iff
#print axioms FgStrip.TwoTriangle.y_third_first_iff
#print axioms FgStrip.TwoTriangle.arrows
#print axioms FgStrip.TwoTriangle.arrowCount_formula
#print axioms FgStrip.TwoTriangle.matrix_formula
#print axioms FgStrip.TwoTriangle.Neighbours
#print axioms FgStrip.TwoTriangle.neighbours_symm
#print axioms FgStrip.TwoTriangle.arrows_zero_of_not_neighbours
#print axioms FgStrip.TwoTriangle.matrix_zero_of_not_neighbours
#print axioms FgStrip.TwoTriangle.Pair.tx_surjective
#print axioms FgStrip.TwoTriangle.Pair.ty_surjective
#print axioms FgStrip.TwoTriangle.Pair.contribution_zero_of_not_range
#print axioms FgStrip.TwoTriangle.Pair.strip_row_eq_contribution
#print axioms FgStrip.TwoTriangle.label_cases
#print axioms FgStrip.TwoTriangle.x_D
#print axioms FgStrip.TwoTriangle.y_D
#print axioms FgStrip.TwoTriangle.x_R
#print axioms FgStrip.TwoTriangle.y_L
#print axioms FgStrip.TwoTriangle.x_X
#print axioms FgStrip.TwoTriangle.y_Y
#print axioms FgStrip.TwoTriangle.CY_rot
#print axioms FgStrip.TwoTriangle.deletedEdge
#print axioms FgStrip.TwoTriangle.deletedEdge_L
#print axioms FgStrip.TwoTriangle.deletedEdge_D
#print axioms FgStrip.TwoTriangle.deletedEdge_R
#print axioms FgStrip.TwoTriangle.Pair.commonEdge
#print axioms FgStrip.TwoTriangle.Pair.ofEdge
#print axioms FgStrip.TwoTriangle.Pair.commonEdge_ofEdge
#print axioms FgStrip.TwoTriangle.Pair.remainder_D
#print axioms FgStrip.TwoTriangle.Pair.remainder_X
#print axioms FgStrip.TwoTriangle.Pair.remainder_Y

#print axioms FgStrip.TwoTriangle.BarycentricC_swap
#print axioms FgStrip.TwoTriangle.Pair.CX_face
#print axioms FgStrip.TwoTriangle.Pair.CY_face
