import FgStrip

namespace FgStrip.Proposition74Consumer64317868
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

end FgStrip.Proposition74Consumer64317868

set_option pp.universes true in
#check @FgStrip.Proposition74.ambient
#check @FgStrip.Proposition74.triangulation
#check @FgStrip.Rounds.rounds
#print axioms FgStrip.Proposition74Consumer64317868.ambient_consumer
#print axioms FgStrip.Rounds.raised
#print axioms FgStrip.Rounds.raised_empty
#print axioms FgStrip.Rounds.raised_insert
#print axioms FgStrip.Rounds.batch_faces
#print axioms FgStrip.Rounds.batch_edges
#print axioms FgStrip.Rounds.faceEdgeA
#print axioms FgStrip.Rounds.faceEdgeB
#print axioms FgStrip.Rounds.faceWeight
#print axioms FgStrip.Rounds.faceWeight_live
#print axioms FgStrip.Rounds.faceEmbedding_a
#print axioms FgStrip.Rounds.faceEmbedding_b
#print axioms FgStrip.Rounds.face_edges
#print axioms FgStrip.Rounds.profile_face_preimage
#print axioms FgStrip.Rounds.shell_profile_sequence
#print axioms FgStrip.Rounds.activeFaces
#print axioms FgStrip.Rounds.activeEdges
#print axioms FgStrip.Rounds.mem_activeFaces
#print axioms FgStrip.Rounds.mem_activeEdges
#print axioms FgStrip.Rounds.raised_edgeDepth
#print axioms FgStrip.Rounds.raised_faceDepth
#print axioms FgStrip.Rounds.pair_face_indices
#print axioms FgStrip.Rounds.active_face_depths
#print axioms FgStrip.Rounds.active_edge_depths
#print axioms FgStrip.Rounds.first_profile
#print axioms FgStrip.Rounds.first_round
#print axioms FgStrip.Rounds.next_round
#print axioms FgStrip.Rounds.rounds
#print axioms FgStrip.Rounds.faceIndex
#print axioms FgStrip.Rounds.faceIndex_bounds
#print axioms FgStrip.Rounds.edgeDepth
#print axioms FgStrip.Rounds.faceDepth
#print axioms FgStrip.Rounds.profileLive
#print axioms FgStrip.Rounds.roundLive
#print axioms FgStrip.Rounds.edgeDepth_zero
#print axioms FgStrip.Rounds.faceDepth_zero
#print axioms FgStrip.Rounds.edgeDepth_left
#print axioms FgStrip.Rounds.edgeDepth_right
#print axioms FgStrip.Rounds.edgeDepth_central
#print axioms FgStrip.Rounds.faceDepth_central
#print axioms FgStrip.Rounds.edgeDepth_mono
#print axioms FgStrip.Rounds.faceDepth_mono
#print axioms FgStrip.Rounds.cornerSet_zero
#print axioms FgStrip.Rounds.cornerSet_one
#print axioms FgStrip.Rounds.cornerSet_mono
#print axioms FgStrip.Rounds.roundLive_zero
#print axioms FgStrip.Rounds.profileLive_edge
#print axioms FgStrip.Rounds.profileLive_interior
#print axioms FgStrip.Rounds.roundLive_antitone
#print axioms FgStrip.Rounds.middle_not_mem_roundLive
#print axioms FgStrip.Rounds.protected_mem_roundLive
#print axioms FgStrip.Rounds.pair_tx_interior
#print axioms FgStrip.Rounds.pair_ty_interior
#print axioms FgStrip.Rounds.pair_lower_interior
#print axioms FgStrip.Rounds.pair_upper_interior
#print axioms FgStrip.Rounds.pair_support_internal
#print axioms FgStrip.Rounds.stripWeight_live
#print axioms FgStrip.Rounds.profile_pair_D
#print axioms FgStrip.Rounds.profile_pair_L
#print axioms FgStrip.Rounds.profile_pair_R
#print axioms FgStrip.Rounds.profile_pair_X
#print axioms FgStrip.Rounds.profile_pair_Y
#print axioms FgStrip.Rounds.pairExtra
#print axioms FgStrip.Rounds.pairExtra_interface
#print axioms FgStrip.Rounds.profile_pair_preimage
#print axioms FgStrip.Rounds.pair_profile_sequence
#print axioms FgStrip.Rounds.pairMatrix
#print axioms FgStrip.Rounds.pairMatrix_skew
#print axioms FgStrip.Rounds.pair_contribution_extension
#print axioms FgStrip.Rounds.pair_supported_rows
#print axioms FgStrip.Rounds.pair_local_sequence
#print axioms FgStrip.Rounds.pair_sequence_on_live
#print axioms FgStrip.Rounds.edgeLayer
#print axioms FgStrip.Rounds.stripWeight_involutive
#print axioms FgStrip.Rounds.stripWeight_endpoint
#print axioms FgStrip.Rounds.pair_endpoints_image
#print axioms FgStrip.Rounds.profile_edge_update
#print axioms FgStrip.Rounds.profile_face_update
#print axioms FgStrip.Rounds.edge_profile_step
#print axioms FgStrip.Rounds.face_profile_step
#print axioms FgStrip.Rounds.Retained
#print axioms FgStrip.Rounds.retainedMatrix
#print axioms FgStrip.Rounds.retainedSupport
#print axioms FgStrip.Rounds.retainedLive
#print axioms FgStrip.Rounds.retainedFinish
#print axioms FgStrip.Rounds.retainedMatrix_skew
#print axioms FgStrip.Rounds.face_contribution_apply
#print axioms FgStrip.Rounds.face_contribution_row_zero
#print axioms FgStrip.Rounds.face_contribution_extension
#print axioms FgStrip.Rounds.face_supported_rows
#print axioms FgStrip.Rounds.retained_shell_sequence
#print axioms FgStrip.Rounds.shell_sequence_on_live
#print axioms FgStrip.Rounds.shell_support_internal
#print axioms FgStrip.Rounds.sequence_support_mono
#print axioms FgStrip.Rounds.sequence_equiv
#print axioms FgStrip.Rounds.sequence_restrict_live
#print axioms FgStrip.Rounds.sequence_pull
#print axioms FgStrip.Rounds.injectionEquiv
#print axioms FgStrip.Rounds.injectionEquiv_inl
#print axioms FgStrip.Rounds.injectionEquiv_inr
#print axioms FgStrip.Rounds.imageLive
#print axioms FgStrip.Rounds.imageLive_apply
#print axioms FgStrip.Rounds.imageLive_univ
#print axioms FgStrip.Rounds.zeroExtension_equiv
#print axioms FgStrip.Rounds.sequence_injection
#print axioms FgStrip.Rounds.sequence_on_live
#print axioms FgStrip.Rounds.zeroExtension_skew
#print axioms FgStrip.Rounds.sequence_of_rows
#print axioms FgStrip.Proposition74.deleted
#print axioms FgStrip.Proposition74.imageLive_compl
#print axioms FgStrip.Proposition74.strip
#print axioms FgStrip.Proposition74.ambient
#print axioms FgStrip.Proposition74.triangulation
#print axioms FgStrip.TriangleShell.shell_deletion
#print axioms FgStrip.TriangleShell.Sequence.execution
#print axioms FgStrip.TriangleShell.stepOutput_original
#print axioms FgStrip.DeletionMove.output_original
#print axioms FgStrip.TriangleShell.pullMove
#print axioms FgStrip.CommonEdge.common_edge_sequence
#print axioms FgStrip.CommonEdge.common_edge_restrict
#print axioms FgStrip.CommonEdge.common_edge_reverse
#print axioms FgStrip.CommonEdge.forward_target_row
#print axioms FgStrip.CommonEdge.coincident_sequence
#print axioms FgStrip.CommonEdge.sequence_ambient
#print axioms FgStrip.TwoTriangle.Pair.contribution_eq
#print axioms FgStrip.TwoTriangle.Pair.remainder_row_zero
#print axioms FgStrip.TwoTriangle.Pair.strip_row_eq_contribution
#print axioms FgStrip.TwoTriangle.Pair.embed_injective
#print axioms FgStrip.TwoTriangle.Pair.embed_D_edge
#print axioms FgStrip.TwoTriangle.Pair.embed_L_edge
#print axioms FgStrip.TwoTriangle.Pair.embed_R_edge
#print axioms FgStrip.Strip.matrix_concrete_entries
#print axioms FgStrip.AmbientTriangulation.Data.ambient_hypothesis
