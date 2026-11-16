import FgStrip.CommonEdge

open FgStrip FgStrip.TwoTriangle FgStrip.TriangleShell FgStrip.CommonEdge

-- Fresh unrestricted consumers. There is no local deletion-certificate hypothesis.
example {n p : ℕ} (hp : p < n/2) :
    Sequence (matrix n) (support n) (live p) (finish p) := common_edge_sequence hp

example {n p : ℕ} (hp : p < n/2) :
    Execution (support n)
      (restrictMatrix (matrix n) (Subtype.val : live p → Grid n))
      (restrictMatrix (matrix n) (Subtype.val : finish p → Grid n)) :=
  (common_edge_deletion hp).2.1

example {n p : ℕ} (hn : n=2*p+2) :
    Sequence (matrix n) (support n) (live p) (finish p) := coincident_sequence hn

example {n p : ℕ} (hn : 2*p+3 ≤ n) (v : wordLive (n := n) p true) :
    mutateWord (restrictMatrix (matrix n) Subtype.val) (forwardWord hn true) (target hn true) v =
      -e (n-p-1) 1 v.val -
      (if true=true ∧ p+2=n-p-1 then e (n-p-2) (n-p-1) v.val else 0) :=
  forward_target_row hn true v

example {n p : ℕ} (hp : p < n/2) (F : Set (Grid n))
    (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n) {Z : Type*} [DecidableEq Z]
    (E : Matrix (Grid n ⊕ Z) (Grid n ⊕ Z) ℤ) (hE : SkewSymmetric E)
    (hz : ∀ u ∈ support n, ∀ z, E (.inl u) z=0) :
    Sequence (extendMatrix (matrix n)+E) (ambientSupport (support n))
      (ambientLive (live p \ F)) (ambientLive (finish p \ F)) :=
  (common_edge_ambient hp F hF E hE hz).1

#check @FgStrip.CommonEdge.common_edge_deletion
#check @FgStrip.CommonEdge.common_edge_sequence
#check @FgStrip.CommonEdge.forwardMove
#check @FgStrip.CommonEdge.forward_target_row
#check @FgStrip.CommonEdge.top_after_diagonal_interval
#check @FgStrip.CommonEdge.top_after_diagonal
#check @FgStrip.CommonEdge.SweepState
#check @FgStrip.CommonEdge.sweep_step
#check @FgStrip.CommonEdge.target_step
#check @FgStrip.CommonEdge.sequence_restrict
#check @FgStrip.CommonEdge.sequence_ambient
#check @FgStrip.CommonEdge.common_edge_reverse_ambient

-- Transitive kernel axiom evidence for every delivered declaration.
#print axioms FgStrip.CommonEdge.ambientLive
#print axioms FgStrip.CommonEdge.ambientSupport
#print axioms FgStrip.CommonEdge.ambientMap
#print axioms FgStrip.CommonEdge.ambientLift
#print axioms FgStrip.CommonEdge.ambientMap_lift
#print axioms FgStrip.CommonEdge.ambientLift_map
#print axioms FgStrip.CommonEdge.ambientMap_injective
#print axioms FgStrip.CommonEdge.sequence_extend
#print axioms FgStrip.CommonEdge.sequence_ambient
#print axioms FgStrip.CommonEdge.central
#print axioms FgStrip.CommonEdge.coincidentMove
#print axioms FgStrip.CommonEdge.coincidentMove_finish
#print axioms FgStrip.CommonEdge.coincident_sequence
#print axioms FgStrip.CommonEdge.coincident_deletion
#print axioms FgStrip.CommonEdge.columnsPrefix
#print axioms FgStrip.CommonEdge.columnsPrefix_zero
#print axioms FgStrip.CommonEdge.totalColumn
#print axioms FgStrip.CommonEdge.columnsPrefix_flatMap
#print axioms FgStrip.CommonEdge.columnsPrefix_succ
#print axioms FgStrip.CommonEdge.prefix_ready
#print axioms FgStrip.CommonEdge.forward_target_row
#print axioms FgStrip.CommonEdge.forward_sink
#print axioms FgStrip.CommonEdge.diagonal_zero
#print axioms FgStrip.CommonEdge.diagonal_parts
#print axioms FgStrip.CommonEdge.top_diagonal
#print axioms FgStrip.CommonEdge.lower_diagonal_zero
#print axioms FgStrip.CommonEdge.previousCorrection
#print axioms FgStrip.CommonEdge.nextCorrection
#print axioms FgStrip.CommonEdge.top_diagonal_correction
#print axioms FgStrip.CommonEdge.diagonalWord_nodup
#print axioms FgStrip.CommonEdge.diagonalWord_disconnected
#print axioms FgStrip.CommonEdge.target_after_diagonal
#print axioms FgStrip.CommonEdge.lower_after_diagonal
#print axioms FgStrip.CommonEdge.support
#print axioms FgStrip.CommonEdge.live
#print axioms FgStrip.CommonEdge.endpoints
#print axioms FgStrip.CommonEdge.finish
#print axioms FgStrip.CommonEdge.e
#print axioms FgStrip.CommonEdge.e_nonneg
#print axioms FgStrip.CommonEdge.e_zero_bottom
#print axioms FgStrip.CommonEdge.mem_live_iff
#print axioms FgStrip.CommonEdge.live_halfturn
#print axioms FgStrip.CommonEdge.endpoints_live
#print axioms FgStrip.CommonEdge.endpoints_supported
#print axioms FgStrip.CommonEdge.deleted_exact
#print axioms FgStrip.CommonEdge.diag
#print axioms FgStrip.CommonEdge.diag_i
#print axioms FgStrip.CommonEdge.diag_j
#print axioms FgStrip.CommonEdge.diag_live
#print axioms FgStrip.CommonEdge.X_live
#print axioms FgStrip.CommonEdge.wordLive
#print axioms FgStrip.CommonEdge.wordLive_false
#print axioms FgStrip.CommonEdge.pivotRegion
#print axioms FgStrip.CommonEdge.pivot_live
#print axioms FgStrip.CommonEdge.pivot_supported
#print axioms FgStrip.CommonEdge.pivot_avoids
#print axioms FgStrip.CommonEdge.forwardMove
#print axioms FgStrip.CommonEdge.forwardMove_supported
#print axioms FgStrip.CommonEdge.afterFirst
#print axioms FgStrip.CommonEdge.first_sequence
#print axioms FgStrip.CommonEdge.secondMap
#print axioms FgStrip.CommonEdge.secondLift
#print axioms FgStrip.CommonEdge.secondMap_lift
#print axioms FgStrip.CommonEdge.secondMap_injective
#print axioms FgStrip.CommonEdge.second_move
#print axioms FgStrip.CommonEdge.distinct_sequence
#print axioms FgStrip.CommonEdge.common_edge_sequence
#print axioms FgStrip.CommonEdge.row_mutate_zero
#print axioms FgStrip.CommonEdge.row_mutateWord_zero
#print axioms FgStrip.CommonEdge.rowCorrection
#print axioms FgStrip.CommonEdge.independent_word_row
#print axioms FgStrip.CommonEdge.range_indicator_sum
#print axioms FgStrip.CommonEdge.diagonal_row
#print axioms FgStrip.CommonEdge.lower_row
#print axioms FgStrip.CommonEdge.coincident_row
#print axioms FgStrip.CommonEdge.first_column_left_zero
#print axioms FgStrip.CommonEdge.target_upper_zero
#print axioms FgStrip.CommonEdge.omitted_diagonal_zero
#print axioms FgStrip.CommonEdge.lowerPoint
#print axioms FgStrip.CommonEdge.lowerPoint_i
#print axioms FgStrip.CommonEdge.lowerPoint_j
#print axioms FgStrip.CommonEdge.columnPath_lowerPoint
#print axioms FgStrip.CommonEdge.SweepState
#print axioms FgStrip.CommonEdge.SweepState.step
#print axioms FgStrip.CommonEdge.SweepState.column_prefix
#print axioms FgStrip.CommonEdge.SweepState.column
#print axioms FgStrip.CommonEdge.SweepState.next
#print axioms FgStrip.CommonEdge.initial_state
#print axioms FgStrip.CommonEdge.anchor
#print axioms FgStrip.CommonEdge.pivotNeg
#print axioms FgStrip.CommonEdge.pivotPos
#print axioms FgStrip.CommonEdge.pivotRow
#print axioms FgStrip.CommonEdge.originalLower
#print axioms FgStrip.CommonEdge.columnLower
#print axioms FgStrip.CommonEdge.sweepRow
#print axioms FgStrip.CommonEdge.targetRow
#print axioms FgStrip.CommonEdge.e_mul
#print axioms FgStrip.CommonEdge.pivot_parts
#print axioms FgStrip.CommonEdge.sweep_entry
#print axioms FgStrip.CommonEdge.sweep_entry_after
#print axioms FgStrip.CommonEdge.target_entry
#print axioms FgStrip.CommonEdge.sweep_step
#print axioms FgStrip.CommonEdge.target_step
#print axioms FgStrip.CommonEdge.top_after_diagonal_interval
#print axioms FgStrip.CommonEdge.top_after_diagonal
#print axioms FgStrip.CommonEdge.sequence_restrict
#print axioms FgStrip.CommonEdge.sequence_neg
#print axioms FgStrip.CommonEdge.interface_disjoint
#print axioms FgStrip.CommonEdge.coincident_restrict_add
#print axioms FgStrip.CommonEdge.start
#print axioms FgStrip.CommonEdge.target
#print axioms FgStrip.CommonEdge.diagonalPath
#print axioms FgStrip.CommonEdge.diagonalWord
#print axioms FgStrip.CommonEdge.columnPath
#print axioms FgStrip.CommonEdge.columnWord
#print axioms FgStrip.CommonEdge.columnsWord
#print axioms FgStrip.CommonEdge.forwardWord
#print axioms FgStrip.CommonEdge.target_i
#print axioms FgStrip.CommonEdge.target_j
#print axioms FgStrip.CommonEdge.diagonalPath_i
#print axioms FgStrip.CommonEdge.diagonalPath_j
#print axioms FgStrip.CommonEdge.columnPath_i
#print axioms FgStrip.CommonEdge.columnPath_j
#print axioms FgStrip.CommonEdge.diagonalWord_region
#print axioms FgStrip.CommonEdge.columnWord_region
#print axioms FgStrip.CommonEdge.forwardWord_region
#print axioms FgStrip.CommonEdge.forwardWord_supported
#print axioms FgStrip.CommonEdge.forwardWord_avoids
#print axioms FgStrip.CommonEdge.deletionWord
#print axioms FgStrip.CommonEdge.deletionWord_map
#print axioms FgStrip.CommonEdge.deletionWord_supported
#print axioms FgStrip.CommonEdge.common_edge_deletion
#print axioms FgStrip.CommonEdge.common_edge_restrict
#print axioms FgStrip.CommonEdge.common_edge_reverse
#print axioms FgStrip.CommonEdge.common_edge_ambient
#print axioms FgStrip.CommonEdge.common_edge_reverse_ambient
