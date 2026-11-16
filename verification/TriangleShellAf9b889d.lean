import FgStrip.TriangleShell

namespace FgStrip.TriangleShell.AuditAf9b889d
open FgStrip.Triangle

/-- Fresh consumer of the unrestricted shell existence and actual output theorem. -/
theorem shell (n p : ℕ) (hp : 1 ≤ p) (hpn : p ≤ (n-1)/2) :
    Execution (interiorSet n)
      (restrictMatrix (matrix n) (Subtype.val : baseLive p → Vertex n))
      (restrictMatrix (matrix n)
        (Subtype.val : ↥(baseLive (n := n) p \ cornerSet (p+1)) → Vertex n)) :=
  (triangle_interior_shell hp hpn).2.1

/-- Both retained sides are in the domain of the sign quantifier. -/
theorem complete_first_sign {n p a : ℕ} (hn : 2*p+1 ≤ n) (ha : 1 ≤ a) (hap : a ≤ p) :
    SourceOrSink
      (mutateWord (restrictMatrix (matrix n) Subtype.val)
        ((firstMove hn ha hap).word.map Subtype.val)) (firstMove hn ha hap).vertex :=
  (firstMove hn ha hap).source_or_sink

/-- The small-rank endpoint is supplied by the same theorem. -/
theorem rank_three :
    Sequence (matrix 3) (interiorSet 3) (baseLive 1) (baseLive 1 \ cornerSet 2) :=
  (triangle_interior_shell (n := 3) (p := 1) (by omega) (by omega)).1

#print axioms shell
#print axioms complete_first_sign
#print axioms rank_three
end FgStrip.TriangleShell.AuditAf9b889d

#check FgStrip.TriangleShell.triangle_interior_shell
#check FgStrip.TriangleShell.first_final_row
#check FgStrip.TriangleShell.second_move
#check FgStrip.TriangleShell.pullMove
#check FgStrip.TriangleShell.firstWord_ambient
#check FgStrip.TriangleShell.validDeletionWord_ambient_restrict
#check FgStrip.TriangleShell.triangle_interior_shell_add

#print axioms FgStrip.TriangleShell.extendMatrix
#print axioms FgStrip.TriangleShell.mutate_extendMatrix
#print axioms FgStrip.TriangleShell.mutateWord_extendMatrix
#print axioms FgStrip.TriangleShell.validDeletionWord_extend
#print axioms FgStrip.TriangleShell.validDeletionWord_ambient
#print axioms FgStrip.TriangleShell.firstWord_ambient
#print axioms FgStrip.TriangleShell.validDeletionWord_ambient_restrict
#print axioms FgStrip.TriangleShell.cell_ext
#print axioms FgStrip.TriangleShell.arrowCount_eq
#print axioms FgStrip.TriangleShell.matrix_eq
#print axioms FgStrip.TriangleShell.exchange
#print axioms FgStrip.TriangleShell.exchange_a
#print axioms FgStrip.TriangleShell.exchange_b
#print axioms FgStrip.TriangleShell.exchange_c
#print axioms FgStrip.TriangleShell.exchange_exchange
#print axioms FgStrip.TriangleShell.matrix_exchange
#print axioms FgStrip.TriangleShell.stepOutput
#print axioms FgStrip.TriangleShell.stepOutput_original
#print axioms FgStrip.TriangleShell.Execution
#print axioms FgStrip.TriangleShell.Sequence.execution
#print axioms FgStrip.TriangleShell.Sequence.add
#print axioms FgStrip.TriangleShell.cornerSet
#print axioms FgStrip.TriangleShell.baseLive
#print axioms FgStrip.TriangleShell.baseLive_iff
#print axioms FgStrip.TriangleShell.firstLive
#print axioms FgStrip.TriangleShell.cornerSet_exchange
#print axioms FgStrip.TriangleShell.baseLive_exchange
#print axioms FgStrip.TriangleShell.shell_iff
#print axioms FgStrip.TriangleShell.shell_overlap
#print axioms FgStrip.TriangleShell.firstLive_start
#print axioms FgStrip.TriangleShell.lineVertex
#print axioms FgStrip.TriangleShell.lineVertex_a
#print axioms FgStrip.TriangleShell.lineVertex_b
#print axioms FgStrip.TriangleShell.lineVertex_c
#print axioms FgStrip.TriangleShell.lineVertex_interior
#print axioms FgStrip.TriangleShell.off
#print axioms FgStrip.TriangleShell.off_nonneg
#print axioms FgStrip.TriangleShell.off_line_zero
#print axioms FgStrip.TriangleShell.off_disjoint
#print axioms FgStrip.TriangleShell.onLine
#print axioms FgStrip.TriangleShell.matrix_interior_row
#print axioms FgStrip.TriangleShell.off_endpoint_zero
#print axioms FgStrip.TriangleShell.onLine_after_zero
#print axioms FgStrip.TriangleShell.onLine_zero_zero
#print axioms FgStrip.TriangleShell.linePath
#print axioms FgStrip.TriangleShell.linePath_a
#print axioms FgStrip.TriangleShell.linePath_b
#print axioms FgStrip.TriangleShell.linePath_c
#print axioms FgStrip.TriangleShell.linePath_injective
#print axioms FgStrip.TriangleShell.linePath_interior
#print axioms FgStrip.TriangleShell.onLine_eq_delta
#print axioms FgStrip.TriangleShell.linePath_original_row
#print axioms FgStrip.TriangleShell.first_final_row
#print axioms FgStrip.TriangleShell.first_word_avoids
#print axioms FgStrip.TriangleShell.firstWord
#print axioms FgStrip.TriangleShell.firstWord_map
#print axioms FgStrip.TriangleShell.rank_three_row
#print axioms FgStrip.TriangleShell.firstMove
#print axioms FgStrip.TriangleShell.firstMove_vertex
#print axioms FgStrip.TriangleShell.delta
#print axioms FgStrip.TriangleShell.delta_self
#print axioms FgStrip.TriangleShell.delta_nonneg
#print axioms FgStrip.TriangleShell.pathWord
#print axioms FgStrip.TriangleShell.pathWord_zero
#print axioms FgStrip.TriangleShell.pathWord_succ
#print axioms FgStrip.TriangleShell.path_prefix_row
#print axioms FgStrip.TriangleShell.path_final_row
#print axioms FgStrip.TriangleShell.interiorSet
#print axioms FgStrip.TriangleShell.firstMove_target_coordinates
#print axioms FgStrip.TriangleShell.firstMove_target_interior
#print axioms FgStrip.TriangleShell.firstMove_word_coordinates
#print axioms FgStrip.TriangleShell.firstMove_liveSet
#print axioms FgStrip.TriangleShell.first_sequence
#print axioms FgStrip.TriangleShell.secondLive
#print axioms FgStrip.TriangleShell.secondMap
#print axioms FgStrip.TriangleShell.secondMap_injective
#print axioms FgStrip.TriangleShell.secondLift
#print axioms FgStrip.TriangleShell.secondMap_lift
#print axioms FgStrip.TriangleShell.second_move
#print axioms FgStrip.TriangleShell.second_sequence
#print axioms FgStrip.TriangleShell.second_start
#print axioms FgStrip.TriangleShell.second_finish
#print axioms FgStrip.TriangleShell.shell_deletion
#print axioms FgStrip.TriangleShell.pullMove
#print axioms FgStrip.TriangleShell.addMove
#print axioms FgStrip.TriangleShell.Sequence
#print axioms FgStrip.TriangleShell.Sequence.trans
#print axioms FgStrip.TriangleShell.Sequence.subset
#print axioms FgStrip.TriangleShell.Sequence.deleted_interior
#print axioms FgStrip.TriangleShell.shell_deleted_exact
#print axioms FgStrip.TriangleShell.triangle_interior_shell
#print axioms FgStrip.TriangleShell.triangle_interior_shell_add
