import FgStrip.Mutation
import FgStrip.Deletion

namespace FgStrip.MutationFoundations861de069

/-- The literal formula in target-theorem Section 2, including the subtraction order. -/
theorem manuscript_formula {V : Type*} [DecidableEq V]
    (B : Matrix V V ℤ) (k i j : V) :
    mutate B k i j = if i = k ∨ j = k then -B i j else
      B i j + max (B i k) 0 * max (B k j) 0 -
        max (-B i k) 0 * max (-B k j) 0 := by
  simp only [mutate, mutationTerm, posPart]
  split_ifs <;> ring

theorem listed_order {V : Type*} [DecidableEq V]
    (B : Matrix V V ℤ) (k₁ k₂ : V) :
    mutateWord B [k₁, k₂] = mutate (mutate B k₁) k₂ := rfl

/-- Finite ambient sets may contain arbitrary protected and exterior vertices. -/
theorem ambient_word {V : Type*} [Fintype V] [DecidableEq V]
    (B E : Matrix V V ℤ) (hE : SkewSymmetric E) (I : Set V)
    (hI : ∀ k ∈ I, ∀ j, E k j = 0) (W : List V) (hW : ∀ k ∈ W, k ∈ I) :
    mutateWord (B + E) W = mutateWord B W + E :=
  mutateWord_add_of_support B E hE I hI W hW

/-- A move on an arbitrary live subset restores every retained ambient entry. -/
theorem live_output {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℤ) (U : Set V)
    (d : DeletionMove U (restrictMatrix A Subtype.val)) :
    ∀ i j : Remaining d.vertex, d.output i j = A i.val.val j.val.val :=
  d.output_original A

end FgStrip.MutationFoundations861de069

#print axioms FgStrip.MutationFoundations861de069.manuscript_formula
#print axioms FgStrip.MutationFoundations861de069.listed_order
#print axioms FgStrip.MutationFoundations861de069.ambient_word
#print axioms FgStrip.MutationFoundations861de069.live_output

-- Each audit is transitive, including the proofs of all invoked local helpers.
#print axioms FgStrip.SkewSymmetric
#print axioms FgStrip.posPart
#print axioms FgStrip.mutationTerm
#print axioms FgStrip.mutationTerm_neg
#print axioms FgStrip.mutationTerm_swap
#print axioms FgStrip.mutate
#print axioms FgStrip.mutate_row
#print axioms FgStrip.mutate_col
#print axioms FgStrip.mutate_of_ne
#print axioms FgStrip.SkewSymmetric.mutate
#print axioms FgStrip.mutate_involutive
#print axioms FgStrip.mutate_neg
#print axioms FgStrip.restrictMatrix
#print axioms FgStrip.restrictMatrix_apply
#print axioms FgStrip.SkewSymmetric.restrictMatrix
#print axioms FgStrip.restrictMatrix_comp
#print axioms FgStrip.restrictMatrix_mutate
#print axioms FgStrip.mutateWord
#print axioms FgStrip.mutateWord_nil
#print axioms FgStrip.mutateWord_cons
#print axioms FgStrip.mutateWord_append
#print axioms FgStrip.mutateWord_reverse
#print axioms FgStrip.SkewSymmetric.mutateWord
#print axioms FgStrip.mutateWord_neg
#print axioms FgStrip.restrictMatrix_mutateWord
#print axioms FgStrip.reindex_mutateWord
#print axioms FgStrip.SkewSymmetric.col_zero
#print axioms FgStrip.mutate_add_of_row_zero
#print axioms FgStrip.mutateWord_add_of_rows_zero
#print axioms FgStrip.mutateWord_add_of_support
#print axioms FgStrip.IsSource
#print axioms FgStrip.IsSink
#print axioms FgStrip.SourceOrSink
#print axioms FgStrip.SourceOrSink.neg
#print axioms FgStrip.SourceOrSink.restrictMatrix
#print axioms FgStrip.Remaining
#print axioms FgStrip.deletionUndo
#print axioms FgStrip.deletionUndo_eq_restrict
#print axioms FgStrip.restriction_undo
#print axioms FgStrip.ValidDeletionWord
#print axioms FgStrip.ValidDeletionWord.neg
#print axioms FgStrip.mutateWord_add_row
#print axioms FgStrip.validDeletionWord_add_iff
#print axioms FgStrip.mapRemaining
#print axioms FgStrip.validDeletionWord_restrict
#print axioms FgStrip.DeletionMove.pivot_live
#print axioms FgStrip.DeletionMove.liveSet
#print axioms FgStrip.DeletionMove.remainingEquiv
#print axioms FgStrip.DeletionMove.output
#print axioms FgStrip.DeletionMove.output_eq_restrict
#print axioms FgStrip.DeletionMove.output_skew
#print axioms FgStrip.DeletionMove.ofSourceOrSink
#print axioms FgStrip.DeletionMove.neg
#print axioms FgStrip.DeletionMove.output_original
