import FgStrip.CommonEdge.Rows

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

/-- The unique endpoint when `n = 2p+2`, on the actual live type. -/
def central {n p} (hn : n = 2*p+2) : live (n := n) p :=
  ⟨diag (p+1) (by omega) (by omega), diag_live (by omega) (by omega)⟩

/-- A concrete empty-word deletion, using the complete cycle-derived expression. -/
def coincidentMove {n p} (hn : n = 2*p+2) :
    DeletionMove (live (n := n) p) (restrictMatrix (matrix n) Subtype.val) :=
  DeletionMove.ofSourceOrSink (central hn) (Or.inr (by
    intro v
    change matrix n (diag (p+1) _ _) v.val  ≤  0
    rw [coincident_row hn]
    have := e_nonneg (i := p+2) (j := p+1) v.val
    have := e_nonneg (i := p) (j := p+1) v.val
    omega))

theorem coincidentMove_finish {n p} (hn : n = 2*p+2) :
    (coincidentMove hn).liveSet = finish p := by
  ext u
  have he : u = (coincidentMove hn).vertex.val ↔ u.i = p+1 ∧ u.j = p+1 := by
    constructor
    · intro h; subst u; exact ⟨rfl,rfl⟩
    · rintro ⟨hi,hj⟩; exact Grid.ext hi hj
  change (u ∈ live p ∧ u ≠ (coincidentMove hn).vertex.val) ↔
    (u ∈ live p ∧ u ∉ endpoints p)
  apply and_congr_right
  intro _
  rw [ne_eq, he]
  apply not_congr
  change (u.i=p+1 ∧ u.j=p+1) ↔ (u.i=u.j ∧ (u.j=p+1 ∨ u.j=n-p-1))
  omega


/-- Supported sequence for every even central layer, including `n = 2,p = 0`. -/
theorem coincident_sequence {n p} (hn : n = 2*p+2) :
    Sequence (matrix n) (support n) (live p) (finish p) := by
  apply Sequence.cons (coincidentMove hn)
  · change 0 < p+1 ∧ p+1 < n
    omega
  · intro k hk
    change k ∈ [] at hk
    simp at hk
  · rw [coincidentMove_finish hn]
    exact .nil _

/-- Actual mutation/deletion/reversal execution and its exact deleted set. -/
theorem coincident_deletion {n p} (hn : n = 2*p+2) :
    Sequence (matrix n) (support n) (live p) (finish p) ∧
    Execution (support n)
      (restrictMatrix (matrix n) (Subtype.val : live p → Grid n))
      (restrictMatrix (matrix n) (Subtype.val : finish p → Grid n)) ∧
    live (n := n) p \ finish p = endpoints p :=
  ⟨coincident_sequence hn, (coincident_sequence hn).execution, deleted_exact (by omega)⟩

end FgStrip.CommonEdge
