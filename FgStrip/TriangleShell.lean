import FgStrip.TriangleShell.Execution

/-! Triangle-interior shell deletion for the actual elementary-cycle matrix.
Source: proof-blueprint Section 2; references/main.tex:3575–3654.
The side depth remains `p`; the deleted interior grows from `C_p` to `C_(p+1)`. -/

namespace FgStrip.TriangleShell
open Triangle

/-- Exactly the new shell is removed, including in the odd overlap case. -/
theorem shell_deleted_exact {n p : ℕ} (hn : 2*p+1 ≤ n) :
    baseLive (n := n) p \ (baseLive p \ cornerSet (p+1)) =
      cornerSet (p+1) \ cornerSet p := by
  ext j
  have ht := j.total
  simp only [baseLive, cornerSet, Set.mem_sdiff, Set.mem_ofPred_eq]
  omega

/-- The manuscript's full permitted range, with the actual operation's exact output. -/
theorem triangle_interior_shell {n p : ℕ} (hp : 1 ≤ p) (hpn : p ≤ (n-1)/2) :
    Sequence (matrix n) (interiorSet n) (baseLive p) (baseLive p \ cornerSet (p+1)) ∧
    Execution (interiorSet n) (restrictMatrix (matrix n) (Subtype.val : baseLive p → Vertex n))
      (restrictMatrix (matrix n) (Subtype.val : ↥(baseLive (n := n) p \ cornerSet (p+1)) → Vertex n)) ∧
    baseLive (n := n) p \ (baseLive p \ cornerSet (p+1)) =
      cornerSet (p+1) \ cornerSet p := by
  have hn : 2*p+1 ≤ n := by omega
  have h := shell_deletion hp hn
  exact ⟨h,h.execution,shell_deleted_exact hn⟩

/-- Complementary-block additions are allowed throughout the entire shell sequence. -/
theorem triangle_interior_shell_add {n p : ℕ} (hp : 1 ≤ p) (hpn : p ≤ (n-1)/2)
    (E : Matrix (Vertex n) (Vertex n) ℤ) (hE : SkewSymmetric E)
    (hz : ∀ k ∈ interiorSet n, ∀ j, E k j=0) :
    Execution (interiorSet n)
      (restrictMatrix (matrix n+E) (Subtype.val : baseLive p → Vertex n))
      (restrictMatrix (matrix n+E) (Subtype.val : ↥(baseLive (n := n) p \ cornerSet (p+1)) → Vertex n)) :=
  ((triangle_interior_shell hp hpn).1.add E hE hz).execution

end FgStrip.TriangleShell
