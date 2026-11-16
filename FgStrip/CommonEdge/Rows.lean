import FgStrip.CommonEdge.Geometry

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

/-- Complete original diagonal expression, derived from the two cycle sums. -/
theorem diagonal_row {n k} (h0 : 0 < k) (hn : k < n) (v : Grid n) :
    matrix n (diag k h0 hn) v =
      e k (k-1) v + e k (k+1) v - e (k+1) k v - e (k-1) k v := by
  let u := diag k h0 hn
  have ui : u.i=k := rfl
  have uj : u.j=k := rfl
  have vi := v.i_le; have vj := v.j_pos; have vn := v.j_lt
  change matrix n u v = _
  have h1 : (u.j < u.i ∧ u.i < n ∧ v.i=u.i+1 ∧ v.j=u.j+1) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h2 : (u.j < u.i ∧ v.i+1=u.i ∧ v.j=u.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h3 : (u.j ≤ u.i ∧ u.i < n ∧ v.i=u.i ∧ v.j+1=u.j) ↔ (v.i=k ∧ v.j=k-1) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h4 : (0 < u.i ∧ u.i ≤ u.j ∧ v.i=u.i ∧ v.j=u.j+1) ↔ (v.i=k ∧ v.j=k+1) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h5 : (0 < u.i ∧ u.i < u.j ∧ v.i+1=u.i ∧ v.j+1=u.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h6 : (u.i < u.j ∧ v.i=u.i+1 ∧ v.j=u.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h7 : (v.j < v.i ∧ v.i < n ∧ u.i=v.i+1 ∧ u.j=v.j+1) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h8 : (v.j < v.i ∧ u.i+1=v.i ∧ u.j=v.j) ↔ (v.i=k+1 ∧ v.j=k) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h9 : (v.j ≤ v.i ∧ v.i < n ∧ u.i=v.i ∧ u.j+1=v.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h10 : (0 < v.i ∧ v.i ≤ v.j ∧ u.i=v.i ∧ u.j=v.j+1) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h11 : (0 < v.i ∧ v.i < v.j ∧ u.i+1=v.i ∧ u.j+1=v.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h12 : (v.i < v.j ∧ u.i=v.i+1 ∧ u.j=v.j) ↔ (v.i=k-1 ∧ v.j=k) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  rw [matrix_formula]
  simp only [arrows, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, if_false, zero_add, add_zero, e]
  ring

/-- Complete original lower-triangle expression, with all interface coefficients. -/
theorem lower_row {n i j} (h0 : 0 < j) (hji : j < i) (hi : i < n) (v : Grid n) :
    matrix n (X i j h0 hji hi) v =
      e (i+1) (j+1) v - e (i+1) j v - e i (j+1) v +
      e i (j-1) v + e (i-1) j v - e (i-1) (j-1) v := by
  let u := X i j h0 hji hi
  have ui : u.i=i := rfl
  have uj : u.j=j := rfl
  have vi := v.i_le; have vj := v.j_pos; have vn := v.j_lt
  change matrix n u v = _
  have h1 : (u.j < u.i ∧ u.i < n ∧ v.i=u.i+1 ∧ v.j=u.j+1) ↔ (v.i=i+1 ∧ v.j=j+1) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h2 : (u.j < u.i ∧ v.i+1=u.i ∧ v.j=u.j) ↔ (v.i=i-1 ∧ v.j=j) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h3 : (u.j ≤ u.i ∧ u.i < n ∧ v.i=u.i ∧ v.j+1=u.j) ↔ (v.i=i ∧ v.j=j-1) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h4 : (0 < u.i ∧ u.i ≤ u.j ∧ v.i=u.i ∧ v.j=u.j+1) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h5 : (0 < u.i ∧ u.i < u.j ∧ v.i+1=u.i ∧ v.j+1=u.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h6 : (u.i < u.j ∧ v.i=u.i+1 ∧ v.j=u.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h7 : (v.j < v.i ∧ v.i < n ∧ u.i=v.i+1 ∧ u.j=v.j+1) ↔ (v.i=i-1 ∧ v.j=j-1) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h8 : (v.j < v.i ∧ u.i+1=v.i ∧ u.j=v.j) ↔ (v.i=i+1 ∧ v.j=j) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h9 : (v.j ≤ v.i ∧ v.i < n ∧ u.i=v.i ∧ u.j+1=v.j) ↔ (v.i=i ∧ v.j=j+1) := by dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h10 : (0 < v.i ∧ v.i ≤ v.j ∧ u.i=v.i ∧ u.j=v.j+1) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h11 : (0 < v.i ∧ v.i < v.j ∧ u.i+1=v.i ∧ u.j+1=v.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  have h12 : (v.i < v.j ∧ u.i=v.i+1 ∧ u.j=v.j) ↔ (False) := by simp only [iff_false]; dsimp [u, diag, D, X, Grid.i, Grid.j, Triangle.EdgeWeight.val] at *; omega
  rw [matrix_formula]
  simp only [arrows, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, if_false, zero_add, add_zero, e]
  ring

/-- At the even central layer the endpoint is already a sink. The formula
includes the rank-two interface labels `(2,1)` and `(0,1)`. -/
theorem coincident_row {n p} (hn : n = 2*p+2) (v : live (n := n) p) :
    matrix n (diag (p+1) (by omega) (by omega)) v.val =
      - e (p+2) (p+1) v.val - e p (p+1) v.val := by
  rw [diagonal_row]
  have hv := (mem_live_iff v.val).mp v.property
  have h0 := v.val.j_pos; have hi := v.val.i_le; have hj := v.val.j_lt
  have h₁ : e (p+1) (p+1-1) v.val = 0 := by
    unfold e
    split_ifs <;> simp_all only [Nat.cast_one, Nat.cast_zero, Grid.i, Grid.j] <;> omega
  have h₂ : e (p+1) (p+1+1) v.val = 0 := by
    unfold e
    split_ifs <;> simp_all only [Nat.cast_one, Nat.cast_zero, Grid.i, Grid.j] <;> omega
  rw [h₁,h₂]
  simp only [show p+1-1 = p by omega, show p+1+1 = p+2 by omega]
  ring

/-- The left neighbours of the first column lie in the deleted corner. -/
theorem first_column_left_zero {n p j b} (hn : 2*p+3 ≤ n) (hj : j < p+1)
    (v : wordLive (n := n) p b) : e (p+1) j v.val=0 := by
  have hv := (mem_live_iff v.val).mp v.property.1
  have hvj := v.val.j_pos
  unfold e
  split_ifs <;> omega

/-- The upper neighbour of the deletion vertex is absent, including `p=0`. -/
theorem target_upper_zero {n p b} (hn : 2*p+3 ≤ n)
    (v : wordLive (n := n) p b) : e (n-p-1) (n-p) v.val=0 := by
  have hv := (mem_live_iff v.val).mp v.property.1
  have hvj := v.val.j_lt
  unfold e
  split_ifs <;> omega

/-- The removed first pivot contributes zero on the modified live type. -/
theorem omitted_diagonal_zero {n p} (v : wordLive (n := n) p true) :
    e (p+1) (p+1) v.val=0 := by
  have hv := v.property.2 rfl
  simp only [e, if_neg hv]

end FgStrip.CommonEdge
