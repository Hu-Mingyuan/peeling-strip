import FgStrip.TwoTriangle.Contribution

namespace FgStrip.TwoTriangle
open Triangle

/-- Label classification is exhaustive, including both interfaces. -/
theorem label_cases {n} (u : Grid n) :
    (∃ k, u = L k) ∨ (∃ k, u = R k) ∨ (∃ k, u = D k) ∨
    (∃ i j hj hji hi, u = X i j hj hji hi) ∨
    (∃ i j hi hij hj, u = Y i j hi hij hj) := by
  have h0 := u.j_pos; have hn := u.j_lt; have hi := u.i_le
  let k : EdgeWeight n := ⟨⟨u.j, hn⟩, h0⟩
  by_cases hz : u.i = 0
  · exact Or.inl ⟨k, Grid.ext hz rfl⟩
  by_cases he : u.i = n
  · exact Or.inr (Or.inl ⟨k, Grid.ext he rfl⟩)
  by_cases hd : u.i = u.j
  · exact Or.inr (Or.inr (Or.inl ⟨k, Grid.ext hd rfl⟩))
  by_cases hl : u.j < u.i
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u.i, u.j, h0, hl, by omega, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u.i, u.j, by omega, by omega, hn, rfl⟩)))

theorem x_D {n} (k : EdgeWeight n) :
    x (Triangle.Vertex.mk (n-k.val) 0 k.val (by have := k.lt; omega)
      (by have := k.pos; have := k.lt; omega) (by have := k.lt; omega) k.lt) = (D k).1 := by
  apply Prod.ext <;> apply Fin.ext <;> simp [x, D]
theorem y_D {n} (k : EdgeWeight n) : y k.ab = (D k).1 := by
  apply Prod.ext <;> apply Fin.ext <;> simp [y, EdgeWeight.ab, D]
theorem x_R {n} (k : EdgeWeight n) : x k.bc = (R k).1 := by
  have := k.lt
  apply Prod.ext <;> apply Fin.ext <;> simp [x, EdgeWeight.bc, R] <;> omega
theorem y_L {n} (k : EdgeWeight n) :
    y (Triangle.Vertex.mk (n-k.val) 0 k.val (by have := k.lt; omega)
      (by have := k.pos; have := k.lt; omega) (by have := k.lt; omega) k.lt) = (L k).1 := by
  apply Prod.ext <;> apply Fin.ext <;> simp [y, L]

theorem x_X {n i j} (hj : 0 < j) (hji : j < i) (hi : i < n) :
    x ((X i j hj hji hi).lower (by change j ≤ i; omega)) = (X i j hj hji hi).1 :=
  Grid.x_lower _ _
theorem y_Y {n i j} (hi : 0 < i) (hij : i < j) (hj : j < n) :
    y ((Y i j hi hij hj).upper (by change i ≤ j; omega)) = (Y i j hi hij hj).1 :=
  Grid.y_upper _ _

theorem CY_rot {n} (p : ℕ) (v : Triangle.Vertex n) :
    CY p (y v) ↔ BarycentricC p (rot v) := by
  rw [CY_y_iff]; rfl

theorem BarycentricC_swap {n} (p : ℕ) (v : Triangle.Vertex n) :
    BarycentricC p (swap v) ↔ BarycentricC p v := by
  simp only [BarycentricC, swap, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b,
    Triangle.Vertex.mk_c]
  tauto

def deletedEdge {n} (p : ℕ) (u : Grid n) : Prop :=
  (u.i = 0 ∨ u.i = u.j ∨ u.i = n) ∧ EdgeDepth n p u.j

theorem deletedEdge_L {n} (p : ℕ) (k : EdgeWeight n) :
    deletedEdge p (L k) ↔ EdgeDepth n p k.val := by simp [deletedEdge, Grid.i, Grid.j, L]
theorem deletedEdge_D {n} (p : ℕ) (k : EdgeWeight n) :
    deletedEdge p (D k) ↔ EdgeDepth n p k.val := by simp [deletedEdge, Grid.i, Grid.j, D]
theorem deletedEdge_R {n} (p : ℕ) (k : EdgeWeight n) :
    deletedEdge p (R k) ↔ EdgeDepth n p k.val := by simp [deletedEdge, Grid.i, Grid.j, R]

namespace Pair
variable {n N : ℕ}
theorem CX_face (s : Pair N) (p : ℕ) (v : Triangle.Vertex n) :
    BarycentricC p (s.tx v) ↔ CX p (x v) := by
  cases s
  · exact (CX_x_iff p v).symm
  · exact (BarycentricC_swap p v).trans (CX_x_iff p v).symm

theorem CY_face (s : Pair N) (p : ℕ) (v : Triangle.Vertex n) :
    BarycentricC p (s.ty v) ↔ CY p (y v) := by
  cases s
  · exact (CY_rot p v).symm
  · exact (BarycentricC_swap p (rot v)).trans (CY_rot p v).symm

def commonEdge (s : Pair N) : Strip.EdgeIndex N :=
  match s with
  | .odd i => ⟨2*i.val+1, by have := i.isLt; omega⟩
  | .even i hi => ⟨2*i.val+2, by omega⟩
def ofEdge (j : Strip.EdgeIndex N) (h0 : 0 < j.val) (hN : j.val < 2*N) : Pair N :=
  if he : j.val % 2 = 1 then .odd ⟨j.val/2, by omega⟩
  else .even ⟨j.val/2-1, by omega⟩ (by change j.val/2-1+1 < N; omega)
@[simp] theorem commonEdge_ofEdge (j : Strip.EdgeIndex N) (h0 : 0 < j.val)
    (hN : j.val < 2*N) : (ofEdge j h0 hN).commonEdge = j := by
  apply Fin.ext
  unfold ofEdge
  split_ifs <;> dsimp [commonEdge] <;> omega

theorem remainder_D (s : Pair N) (k : EdgeWeight n) (v : Strip.Vertex n N) :
    s.remainder (s.embed (D k)) v = 0 := s.remainder_row_zero (D k) k.pos k.lt v
theorem remainder_X (s : Pair N) {i j} (hj : 0 < j) (hji : j < i) (hi : i < n)
    (v : Strip.Vertex n N) : s.remainder (s.embed (X i j hj hji hi)) v = 0 :=
  s.remainder_row_zero (X i j hj hji hi) (by change 0 < i; omega) hi v
theorem remainder_Y (s : Pair N) {i j} (hi : 0 < i) (hij : i < j) (hj : j < n)
    (v : Strip.Vertex n N) : s.remainder (s.embed (Y i j hi hij hj)) v = 0 :=
  s.remainder_row_zero (Y i j hi hij hj) hi (by change i < n; omega) v
end Pair
end FgStrip.TwoTriangle
