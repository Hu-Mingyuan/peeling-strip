import FgStrip.TwoTriangle.Coordinates

namespace FgStrip.TwoTriangle
open Triangle

def rot {n} (p : Triangle.Vertex n) : Triangle.Vertex n :=
  Triangle.Vertex.mk p.b p.c p.a (by have := p.total; omega) p.b_lt p.c_lt p.a_lt
def swap {n} (p : Triangle.Vertex n) : Triangle.Vertex n :=
  Triangle.Vertex.mk p.b p.a p.c (by have := p.total; omega) p.b_lt p.a_lt p.c_lt
@[simp] theorem rot_rot_rot {n} (p : Triangle.Vertex n) : rot (rot (rot p)) = p := by
  apply Triangle.Vertex.ext <;> rfl
@[simp] theorem swap_swap {n} (p : Triangle.Vertex n) : swap (swap p) = p := by
  apply Triangle.Vertex.ext <;> rfl

def cellRot {n} (t : Cell n) : Cell n :=
  ⟨(t.1.2.1, t.1.2.2, t.1.1), by have := t.total; dsimp [Cell.a, Cell.b, Cell.c] at *; omega⟩
def cellSwap {n} (t : Cell n) : Cell n :=
  ⟨(t.1.2.1, t.1.1, t.1.2.2), by have := t.total; dsimp [Cell.a, Cell.b, Cell.c] at *; omega⟩
def cellRotEquiv (n : ℕ) : Cell n ≃ Cell n where
  toFun := cellRot
  invFun := cellRot ∘ cellRot
  left_inv _ := rfl
  right_inv _ := rfl
def cellSwapEquiv (n : ℕ) : Cell n ≃ Cell n where
  toFun := cellSwap
  invFun := cellSwap
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem rot_first {n} (t : Cell n) : rot t.first = (cellRot t).third := by
  apply Triangle.Vertex.ext <;> rfl
@[simp] theorem rot_second {n} (t : Cell n) : rot t.second = (cellRot t).first := by
  apply Triangle.Vertex.ext <;> rfl
@[simp] theorem rot_third {n} (t : Cell n) : rot t.third = (cellRot t).second := by
  apply Triangle.Vertex.ext <;> rfl
@[simp] theorem swap_first {n} (t : Cell n) : swap t.first = (cellSwap t).first := by
  apply Triangle.Vertex.ext <;> rfl
@[simp] theorem swap_second {n} (t : Cell n) : swap t.second = (cellSwap t).third := by
  apply Triangle.Vertex.ext <;> rfl
@[simp] theorem swap_third {n} (t : Cell n) : swap t.third = (cellSwap t).second := by
  apply Triangle.Vertex.ext <;> rfl

theorem cycleEntry_cyclic {V} [DecidableEq V] (a b c u v : V) :
    cycleEntry c a b u v = cycleEntry a b c u v := by
  simp only [cycleEntry, cycleCount, Nat.cast_add]; ring

theorem cycleEntry_reverse {V} [DecidableEq V] (a b c u v : V) :
    cycleEntry a c b u v = -cycleEntry a b c u v := by
  simp only [cycleEntry, cycleCount, Nat.cast_add]
  simp only [and_comm]
  ring

theorem cycleEntry_map {V W} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (a b c u v : V) :
    cycleEntry (f a) (f b) (f c) (f u) (f v) = cycleEntry a b c u v := by
  simp only [cycleEntry, cycleCount, hf.eq_iff]

theorem mapMatrix_rot {n V} [DecidableEq V] (f : Triangle.Vertex n → V) (u v : V) :
    mapMatrix (f ∘ rot) u v = mapMatrix f u v := by
  simp only [mapMatrix_eq_sum, Function.comp_apply, rot_first, rot_second, rot_third,
    cycleEntry_cyclic]
  exact Fintype.sum_equiv (cellRotEquiv n) _ _ (fun _ => rfl)

theorem mapMatrix_swap {n V} [DecidableEq V] (f : Triangle.Vertex n → V) (u v : V) :
    mapMatrix (f ∘ swap) u v = -mapMatrix f u v := by
  simp only [mapMatrix_eq_sum, Function.comp_apply, swap_first, swap_second, swap_third]
  rw [← Finset.sum_neg_distrib]
  apply Fintype.sum_equiv (cellSwapEquiv n)
  intro t
  exact cycleEntry_reverse _ _ _ _ _

theorem mapMatrix_map {n V W} [DecidableEq V] [DecidableEq W]
    (f : Triangle.Vertex n → V) (g : V → W) (hg : Function.Injective g) (u v : V) :
    mapMatrix (g ∘ f) (g u) (g v) = mapMatrix f u v := by
  simp only [mapMatrix_eq_sum, Function.comp_apply, cycleEntry_map g hg]

theorem HSquare_x {n} (p : Triangle.Vertex n) : HSquare (x p) = y (rot (rot p)) := by
  have := p.total
  apply Prod.ext <;> apply Fin.ext <;> simp [HSquare, x, y, rot, Fin.rev] <;> omega
theorem HSquare_y {n} (p : Triangle.Vertex n) : HSquare (y p) = x (rot p) := by
  have := p.total
  apply Prod.ext <;> apply Fin.ext <;> simp [HSquare, x, y, rot, Fin.rev] <;> omega

/-- Actual signed cycle sum on the square. No adjacency or deletion property is assumed. -/
def squareMatrix (n : ℕ) : Matrix (Square n) (Square n) ℤ :=
  fun u v => mapMatrix x u v + mapMatrix y u v
def matrix (n : ℕ) : Matrix (Grid n) (Grid n) ℤ :=
  fun u v => squareMatrix n u.1 v.1

theorem matrix_cycle_sum {n} (u v : Grid n) :
    matrix n u v =
      (∑ t : Cell n, cycleEntry (x t.first) (x t.second) (x t.third) u.1 v.1) +
      ∑ t : Cell n, cycleEntry (y t.first) (y t.second) (y t.third) u.1 v.1 := by
  simp only [matrix, squareMatrix, mapMatrix_eq_sum]

/-- A complete computable entry formula. The six ordered pairs in each cell are
listed explicitly; this applies on the diagonal and both interfaces as well. -/
def entry (n : ℕ) (u v : Square n) : ℤ :=
  ∑ t : Cell n,
    (cycleEntry
      (⟨t.b+t.c+1, by have := t.total; omega⟩, ⟨t.c, by have := t.total; omega⟩)
      (⟨t.b+t.c+2, by have := t.total; omega⟩, ⟨t.c+1, by have := t.total; omega⟩)
      (⟨t.b+t.c+1, by have := t.total; omega⟩, ⟨t.c+1, by have := t.total; omega⟩) u v +
    cycleEntry
      (⟨t.b+1, by have := t.total; omega⟩, ⟨t.b+t.c+1, by have := t.total; omega⟩)
      (⟨t.b+1, by have := t.total; omega⟩, ⟨t.b+t.c+2, by have := t.total; omega⟩)
      (⟨t.b, by have := t.total; omega⟩, ⟨t.b+t.c+1, by have := t.total; omega⟩) u v)

theorem matrix_entry {n} (u v : Grid n) : matrix n u v = entry n u.1 v.1 := by
  rw [matrix_cycle_sum, ← Finset.sum_add_distrib]
  unfold entry
  apply Finset.sum_congr rfl
  intro t _
  simp only [x, y, Cell.first, Cell.second, Cell.third, Triangle.Vertex.mk_b,
    Triangle.Vertex.mk_c]
  have h1 : t.b+1+t.c = t.b+t.c+1 := by omega
  have h2 : t.b+1+(t.c+1) = t.b+t.c+2 := by omega
  simp only [h1, h2, Nat.add_assoc]

theorem matrix_skew {n} (u v : Grid n) : matrix n u v = -matrix n v u := by
  simp only [matrix, squareMatrix]
  rw [mapMatrix_skew x, mapMatrix_skew y]; ring

theorem squareMatrix_halfturn {n} (u v : Square n) :
    squareMatrix n (HSquare u) (HSquare v) = squareMatrix n u v := by
  have hx : mapMatrix (HSquare ∘ x) u v = mapMatrix y u v := by
    have he : HSquare ∘ (@x n) = (y ∘ rot) ∘ rot := funext HSquare_x
    rw [he, mapMatrix_rot, mapMatrix_rot]
  have hy : mapMatrix (HSquare ∘ y) u v = mapMatrix x u v := by
    have he : HSquare ∘ (@y n) = x ∘ rot := funext HSquare_y
    rw [he, mapMatrix_rot]
  have hx' := mapMatrix_map x HSquare HSquare_injective (HSquare u) (HSquare v)
  have hy' := mapMatrix_map y HSquare HSquare_injective (HSquare u) (HSquare v)
  simp only [HSquare_HSquare] at hx' hy'
  unfold squareMatrix
  rw [← hx', ← hy', hx, hy]
  omega

theorem matrix_halfturn {n} (u v : Grid n) : matrix n (H u) (H v) = matrix n u v :=
  squareMatrix_halfturn u.1 v.1
end FgStrip.TwoTriangle
