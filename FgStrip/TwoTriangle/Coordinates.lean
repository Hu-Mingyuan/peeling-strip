import FgStrip.Strip

/-! Square coordinates of the two triangles, before any shell deletion.
Source: proof-blueprint §3 and main.tex:3767–3792. -/
namespace FgStrip.TwoTriangle
open Triangle

abbrev Square (n : ℕ) := Fin (n + 1) × Fin (n + 1)
abbrev Grid (n : ℕ) := {u : Square n // 0 < u.2.val ∧ u.2.val < n}
deriving instance DecidableEq, Fintype for Grid

def x {n} (p : Triangle.Vertex n) : Square n :=
  (⟨p.b + p.c, by have := p.total; omega⟩, ⟨p.c, by have := p.c_lt; omega⟩)
def y {n} (p : Triangle.Vertex n) : Square n :=
  (⟨p.b, by have := p.b_lt; omega⟩, ⟨p.b + p.c, by have := p.total; omega⟩)

theorem x_injective {n} : Function.Injective (@x n) := by
  intro p q h
  have h1 := congrArg (fun z : Square n => z.1.val) h
  have h2 := congrArg (fun z : Square n => z.2.val) h
  simp only [x] at h1 h2
  have := p.total; have := q.total
  apply Triangle.Vertex.ext <;> omega

theorem y_injective {n} : Function.Injective (@y n) := by
  intro p q h
  have h1 := congrArg (fun z : Square n => z.1.val) h
  have h2 := congrArg (fun z : Square n => z.2.val) h
  simp only [y] at h1 h2
  have := p.total; have := q.total
  apply Triangle.Vertex.ext <;> omega

theorem x_eq_y_iff {n} (p q : Triangle.Vertex n) :
    x p = y q ↔ p.b = 0 ∧ q.c = 0 ∧ p.a = q.a ∧ p.c = q.b := by
  have := p.total; have := q.total
  simp only [x, y, Prod.mk.injEq, Fin.mk.injEq]
  omega

theorem x_retained_iff {n} (p : Triangle.Vertex n) :
    (0 < (x p).2.val ∧ (x p).2.val < n) ↔ 0 < p.c := by
  simp only [x]; exact and_iff_left p.c_lt

theorem y_retained_iff {n} (p : Triangle.Vertex n) :
    (0 < (y p).2.val ∧ (y p).2.val < n) ↔ 0 < p.a := by
  have := p.total; have := p.a_lt
  simp only [y]; omega

namespace Grid
variable {n : ℕ}
def i (u : Grid n) : ℕ := u.1.1.val
def j (u : Grid n) : ℕ := u.1.2.val
theorem i_le (u : Grid n) : u.i ≤ n := by have := u.1.1.isLt; exact Nat.le_of_lt_succ this
theorem j_pos (u : Grid n) : 0 < u.j := u.2.1
theorem j_lt (u : Grid n) : u.j < n := u.2.2
@[ext] theorem ext {u v : Grid n} (hi : u.i = v.i) (hj : u.j = v.j) : u = v :=
  Subtype.ext (Prod.ext (Fin.ext hi) (Fin.ext hj))

def lower (u : Grid n) (h : u.j ≤ u.i) : Triangle.Vertex n :=
  Triangle.Vertex.mk (n-u.i) (u.i-u.j) u.j
    (by have := u.i_le; omega) (by have := u.j_pos; have := u.j_lt; omega)
    (by have := u.i_le; have := u.j_pos; omega) u.j_lt

def upper (u : Grid n) (h : u.i ≤ u.j) : Triangle.Vertex n :=
  Triangle.Vertex.mk (n-u.j) u.i (u.j-u.i)
    (by have := u.j_lt; omega) (by have := u.j_pos; have := u.j_lt; omega)
    (by have := u.j_lt; omega) (by have := u.j_lt; omega)

@[simp] theorem x_lower (u : Grid n) (h : u.j ≤ u.i) : x (u.lower h) = u.1 := by
  apply Prod.ext <;> apply Fin.ext
  · change u.i-u.j+u.j = u.i; omega
  · rfl
@[simp] theorem y_upper (u : Grid n) (h : u.i ≤ u.j) : y (u.upper h) = u.1 := by
  apply Prod.ext <;> apply Fin.ext
  · rfl
  · change u.i+(u.j-u.i) = u.j; omega

theorem covered (u : Grid n) :
    (∃ p, 0 < p.c ∧ x p = u.1) ∨ (∃ p, 0 < p.a ∧ y p = u.1) := by
  by_cases h : u.j ≤ u.i
  · exact Or.inl ⟨u.lower h, u.j_pos, u.x_lower h⟩
  · have h' : u.i ≤ u.j := by omega
    exact Or.inr ⟨u.upper h', by dsimp [upper]; have := u.j_lt; omega, u.y_upper h'⟩
end Grid

def L {n} (k : EdgeWeight n) : Grid n :=
  ⟨(⟨0, by have := k.lt; omega⟩, ⟨k.val, by have := k.lt; omega⟩), k.pos, k.lt⟩
def D {n} (k : EdgeWeight n) : Grid n :=
  ⟨(⟨k.val, by have := k.lt; omega⟩, ⟨k.val, by have := k.lt; omega⟩), k.pos, k.lt⟩
def R {n} (k : EdgeWeight n) : Grid n :=
  ⟨(⟨n, by omega⟩, ⟨k.val, by have := k.lt; omega⟩), k.pos, k.lt⟩
def X {n} (i j : ℕ) (hj : 0 < j) (hji : j < i) (hi : i < n) : Grid n :=
  ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hj, by change j < n; omega⟩
def Y {n} (i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < n) : Grid n :=
  ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), by change 0 < j; omega, hj⟩

def HSquare {n} (u : Square n) : Square n := (u.1.rev, u.2.rev)
@[simp] theorem HSquare_HSquare {n} (u : Square n) : HSquare (HSquare u) = u := by
  simp [HSquare]
theorem HSquare_injective {n} : Function.Injective (@HSquare n) := by
  intro u v h
  simpa using congrArg HSquare h

def H {n} (u : Grid n) : Grid n :=
  ⟨HSquare u.1, by simp only [HSquare, Fin.val_rev]; change 0 < n+1-(u.j+1) ∧ n+1-(u.j+1) < n; have := u.j_pos; have := u.j_lt; omega⟩
@[simp] theorem H_i {n} (u : Grid n) : (H u).i = n-u.i := by simp [Grid.i, H, HSquare, Fin.rev]
@[simp] theorem H_j {n} (u : Grid n) : (H u).j = n-u.j := by simp [Grid.j, H, HSquare, Fin.rev]
@[simp] theorem H_H {n} (u : Grid n) : H (H u) = u := by
  apply Subtype.ext; exact HSquare_HSquare u.1

def reverseWeight {n} (k : EdgeWeight n) : EdgeWeight n :=
  ⟨⟨n-k.val, by have := k.pos; have := k.lt; omega⟩, by change 0 < n-k.val; have := k.lt; omega⟩
@[simp] theorem H_D {n} (k : EdgeWeight n) : H (D k) = D (reverseWeight k) := by
  apply Grid.ext <;> simp [Grid.i, Grid.j, H, HSquare, D, reverseWeight, EdgeWeight.val, Fin.rev]
@[simp] theorem H_L {n} (k : EdgeWeight n) : H (L k) = R (reverseWeight k) := by
  apply Grid.ext <;> simp [Grid.i, Grid.j, H, HSquare, L, R, reverseWeight, EdgeWeight.val, Fin.rev]
@[simp] theorem H_R {n} (k : EdgeWeight n) : H (R k) = L (reverseWeight k) := by
  apply Grid.ext <;> simp [Grid.i, Grid.j, H, HSquare, L, R, reverseWeight, EdgeWeight.val, Fin.rev]
theorem H_X {n i j} (hj : 0 < j) (hji : j < i) (hi : i < n) :
    H (X i j hj hji hi) = Y (n-i) (n-j) (by omega) (by omega) (by omega) := by
  apply Grid.ext <;> simp [Grid.i, Grid.j, H, HSquare, X, Y, Fin.rev]
theorem H_Y {n i j} (hi : 0 < i) (hij : i < j) (hj : j < n) :
    H (Y i j hi hij hj) = X (n-i) (n-j) (by omega) (by omega) (by omega) := by
  apply Grid.ext <;> simp [Grid.i, Grid.j, H, HSquare, X, Y, Fin.rev]

/-- Deleted portions of any of the three transverse edges. -/
def EdgeDepth (n p k : ℕ) : Prop := k ≤ p ∨ n-p ≤ k
/-- Barycentric condition with omitted side `c=0`. -/
def BarycentricC {n} (p : ℕ) (v : Triangle.Vertex n) : Prop :=
  0 < v.a ∧ 0 < v.b ∧ 0 < v.c ∧ (v.a+v.c ≤ p ∨ v.b+v.c ≤ p)
def CX {n} (p : ℕ) (u : Square n) : Prop :=
  0 < u.2.val ∧ u.2.val < u.1.val ∧ u.1.val < n ∧
    (n-(u.1.val-u.2.val) ≤ p ∨ u.1.val ≤ p)
def CY {n} (p : ℕ) (u : Square n) : Prop :=
  0 < u.1.val ∧ u.1.val < u.2.val ∧ u.2.val < n ∧
    (n-(u.2.val-u.1.val) ≤ p ∨ n-u.1.val ≤ p)

theorem CX_x_iff {n} (p : ℕ) (v : Triangle.Vertex n) :
    CX p (x v) ↔ BarycentricC p v := by
  have := v.total
  dsimp [CX, x, BarycentricC]
  omega

theorem CY_y_iff {n} (p : ℕ) (v : Triangle.Vertex n) :
    CY p (y v) ↔ 0 < v.b ∧ 0 < v.c ∧ 0 < v.a ∧
      (v.b+v.a ≤ p ∨ v.c+v.a ≤ p) := by
  have := v.total
  dsimp [CY, y]
  omega

theorem edgeDepth_reverse {n} (p : ℕ) (k : EdgeWeight n) :
    EdgeDepth n p (reverseWeight k).val ↔ EdgeDepth n p k.val := by
  have := k.lt
  dsimp [EdgeDepth, reverseWeight, EdgeWeight.val]
  omega
end FgStrip.TwoTriangle
