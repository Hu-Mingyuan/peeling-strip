import Mathlib

/-! The noncorner triangle lattice and its oriented elementary cycles.
Source: `docs/tex/target-theorem.tex`, Section 1, equation (1). -/

namespace FgStrip
namespace Triangle

/-- Nonnegative barycentric coordinates of total weight `n`, excluding corners.
For a nonnegative triple of total weight `n`, being a corner is equivalent to
one coordinate being `n`. -/
def Vertex (n : ℕ) :=
  {p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    p.1.val + p.2.1.val + p.2.2.val = n ∧
    p.1.val < n ∧ p.2.1.val < n ∧ p.2.2.val < n}

deriving instance DecidableEq, Fintype for Vertex

namespace Vertex
variable {n : ℕ}
def a (v : Vertex n) : ℕ := v.1.1.val
def b (v : Vertex n) : ℕ := v.1.2.1.val
def c (v : Vertex n) : ℕ := v.1.2.2.val

theorem total (v : Vertex n) : v.a + v.b + v.c = n := v.2.1
theorem a_lt (v : Vertex n) : v.a < n := v.2.2.1
theorem b_lt (v : Vertex n) : v.b < n := v.2.2.2.1
theorem c_lt (v : Vertex n) : v.c < n := v.2.2.2.2

@[ext] theorem ext {v w : Vertex n}
    (ha : v.a = w.a) (hb : v.b = w.b) (hc : v.c = w.c) : v = w := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext ha) (Prod.ext (Fin.ext hb) (Fin.ext hc))

/-- Construct a noncorner vertex from its three natural weights. -/
def mk (a b c : ℕ) (ht : a + b + c = n) (ha : a < n) (hb : b < n)
    (hc : c < n) : Vertex n :=
  ⟨(⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩), ht, ha, hb, hc⟩

@[simp] theorem mk_a (a b c ht ha hb hc) : (mk (n := n) a b c ht ha hb hc).a = a := rfl
@[simp] theorem mk_b (a b c ht ha hb hc) : (mk (n := n) a b c ht ha hb hc).b = b := rfl
@[simp] theorem mk_c (a b c ht ha hb hc) : (mk (n := n) a b c ht ha hb hc).c = c := rfl
end Vertex

/-- Strictly positive barycentric vertices. -/
def Interior (n : ℕ) := {v : Vertex n // 0 < v.a ∧ 0 < v.b ∧ 0 < v.c}
deriving instance DecidableEq, Fintype for Interior

/-- An elementary cycle is indexed by `a+b+c+2=n`.
This avoids truncated subtraction for the empty ranks `n<2`. -/
def Cell (n : ℕ) :=
  {p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    p.1.val + p.2.1.val + p.2.2.val + 2 = n}
deriving instance DecidableEq, Fintype for Cell

namespace Cell
variable {n : ℕ}
def a (t : Cell n) : ℕ := t.1.1.val
def b (t : Cell n) : ℕ := t.1.2.1.val
def c (t : Cell n) : ℕ := t.1.2.2.val
theorem total (t : Cell n) : t.a + t.b + t.c + 2 = n := t.2

def first (t : Cell n) : Vertex n :=
  Vertex.mk (t.a + 1) (t.b + 1) t.c (by have := t.total; omega)
    (by have := t.total; omega) (by have := t.total; omega) (by have := t.total; omega)
def second (t : Cell n) : Vertex n :=
  Vertex.mk t.a (t.b + 1) (t.c + 1) (by have := t.total; omega)
    (by have := t.total; omega) (by have := t.total; omega) (by have := t.total; omega)
def third (t : Cell n) : Vertex n :=
  Vertex.mk (t.a + 1) t.b (t.c + 1) (by have := t.total; omega)
    (by have := t.total; omega) (by have := t.total; omega) (by have := t.total; omega)
end Cell

/-- Number of arrows from `u` to `v` in `x → y → z → x`.
The vertices may have been identified by a gluing map. -/
def cycleCount {V : Type*} [DecidableEq V] (x y z u v : V) : ℕ :=
  (if u = x ∧ v = y then 1 else 0) +
  (if u = y ∧ v = z then 1 else 0) +
  (if u = z ∧ v = x then 1 else 0)

def cycleEntry {V : Type*} [DecidableEq V] (x y z u v : V) : ℤ :=
  (cycleCount x y z u v : ℤ) - cycleCount x y z v u

theorem cycleEntry_skew {V : Type*} [DecidableEq V] (x y z u v : V) :
    cycleEntry x y z u v = -cycleEntry x y z v u := by
  simp only [cycleEntry]; omega

/-- Directed multiplicity after applying any map to the triangle vertices. -/
def arrowCount {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Vertex n → V) (u v : V) : ℕ :=
  ∑ t : Cell n, cycleCount (f t.first) (f t.second) (f t.third) u v

/-- The signed triangle matrix, including its three sides. -/
def mapMatrix {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Vertex n → V) : Matrix V V ℤ :=
  fun u v => (arrowCount f u v : ℤ) - arrowCount f v u

theorem mapMatrix_eq_sum {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Vertex n → V) (u v : V) :
    mapMatrix f u v =
      ∑ t : Cell n, cycleEntry (f t.first) (f t.second) (f t.third) u v := by
  simp [mapMatrix, arrowCount, cycleEntry, Nat.cast_sum, Finset.sum_sub_distrib]

theorem mapMatrix_skew {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Vertex n → V) (u v : V) : mapMatrix f u v = -mapMatrix f v u := by
  simp only [mapMatrix]; omega

def matrix (n : ℕ) : Matrix (Vertex n) (Vertex n) ℤ := mapMatrix id

/-- A weight on an open edge, with `0 < k < n`. -/
def EdgeWeight (n : ℕ) := {k : Fin n // 0 < k.val}
deriving instance DecidableEq, Fintype for EdgeWeight

namespace EdgeWeight
variable {n : ℕ}
def val (k : EdgeWeight n) : ℕ := k.1.val
theorem pos (k : EdgeWeight n) : 0 < k.val := k.2
theorem lt (k : EdgeWeight n) : k.val < n := k.1.isLt

/-- The three oriented triangle sides, with weights `(n-k,k)` in cyclic order. -/
def ab (k : EdgeWeight n) : Vertex n :=
  Vertex.mk (n - k.val) k.val 0 (by have := k.lt; omega)
    (by have := k.pos; have := k.lt; omega) k.lt (by have := k.lt; omega)
def bc (k : EdgeWeight n) : Vertex n :=
  Vertex.mk 0 (n - k.val) k.val (by have := k.lt; omega)
    (by have := k.lt; omega) (by have := k.pos; have := k.lt; omega) k.lt
def ca (k : EdgeWeight n) : Vertex n :=
  Vertex.mk k.val 0 (n - k.val) (by have := k.lt; omega)
    k.lt (by have := k.lt; omega) (by have := k.pos; have := k.lt; omega)
end EdgeWeight

end Triangle
end FgStrip
