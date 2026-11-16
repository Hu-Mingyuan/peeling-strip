import FgStrip.Triangle
import FgStrip.Deletion

namespace FgStrip.TriangleShell
open Triangle

@[ext] theorem cell_ext {n : ℕ} {s t : Cell n}
    (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c) : s = t := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext ha) (Prod.ext (Fin.ext hb) (Fin.ext hc))

private theorem first_injective (n : ℕ) : Function.Injective (Cell.first (n := n)) := by
  intro s t h
  have ha := congrArg Vertex.a h
  have hb := congrArg Vertex.b h
  have hc := congrArg Vertex.c h
  simp only [Cell.first, Vertex.mk_a, Vertex.mk_b, Vertex.mk_c] at *
  apply cell_ext <;> omega

private theorem second_injective (n : ℕ) : Function.Injective (Cell.second (n := n)) := by
  intro s t h
  have ha := congrArg Vertex.a h
  have hb := congrArg Vertex.b h
  have hc := congrArg Vertex.c h
  simp only [Cell.second, Vertex.mk_a, Vertex.mk_b, Vertex.mk_c] at *
  apply cell_ext <;> omega

private theorem third_injective (n : ℕ) : Function.Injective (Cell.third (n := n)) := by
  intro s t h
  have ha := congrArg Vertex.a h
  have hb := congrArg Vertex.b h
  have hc := congrArg Vertex.c h
  simp only [Cell.third, Vertex.mk_a, Vertex.mk_b, Vertex.mk_c] at *
  apply cell_ext <;> omega

private theorem sum_pair {T V : Type*} [Fintype T] [DecidableEq V]
    (f g : T → V) (hf : Function.Injective f) (u v : V) :
    (∑ t, if u = f t ∧ v = g t then (1 : ℕ) else 0) =
      if ∃ t, u = f t ∧ v = g t then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨t, ht⟩ := h
    rw [Finset.sum_eq_single t]
    · simp [ht]
    · intro s _ hst
      have hn : u ≠ f s := fun hs => hst (hf (hs.symm.trans ht.1))
      simp [hn]
    · simp
  · apply Finset.sum_eq_zero
    intro t _
    have hn : ¬(u = f t ∧ v = g t) := fun ht => h ⟨t, ht⟩
    simp [hn]

private def mkCell {n : ℕ} (a b c : ℕ) (ht : a+b+c+2=n) : Cell n :=
  ⟨(⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩), ht⟩

private theorem first_second {n : ℕ} (u v : Vertex n) :
    (∃ t : Cell n, u = t.first ∧ v = t.second) ↔
      v.a + 1 = u.a ∧ v.b = u.b ∧ v.c = u.c + 1 ∧ 0 < u.b := by
  constructor
  · rintro ⟨t, rfl, rfl⟩
    simp [Cell.first, Cell.second]
  · rintro ⟨ha,hb,hc,hpos⟩
    have ht := u.total
    refine ⟨mkCell (u.a-1) (u.b-1) u.c (by omega), ?_, ?_⟩ <;>
      apply Vertex.ext <;>
      simp only [Cell.first, Cell.second, Vertex.mk_a, Vertex.mk_b, Vertex.mk_c,
        Cell.a, Cell.b, Cell.c, mkCell] <;> omega

private theorem second_third {n : ℕ} (u v : Vertex n) :
    (∃ t : Cell n, u = t.second ∧ v = t.third) ↔
      v.a = u.a + 1 ∧ v.b + 1 = u.b ∧ v.c = u.c ∧ 0 < u.c := by
  constructor
  · rintro ⟨t, rfl, rfl⟩
    simp [Cell.second, Cell.third]
  · rintro ⟨ha,hb,hc,hpos⟩
    have ht := u.total
    refine ⟨mkCell u.a (u.b-1) (u.c-1) (by omega), ?_, ?_⟩ <;>
      apply Vertex.ext <;>
      simp only [Cell.second, Cell.third, Vertex.mk_a, Vertex.mk_b, Vertex.mk_c,
        Cell.a, Cell.b, Cell.c, mkCell] <;> omega

private theorem third_first {n : ℕ} (u v : Vertex n) :
    (∃ t : Cell n, u = t.third ∧ v = t.first) ↔
      v.a = u.a ∧ v.b = u.b + 1 ∧ v.c + 1 = u.c ∧ 0 < u.a := by
  constructor
  · rintro ⟨t, rfl, rfl⟩
    simp [Cell.third, Cell.first]
  · rintro ⟨ha,hb,hc,hpos⟩
    have ht := u.total
    refine ⟨mkCell (u.a-1) u.b (u.c-1) (by omega), ?_, ?_⟩ <;>
      apply Vertex.ext <;>
      simp only [Cell.third, Cell.first, Vertex.mk_a, Vertex.mk_b, Vertex.mk_c,
        Cell.a, Cell.b, Cell.c, mkCell] <;> omega

/-- The directed count derived from the elementary cycle sum, including sides. -/
theorem arrowCount_eq {n : ℕ} (u v : Vertex n) :
    arrowCount id u v =
      (if v.a+1=u.a ∧ v.b=u.b ∧ v.c=u.c+1 ∧ 0<u.b then 1 else 0) +
      (if v.a=u.a+1 ∧ v.b+1=u.b ∧ v.c=u.c ∧ 0<u.c then 1 else 0) +
      (if v.a=u.a ∧ v.b=u.b+1 ∧ v.c+1=u.c ∧ 0<u.a then 1 else 0) := by
  classical
  simp only [arrowCount, cycleCount, id_eq, Finset.sum_add_distrib]
  rw [sum_pair _ _ (first_injective n), sum_pair _ _ (second_injective n),
    sum_pair _ _ (third_injective n)]
  simp only [first_second, second_third, third_first]

/-- Complete matrix entries. Every coefficient outside the six listed directions is zero. -/
theorem matrix_eq {n : ℕ} (u v : Vertex n) :
    matrix n u v =
      ((if v.a+1=u.a ∧ v.b=u.b ∧ v.c=u.c+1 ∧ 0<u.b then 1 else 0) +
       (if v.a=u.a+1 ∧ v.b+1=u.b ∧ v.c=u.c ∧ 0<u.c then 1 else 0) +
       (if v.a=u.a ∧ v.b=u.b+1 ∧ v.c+1=u.c ∧ 0<u.a then 1 else 0) : ℤ) -
      ((if u.a+1=v.a ∧ u.b=v.b ∧ u.c=v.c+1 ∧ 0<v.b then 1 else 0) +
       (if u.a=v.a+1 ∧ u.b+1=v.b ∧ u.c=v.c ∧ 0<v.c then 1 else 0) +
       (if u.a=v.a ∧ u.b=v.b+1 ∧ u.c+1=v.c ∧ 0<v.a then 1 else 0)) := by
  simp only [matrix, mapMatrix, arrowCount_eq, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Reflection exchanges the first two barycentric weights. -/
def exchange {n : ℕ} (v : Vertex n) : Vertex n :=
  Vertex.mk v.b v.a v.c (by have := v.total; omega) v.b_lt v.a_lt v.c_lt

@[simp] theorem exchange_a {n} (v : Vertex n) : (exchange v).a = v.b := rfl
@[simp] theorem exchange_b {n} (v : Vertex n) : (exchange v).b = v.a := rfl
@[simp] theorem exchange_c {n} (v : Vertex n) : (exchange v).c = v.c := rfl
@[simp] theorem exchange_exchange {n} (v : Vertex n) : exchange (exchange v) = v := by
  apply Vertex.ext <;> rfl

/-- Reflection reverses the concrete cycle matrix, including the interface entries. -/
theorem matrix_exchange {n : ℕ} (u v : Vertex n) :
    matrix n (exchange u) (exchange v) = -matrix n u v := by
  rw [matrix_eq, matrix_eq]
  simp only [exchange_a, exchange_b, exchange_c]
  have h₁ : (v.b+1=u.b ∧ v.a=u.a ∧ v.c=u.c+1 ∧ 0<u.a) ↔
      (u.a=v.a ∧ u.b=v.b+1 ∧ u.c+1=v.c ∧ 0<v.a) := by omega
  have h₂ : (v.b=u.b+1 ∧ v.a+1=u.a ∧ v.c=u.c ∧ 0<u.c) ↔
      (u.a=v.a+1 ∧ u.b+1=v.b ∧ u.c=v.c ∧ 0<v.c) := by omega
  have h₃ : (v.b=u.b ∧ v.a=u.a+1 ∧ v.c+1=u.c ∧ 0<u.b) ↔
      (u.a+1=v.a ∧ u.b=v.b ∧ u.c=v.c+1 ∧ 0<v.b) := by omega
  have h₄ : (u.b+1=v.b ∧ u.a=v.a ∧ u.c=v.c+1 ∧ 0<v.a) ↔
      (v.a=u.a ∧ v.b=u.b+1 ∧ v.c+1=u.c ∧ 0<u.a) := by omega
  have h₅ : (u.b=v.b+1 ∧ u.a+1=v.a ∧ u.c=v.c ∧ 0<v.c) ↔
      (v.a=u.a+1 ∧ v.b+1=u.b ∧ v.c=u.c ∧ 0<u.c) := by omega
  have h₆ : (u.b=v.b ∧ u.a=v.a+1 ∧ u.c+1=v.c ∧ 0<v.b) ↔
      (v.a+1=u.a ∧ v.b=u.b ∧ v.c=u.c+1 ∧ 0<u.b) := by omega
  simp only [h₁,h₂,h₃,h₄,h₅,h₆]
  ring

end FgStrip.TriangleShell
