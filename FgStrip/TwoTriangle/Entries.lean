import FgStrip.TwoTriangle.Cycles

namespace FgStrip.TwoTriangle
open Triangle

@[ext] theorem cell_ext {n} {s t : Cell n} (ha : s.a=t.a) (hb : s.b=t.b)
    (hc : s.c=t.c) : s=t := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext ha) (Prod.ext (Fin.ext hb) (Fin.ext hc))
theorem first_injective {n} : Function.Injective (@Cell.first n) := by
  intro s t h
  have ha := congrArg Triangle.Vertex.a h
  have hb := congrArg Triangle.Vertex.b h
  have hc := congrArg Triangle.Vertex.c h
  simp only [Cell.first, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c] at *
  apply cell_ext <;> omega
theorem second_injective {n} : Function.Injective (@Cell.second n) := by
  intro s t h
  have ha := congrArg Triangle.Vertex.a h
  have hb := congrArg Triangle.Vertex.b h
  have hc := congrArg Triangle.Vertex.c h
  simp only [Cell.second, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c] at *
  apply cell_ext <;> omega
theorem third_injective {n} : Function.Injective (@Cell.third n) := by
  intro s t h
  have ha := congrArg Triangle.Vertex.a h
  have hb := congrArg Triangle.Vertex.b h
  have hc := congrArg Triangle.Vertex.c h
  simp only [Cell.third, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c] at *
  apply cell_ext <;> omega

def cellOfBC {n} (b c : ℕ) (h : b+c+2 ≤ n) : Cell n :=
  ⟨(⟨n-(b+c+2), by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩), by dsimp; omega⟩

theorem indicator_sum {T V} [Fintype T] [DecidableEq T] [DecidableEq V]
    (f g : T → V) (hf : Function.Injective f) (u v : V) :
    (∑ t, if u=f t ∧ v=g t then (1:ℕ) else 0) =
      if ∃ t, u=f t ∧ v=g t then 1 else 0 := by
  by_cases he : ∃ t, u=f t ∧ v=g t
  · rcases he with ⟨t, hu, hv⟩
    rw [ite_eq_left ⟨t,hu,hv⟩]
    rw [Finset.sum_eq_single t]
    · simp [hu,hv]
    · intro s _ hst
      have hn : u ≠ f s := by intro hh; exact hst (hf (hh.symm.trans hu))
      simp [hn]
    · simp
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro t _
    simp only [not_exists] at he
    simp [he t]

theorem x_first_second_iff {n} (u v : Grid n) :
    (∃ t : Cell n, u.1=x t.first ∧ v.1=x t.second) ↔
      u.j < u.i ∧ u.i < n ∧ v.i=u.i+1 ∧ v.j=u.j+1 := by
  have ui := u.i_le; have uj := u.j_pos; have un := u.j_lt
  constructor
  · rintro ⟨t, hu, hv⟩
    have ht := t.total
    have hu1 := congrArg (fun z : Square n => z.1.val) hu
    have hu2 := congrArg (fun z : Square n => z.2.val) hu
    have hv1 := congrArg (fun z : Square n => z.1.val) hv
    have hv2 := congrArg (fun z : Square n => z.2.val) hv
    change u.i=t.b+1+t.c at hu1
    change u.j=t.c at hu2
    change v.i=t.b+1+(t.c+1) at hv1
    change v.j=t.c+1 at hv2
    omega
  · rintro ⟨hji,hin,hvi,hvj⟩
    refine ⟨cellOfBC (u.i-u.j-1) u.j (by omega), ?_, ?_⟩
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        simp only [x, Cell.first, Cell.second, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
          cellOfBC, Cell.b, Cell.c]
        dsimp [Grid.i, Grid.j] at *
        all_goals omega

theorem x_second_third_iff {n} (u v : Grid n) :
    (∃ t : Cell n, u.1=x t.second ∧ v.1=x t.third) ↔
      u.j < u.i ∧ v.i+1=u.i ∧ v.j=u.j := by
  have ui := u.i_le; have uj := u.j_pos; have un := u.j_lt
  constructor
  · rintro ⟨t, hu, hv⟩
    have hu1 := congrArg (fun z : Square n => z.1.val) hu
    have hu2 := congrArg (fun z : Square n => z.2.val) hu
    have hv1 := congrArg (fun z : Square n => z.1.val) hv
    have hv2 := congrArg (fun z : Square n => z.2.val) hv
    change u.i=t.b+1+(t.c+1) at hu1
    change u.j=t.c+1 at hu2
    change v.i=t.b+(t.c+1) at hv1
    change v.j=t.c+1 at hv2
    omega
  · rintro ⟨hji,hvi,hvj⟩
    refine ⟨cellOfBC (u.i-u.j-1) (u.j-1) (by omega), ?_, ?_⟩
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        simp only [x, Cell.second, Cell.third, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
          cellOfBC, Cell.b, Cell.c]
        dsimp [Grid.i, Grid.j] at *
        all_goals omega

theorem x_third_first_iff {n} (u v : Grid n) :
    (∃ t : Cell n, u.1=x t.third ∧ v.1=x t.first) ↔
      u.j ≤ u.i ∧ u.i < n ∧ v.i=u.i ∧ v.j+1=u.j := by
  have ui := u.i_le; have uj := u.j_pos; have un := u.j_lt
  constructor
  · rintro ⟨t, hu, hv⟩
    have ht := t.total
    have hu1 := congrArg (fun z : Square n => z.1.val) hu
    have hu2 := congrArg (fun z : Square n => z.2.val) hu
    have hv1 := congrArg (fun z : Square n => z.1.val) hv
    have hv2 := congrArg (fun z : Square n => z.2.val) hv
    change u.i=t.b+(t.c+1) at hu1
    change u.j=t.c+1 at hu2
    change v.i=t.b+1+t.c at hv1
    change v.j=t.c at hv2
    omega
  · rintro ⟨hji,hin,hvi,hvj⟩
    refine ⟨cellOfBC (u.i-u.j) (u.j-1) (by omega), ?_, ?_⟩
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        simp only [x, Cell.first, Cell.third, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
          cellOfBC, Cell.b, Cell.c]
        dsimp [Grid.i, Grid.j] at *
        all_goals omega

theorem y_first_second_iff {n} (u v : Grid n) :
    (∃ t : Cell n, u.1=y t.first ∧ v.1=y t.second) ↔
      0 < u.i ∧ u.i ≤ u.j ∧ v.i=u.i ∧ v.j=u.j+1 := by
  have ui := u.i_le; have uj := u.j_pos; have un := u.j_lt
  constructor
  · rintro ⟨t, hu, hv⟩
    have ht := t.total
    have hu1 := congrArg (fun z : Square n => z.1.val) hu
    have hu2 := congrArg (fun z : Square n => z.2.val) hu
    have hv1 := congrArg (fun z : Square n => z.1.val) hv
    have hv2 := congrArg (fun z : Square n => z.2.val) hv
    change u.i=t.b+1 at hu1
    change u.j=t.b+1+t.c at hu2
    change v.i=t.b+1 at hv1
    change v.j=t.b+1+(t.c+1) at hv2
    omega
  · rintro ⟨hi,hij,hvi,hvj⟩
    refine ⟨cellOfBC (u.i-1) (u.j-u.i) (by omega), ?_, ?_⟩
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        simp only [y, Cell.first, Cell.second, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
          cellOfBC, Cell.b, Cell.c]
        dsimp [Grid.i, Grid.j] at *
        all_goals omega

theorem y_second_third_iff {n} (u v : Grid n) :
    (∃ t : Cell n, u.1=y t.second ∧ v.1=y t.third) ↔
      0 < u.i ∧ u.i < u.j ∧ v.i+1=u.i ∧ v.j+1=u.j := by
  have ui := u.i_le; have uj := u.j_pos; have un := u.j_lt
  constructor
  · rintro ⟨t, hu, hv⟩
    have ht := t.total
    have hu1 := congrArg (fun z : Square n => z.1.val) hu
    have hu2 := congrArg (fun z : Square n => z.2.val) hu
    have hv1 := congrArg (fun z : Square n => z.1.val) hv
    have hv2 := congrArg (fun z : Square n => z.2.val) hv
    change u.i=t.b+1 at hu1
    change u.j=t.b+1+(t.c+1) at hu2
    change v.i=t.b at hv1
    change v.j=t.b+(t.c+1) at hv2
    omega
  · rintro ⟨hi,hij,hvi,hvj⟩
    refine ⟨cellOfBC (u.i-1) (u.j-u.i-1) (by omega), ?_, ?_⟩
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        simp only [y, Cell.second, Cell.third, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
          cellOfBC, Cell.b, Cell.c]
        dsimp [Grid.i, Grid.j] at *
        all_goals omega

theorem y_third_first_iff {n} (u v : Grid n) :
    (∃ t : Cell n, u.1=y t.third ∧ v.1=y t.first) ↔
      u.i < u.j ∧ v.i=u.i+1 ∧ v.j=u.j := by
  have ui := u.i_le; have uj := u.j_pos; have un := u.j_lt
  constructor
  · rintro ⟨t, hu, hv⟩
    have ht := t.total
    have hu1 := congrArg (fun z : Square n => z.1.val) hu
    have hu2 := congrArg (fun z : Square n => z.2.val) hu
    have hv1 := congrArg (fun z : Square n => z.1.val) hv
    have hv2 := congrArg (fun z : Square n => z.2.val) hv
    change u.i=t.b at hu1
    change u.j=t.b+(t.c+1) at hu2
    change v.i=t.b+1 at hv1
    change v.j=t.b+1+t.c at hv2
    omega
  · rintro ⟨hij,hvi,hvj⟩
    refine ⟨cellOfBC (u.i) (u.j-u.i-1) (by omega), ?_, ?_⟩
    all_goals
      apply Prod.ext <;> apply Fin.ext
      all_goals
        simp only [y, Cell.third, Cell.first, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
          cellOfBC, Cell.b, Cell.c]
        dsimp [Grid.i, Grid.j] at *
        all_goals omega

/-- Complete directed multiplicity on the retained grid, with interface terms. -/
def arrows {n} (u v : Grid n) : ℕ :=
  (if u.j < u.i ∧ u.i < n ∧ v.i=u.i+1 ∧ v.j=u.j+1 then 1 else 0) +
  (if u.j < u.i ∧ v.i+1=u.i ∧ v.j=u.j then 1 else 0) +
  (if u.j ≤ u.i ∧ u.i < n ∧ v.i=u.i ∧ v.j+1=u.j then 1 else 0) +
  (if 0 < u.i ∧ u.i ≤ u.j ∧ v.i=u.i ∧ v.j=u.j+1 then 1 else 0) +
  (if 0 < u.i ∧ u.i < u.j ∧ v.i+1=u.i ∧ v.j+1=u.j then 1 else 0) +
  (if u.i < u.j ∧ v.i=u.i+1 ∧ v.j=u.j then 1 else 0)

theorem arrowCount_formula {n} (u v : Grid n) :
    arrowCount x u.1 v.1 + arrowCount y u.1 v.1 = arrows u v := by
  simp only [arrowCount, cycleCount, Finset.sum_add_distrib]
  have h1 := indicator_sum (x ∘ Cell.first) (x ∘ Cell.second) (x_injective.comp first_injective) u.1 v.1
  have h2 := indicator_sum (x ∘ Cell.second) (x ∘ Cell.third) (x_injective.comp second_injective) u.1 v.1
  have h3 := indicator_sum (x ∘ Cell.third) (x ∘ Cell.first) (x_injective.comp third_injective) u.1 v.1
  have h4 := indicator_sum (y ∘ Cell.first) (y ∘ Cell.second) (y_injective.comp first_injective) u.1 v.1
  have h5 := indicator_sum (y ∘ Cell.second) (y ∘ Cell.third) (y_injective.comp second_injective) u.1 v.1
  have h6 := indicator_sum (y ∘ Cell.third) (y ∘ Cell.first) (y_injective.comp third_injective) u.1 v.1
  simp only [Function.comp_apply] at h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h4,h5,h6]
  simp only [x_first_second_iff, x_second_third_iff, x_third_first_iff,
    y_first_second_iff, y_second_third_iff, y_third_first_iff, arrows]
  omega

theorem matrix_formula {n} (u v : Grid n) :
    matrix n u v = (arrows u v : ℤ) - arrows v u := by
  rw [← arrowCount_formula, ← arrowCount_formula]
  simp only [matrix, squareMatrix, mapMatrix, Nat.cast_add]
  ring

/-- Every coefficient outside the six nearest-neighbour directions is zero. -/
def Neighbours {n} (u v : Grid n) : Prop :=
  (v.i=u.i+1 ∧ v.j=u.j+1) ∨ (v.i+1=u.i ∧ v.j+1=u.j) ∨
  (v.i=u.i+1 ∧ v.j=u.j) ∨ (v.i+1=u.i ∧ v.j=u.j) ∨
  (v.i=u.i ∧ v.j=u.j+1) ∨ (v.i=u.i ∧ v.j+1=u.j)

theorem neighbours_symm {n} (u v : Grid n) : Neighbours u v ↔ Neighbours v u := by
  unfold Neighbours
  omega

theorem arrows_zero_of_not_neighbours {n} (u v : Grid n) (h : ¬Neighbours u v) :
    arrows u v = 0 := by
  dsimp [Neighbours] at h
  have h1 : ¬(u.j < u.i ∧ u.i < n ∧ v.i=u.i+1 ∧ v.j=u.j+1) := by omega
  have h2 : ¬(u.j < u.i ∧ v.i+1=u.i ∧ v.j=u.j) := by omega
  have h3 : ¬(u.j ≤ u.i ∧ u.i < n ∧ v.i=u.i ∧ v.j+1=u.j) := by omega
  have h4 : ¬(0 < u.i ∧ u.i ≤ u.j ∧ v.i=u.i ∧ v.j=u.j+1) := by omega
  have h5 : ¬(0 < u.i ∧ u.i < u.j ∧ v.i+1=u.i ∧ v.j+1=u.j) := by omega
  have h6 : ¬(u.i < u.j ∧ v.i=u.i+1 ∧ v.j=u.j) := by omega
  simp only [arrows, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_right h6]

theorem matrix_zero_of_not_neighbours {n} (u v : Grid n) (h : ¬Neighbours u v) :
    matrix n u v = 0 := by
  rw [matrix_formula, arrows_zero_of_not_neighbours u v h,
    arrows_zero_of_not_neighbours v u (fun hh => h ((neighbours_symm u v).mpr hh))]
  rfl
end FgStrip.TwoTriangle
