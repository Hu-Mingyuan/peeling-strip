import FgStrip.AmbientTriangulation.Construction

namespace FgStrip.AmbientTriangulation
open Triangle

/-- Ordinary zero extension along an embedding. -/
noncomputable def zeroExtension {S V : Type*} (i : S ↪ V) (B : Matrix S S ℤ) :
    Matrix V V ℤ := by
  classical
  exact fun u v => if hu : ∃ x, i x = u then
    if hv : ∃ y, i y = v then B hu.choose hv.choose else 0 else 0

@[simp] theorem zeroExtension_apply {S V : Type*} (i : S ↪ V) (B : Matrix S S ℤ)
    (x y : S) : zeroExtension i B (i x) (i y) = B x y := by
  classical
  have hx : ∃ a, i a = i x := ⟨x,rfl⟩
  have hy : ∃ a, i a = i y := ⟨y,rfl⟩
  simp only [zeroExtension, dite_eq_left hx, dite_eq_left hy]
  rw [i.injective hx.choose_spec, i.injective hy.choose_spec]

theorem zeroExtension_row_zero {S V : Type*} (i : S ↪ V) (B : Matrix S S ℤ)
    (u v : V) (hu : u ∉ Set.range i) : zeroExtension i B u v = 0 := by
  classical
  unfold zeroExtension
  split
  · next h => exact (hu h).elim
  · rfl

theorem zeroExtension_col_zero {S V : Type*} (i : S ↪ V) (B : Matrix S S ℤ)
    (u v : V) (hv : v ∉ Set.range i) : zeroExtension i B u v = 0 := by
  classical
  unfold zeroExtension
  split
  · split
    · next h => exact (hv h).elim
    · rfl
  · rfl

/-- An elementary cycle contributes nothing at a point outside its three vertices. -/
theorem cycleEntry_row_zero {V : Type*} [DecidableEq V] (a b c u v : V)
    (ha : u ≠ a) (hb : u ≠ b) (hc : u ≠ c) :
    cycleEntry a b c u v = 0 := by
  simp [cycleEntry, cycleCount, ha, hb, hc]

namespace Data
variable {n N : ℕ} {X O : Type*} (d : Data N X O)

/-- All triangle cycles, glued and then restricted to the retained points. -/
noncomputable def matrix [Fintype O] (n : ℕ) : Matrix (d.Vertex n) (d.Vertex n) ℤ := by
  classical
  exact fun u v => ∑ f : Strip.Face N ⊕ O, ∑ t : Cell n,
    cycleEntry (d.localWeight f t.first) (d.localWeight f t.second)
      (d.localWeight f t.third) u.1.1 v.1.1

/-- The summands from the actual ordered strip faces. -/
noncomputable def stripContribution (n : ℕ) : Matrix (d.Vertex n) (d.Vertex n) ℤ := by
  classical
  exact fun u v => ∑ f : Strip.Face N, ∑ t : Cell n,
    cycleEntry (d.localWeight (Sum.inl f) t.first)
      (d.localWeight (Sum.inl f) t.second) (d.localWeight (Sum.inl f) t.third) u.1.1 v.1.1

/-- The exterior contribution is computed independently from its triangle cycles. -/
noncomputable def exterior [Fintype O] (n : ℕ) : Matrix (d.Vertex n) (d.Vertex n) ℤ := by
  classical
  exact fun u v => ∑ o : O, ∑ t : Cell n,
    cycleEntry (d.localWeight (Sum.inr o) t.first)
      (d.localWeight (Sum.inr o) t.second) (d.localWeight (Sum.inr o) t.third) u.1.1 v.1.1

theorem matrix_split [Fintype O] :
    d.matrix n = d.stripContribution n + d.exterior n := by
  classical
  funext u v
  exact Fintype.sum_sum_type _

theorem stripContribution_skew : SkewSymmetric (d.stripContribution n) := by
  classical
  intro u v
  simp only [stripContribution, cycleEntry_skew (u := u.1.1) (v := v.1.1), Finset.sum_neg_distrib]

theorem exterior_skew [Fintype O] : SkewSymmetric (d.exterior n) := by
  classical
  intro u v
  simp only [exterior, cycleEntry_skew (u := u.1.1) (v := v.1.1), Finset.sum_neg_distrib]

theorem matrix_skew [Fintype O] : SkewSymmetric (d.matrix n) := by
  classical
  intro u v
  simp only [matrix, cycleEntry_skew (u := u.1.1) (v := v.1.1), Finset.sum_neg_distrib]

/-- Equality of the retained strip contribution follows from its glued weights;
no ambient matrix equality is assumed. -/
theorem stripContribution_embedding (hb : d.BoundaryCompatible n) (x y : Strip.Vertex n N) :
    d.stripContribution n (d.embedding hb x) (d.embedding hb y) = Strip.matrix n N x y := by
  classical
  rw [Strip.matrix_concrete_entries]
  simp only [stripContribution, localWeight_strip, embedding_weight, cycleEntry, cycleCount,
    extendWeight_injective.eq_iff]

theorem stripContribution_row_zero (hb : d.BoundaryCompatible n) (u v : d.Vertex n)
    (hu : u ∉ Set.range (d.embedding hb)) : d.stripContribution n u v = 0 := by
  classical
  have hp : ∀ f : Strip.Face N, ∀ p : Triangle.Vertex n,
      u.1.1 ≠ d.localWeight (Sum.inl f) p := by
    intro f p h
    exact hu (d.mem_range_of_strip_weight hb u f p ((d.localWeight_strip f p) ▸ h))
  apply Finset.sum_eq_zero
  intro f _
  apply Finset.sum_eq_zero
  intro t _
  exact cycleEntry_row_zero _ _ _ _ _ (hp f t.first) (hp f t.second) (hp f t.third)

theorem stripContribution_eq_zeroExtension (hb : d.BoundaryCompatible n) :
    d.stripContribution n = zeroExtension (d.embedding hb) (Strip.matrix n N) := by
  classical
  funext u v
  by_cases hu : u ∈ Set.range (d.embedding hb)
  · obtain ⟨x,rfl⟩ := hu
    by_cases hv : v ∈ Set.range (d.embedding hb)
    · obtain ⟨y,rfl⟩ := hv
      rw [zeroExtension_apply, d.stripContribution_embedding hb]
    · rw [zeroExtension_col_zero _ _ _ _ hv, d.stripContribution_skew,
        d.stripContribution_row_zero hb _ _ hv, neg_zero]
  · rw [zeroExtension_row_zero _ _ _ _ hu, d.stripContribution_row_zero hb _ _ hu]

/-- Every exterior elementary cycle vanishes at an internal strip point, against
all ambient columns, whether or not those columns lie in the strip. -/
theorem exterior_row_zero [Fintype O] (hb : d.BoundaryCompatible n)
    (hi : d.FaceIncidence n) (hN : 0 < N) (x : Strip.Vertex n N)
    (hx : x ∈ Strip.internal hN) (v : d.Vertex n) :
    d.exterior n (d.embedding hb x) v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro o _
  apply Finset.sum_eq_zero
  intro t _
  exact cycleEntry_row_zero _ _ _ _ _
    (d.outside_ne_internal hb hi hN x hx o t.first)
    (d.outside_ne_internal hb hi hN x hx o t.second)
    (d.outside_ne_internal hb hi hN x hx o t.third)

/-- The ambient hypothesis of target-theorem Section 2, derived from finite
triangle incidence. This does not assert existence of deletion moves. -/
theorem ambient_hypothesis [Fintype O] (hb : d.BoundaryCompatible n)
    (hi : d.FaceIncidence n) (hN : 0 < N) :
    d.matrix n = zeroExtension (d.embedding hb) (Strip.matrix n N) + d.exterior n ∧
    SkewSymmetric (d.exterior n) ∧
    ∀ x ∈ Strip.internal hN, ∀ v : d.Vertex n, d.exterior n (d.embedding hb x) v = 0 := by
  refine ⟨?_, d.exterior_skew, d.exterior_row_zero hb hi hN⟩
  rw [d.matrix_split, d.stripContribution_eq_zeroExtension hb]

end Data
end FgStrip.AmbientTriangulation
