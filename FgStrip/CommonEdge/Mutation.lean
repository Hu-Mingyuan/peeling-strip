import FgStrip.CommonEdge.Rows

namespace FgStrip.CommonEdge

/-- A zero coefficient at an unmutated pivot leaves the entire row unchanged. -/
theorem row_mutate_zero {V : Type*} [DecidableEq V] (B : Matrix V V ℤ)
    {u k : V} (hne : u ≠ k) (hz : B u k = 0) (j : V) : mutate B k u j = B u j := by
  by_cases hj : j = k
  · subst j; rw [mutate_col, hz]; rfl
  · rw [mutate_of_ne _ _ _ _ hne hj, hz]
    simp [posPart]

/-- Unconnected rows stay unchanged throughout a word. -/
theorem row_mutateWord_zero {V : Type*} [DecidableEq V] (B : Matrix V V ℤ)
    (W : List V) (u : V) (hne : ∀ k ∈ W, u≠k) (hz : ∀ k ∈ W, B u k = 0) (j : V) :
    mutateWord B W u j = B u j := by
  induction W generalizing B with
  | nil => rfl
  | cons k W ih =>
    rw [mutateWord_cons, ih]
    · exact row_mutate_zero B (hne k (by simp)) (hz k (by simp)) j
    · intro l hl; exact hne l (by simp [hl])
    · intro l hl
      rw [row_mutate_zero B (hne k (by simp)) (hz k (by simp))]
      exact hz l (by simp [hl])

/-- The row update contributed by an independent pivot. -/
def rowCorrection {V : Type*} [DecidableEq V] (B : Matrix V V ℤ) (u k j : V) : ℤ :=
  if j = k then -2*B u j else mutationTerm (B u k) (B k j)

/-- Pairwise disconnected pivots contribute independent row updates. This is
an identity for actual mutation, and not an assumed local deletion certificate. -/
theorem independent_word_row {V : Type*} [DecidableEq V]
    (B : Matrix V V ℤ) (hB : SkewSymmetric B) (W : List V) (hd : W.Nodup)
    (hz : ∀ k ∈ W, ∀ l ∈ W, B k l = 0) (u : V) (hu : u ∉ W) (j : V) :
    mutateWord B W u j = B u j + (W.map (fun k => rowCorrection B u k j)).sum := by
  induction W using List.reverseRecOn with
  | nil => simp
  | @append_singleton W k ih =>
    have hdW : W.Nodup := (List.nodup_append.mp hd).1
    have hk : k ∉ W := by
      intro hk
      exact (List.nodup_append.mp hd).2.2 k hk k (by simp) rfl
    have huW : u ∉ W := by intro h; exact hu (List.mem_append_left _ h)
    have huk : u ≠ k := by intro h; subst u; exact hu (by simp)
    have hzW : ∀ a ∈ W, ∀ b ∈ W, B a b = 0 := by
      intro a ha b hb; exact hz a (by simp [ha]) b (by simp [hb])
    have hkr : ∀ v, mutateWord B W k v = B k v := by
      intro v
      apply row_mutateWord_zero B W k
      · intro l hl h; exact hk (h.symm ▸ hl)
      · intro l hl; exact hz k (by simp) l (by simp [hl])
    have hukentry : mutateWord B W u k = B u k := by
      rw [(hB.mutateWord W) u k, hkr, hB k u, neg_neg]
    rw [mutateWord_append]
    simp only [mutateWord_cons, mutateWord_nil, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    by_cases hj : j = k
    · subst j
      rw [mutate_col, hukentry]
      have hsum : (W.map (fun l => rowCorrection B u l k)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz'
        obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hz'
        have hkl : k≠l := by intro he; exact hk (he.symm ▸ hl)
        have hlk := hz l (by simp [hl]) k (by simp)
        simp [rowCorrection, hkl, hlk, mutationTerm, posPart]
      rw [hsum]
      simp [rowCorrection]
      ring
    · rw [mutate_of_ne _ _ _ _ huk hj, hukentry, hkr, ih hdW hzW huW]
      simp only [rowCorrection, if_neg hj]
      unfold mutationTerm
      ring

/-- Sum of a coordinate indicator over an increasing finite interval. -/
theorem range_indicator_sum (a b q : ℕ) (z : ℤ) :
    ((List.range q).map (fun k => if a+k=b then z else 0)).sum =
      if a ≤ b ∧ b < a+q then z else 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> omega

end FgStrip.CommonEdge
