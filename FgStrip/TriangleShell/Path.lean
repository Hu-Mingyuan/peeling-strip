import FgStrip.Deletion

namespace FgStrip.TriangleShell

/-- Coordinate vector on the whole live type. -/
def delta {V : Type*} [DecidableEq V] (v j : V) : ℤ := if j=v then 1 else 0

@[simp] theorem delta_self {V : Type*} [DecidableEq V] (v : V) : delta v v = 1 := by
  simp [delta]

theorem delta_nonneg {V : Type*} [DecidableEq V] (v j : V) : 0 ≤ delta v j := by
  unfold delta; split_ifs <;> omega

/-- The listed prefix of the path. -/
def pathWord {V : Type*} (v : ℕ → V) (t : ℕ) : List V := (List.range t).map v

@[simp] theorem pathWord_zero {V : Type*} (v : ℕ → V) : pathWord v 0 = [] := rfl

theorem pathWord_succ {V : Type*} (v : ℕ → V) (t : ℕ) :
    pathWord v (t+1) = pathWord v t ++ [v t] := by
  simp [pathWord, List.range_succ]

section Path
variable {V : Type*} [DecidableEq V]
variable (B : Matrix V V ℤ) (m : ℕ) (v : ℕ → V) (f : ℕ → V → ℤ)
variable (hinj : ∀ i ≤ m, ∀ j ≤ m, v i = v j → i=j)
variable (hf : ∀ i ≤ m, ∀ j, 0 ≤ f i j)
variable (hz : ∀ i ≤ m, ∀ k ≤ m, f i (v k) = 0)
variable (hd : ∀ j, f 0 j = 0 ∨ f 1 j = 0)
variable (hr : ∀ i ≤ m, ∀ j, B (v i) j =
    f i j - (if i < m then f (i+1) j else 0) +
    (if i < m then delta (v (i+1)) j else 0) -
    (if 0 < i then delta (v (i-1)) j else 0))

include hinj hz hr in
private theorem path_entry (i j : ℕ) (hi : i≤m) (hj : j≤m) :
    B (v i) (v j) = (if j=i+1 then 1 else 0) - (if i=j+1 then 1 else 0) := by
  rw [hr i hi, hz i hi j hj]
  by_cases hlt : i < m
  · rw [ite_eq_left hlt, ite_eq_left hlt, hz (i+1) (by omega) j hj]
    have he : v j = v (i+1) ↔ j=i+1 := ⟨hinj j hj (i+1) (by omega), congrArg v⟩
    simp only [delta, he]
    by_cases hp : 0 < i
    · have he' : v j = v (i-1) ↔ i=j+1 := by
        constructor
        · intro h; have := hinj j hj (i-1) (by omega) h; omega
        · intro h; congr 1; omega
      simp only [ite_eq_left hp, delta, he']
      ring
    · have hne : i≠j+1 := by omega
      simp [hp, hne]
  · have hne : j≠i+1 := by omega
    simp only [ite_eq_right hlt, ite_eq_right hne, sub_zero, add_zero, zero_sub]
    by_cases hp : 0 < i
    · have he' : v j = v (i-1) ↔ i=j+1 := by
        constructor
        · intro h; have := hinj j hj (i-1) (by omega) h; omega
        · intro h; congr 1; omega
      simp only [ite_eq_left hp, delta, he']
    · have hne' : i≠j+1 := by omega
      simp [hp, hne']

include hf hz hd hr in
private theorem path_front_negative (t : ℕ) (ht : t < m) (j : V) :
    posPart (-(B (v t) j + (if 0 < t then 2*delta (v (t-1)) j - f t j else 0))) =
      f (t+1) j := by
  rw [hr t (by omega)]
  simp only [ite_eq_left ht]
  have hnext := hf (t+1) (by omega) j
  by_cases hp : 0 < t
  · simp only [ite_eq_left hp]
    have hprev := delta_nonneg (v (t-1)) j
    have hsucc := delta_nonneg (v (t+1)) j
    by_cases he₁ : j = v (t-1)
    · subst j
      rw [hz (t+1) (by omega) (t-1) (by omega)]
      unfold posPart
      rw [max_eq_right] <;> linarith
    by_cases he₂ : j = v (t+1)
    · subst j
      rw [hz (t+1) (by omega) (t+1) (by omega)]
      unfold posPart
      rw [max_eq_right] <;> linarith
    · simp only [delta, ite_eq_right he₁, ite_eq_right he₂]
      unfold posPart
      have he : -(f t j - f (t+1) j + 0 - 0 + (2*0-f t j)) = f (t+1) j := by ring
      rw [he, max_eq_left hnext]
  · simp only [ite_eq_right hp, sub_zero, add_zero]
    have ht0 : t=0 := by omega
    subst t
    by_cases he : j = v 1
    · subst j
      rw [hz 0 (by omega) 1 (by omega), hz 1 (by omega) 1 (by omega)]
      norm_num [delta, posPart]
    · simp only [delta, ite_eq_right he, add_zero]
      rcases hd j with h | h
      · simp [h, posPart, max_eq_left hnext]
      · have hzero := hf 0 (by omega) j
        simp [h, posPart, max_eq_right (neg_nonpos.mpr hzero)]

include hinj hf hz hd hr in
/-- Each earlier pivot leaves all more distant path rows unchanged. The frontier
row is obtained by cancelling its two off-path coefficients and reversing the
preceding path arrow. This is proved from `mutate`, not a pivot certificate. -/
theorem path_prefix_row (t : ℕ) (ht : t≤m) (k : ℕ) (hkt : t≤k) (hk : k≤m) (j : V) :
    mutateWord B (pathWord v t) (v k) j = B (v k) j +
      (if k=t ∧ 0 < t then 2*delta (v (k-1)) j - f k j else 0) := by
  induction t generalizing k j with
  | zero => simp
  | succ t ih =>
    have htm : t < m := by omega
    have hne : v k ≠ v t := by
      intro h; have := hinj k hk t (by omega) h; omega
    have hrow : ∀ x, mutateWord B (pathWord v t) (v k) x = B (v k) x := by
      intro x
      rw [ih (by omega) k (by omega) hk x]
      have hne' : k≠t := by omega
      simp [hne']
    have hfront : ∀ x, mutateWord B (pathWord v t) (v t) x =
        B (v t) x + (if 0 < t then 2*delta (v (t-1)) x - f t x else 0) := by
      intro x
      simpa using ih (by omega) t (by omega) (by omega) x
    rw [pathWord_succ, mutateWord_append]
    simp only [mutateWord_cons, mutateWord_nil]
    by_cases he : k=t+1
    · have hentry : B (v k) (v t) = -1 := by
        rw [path_entry B m v f hinj hz hr k t hk (by omega)]
        simp only [he]
        split_ifs <;> omega
      by_cases hj : j=v t
      · subst j
        rw [mutate_col, hrow, hentry]
        have hdelt : delta (v (k-1)) (v t) = 1 := by
          have : k-1=t := by omega
          simp [this]
        simp only [he, and_self, Nat.succ_pos, and_true, ite_eq_left rfl]
        rw [hz (t+1) (by omega) t (by omega)]
        have : t+1-1=t := by omega
        simp [this, delta, hentry, he]
      · rw [mutate_of_ne _ _ _ _ hne hj, hrow, hrow, hentry, hfront]
        have hnegative := path_front_negative B m v f hf hz hd hr t htm j
        change _ + posPart (-1) * posPart _ - posPart 1 * posPart _ = _
        rw [hnegative]
        norm_num [posPart]
        have hdelta : delta (v (k-1)) j = 0 := by
          have : k-1=t := by omega
          simp [this, delta, hj]
        have hpos : 0 < t+1 := by omega
        simp [he, hpos, show t+1-1=t by omega, delta, hj, sub_eq_add_neg]
    · have hentry : B (v k) (v t) = 0 := by
        rw [path_entry B m v f hinj hz hr k t hk (by omega)]
        split_ifs <;> omega
      have hcond : ¬(k=t+1 ∧ 0 < t+1) := by omega
      simp only [ite_eq_right hcond, add_zero]
      by_cases hj : j=v t
      · subst j
        rw [mutate_col, hrow, hentry]
        norm_num
      · rw [mutate_of_ne _ _ _ _ hne hj, hrow, hrow, hentry]
        simp [posPart]

include hinj hf hz hd hr in
/-- The endpoint is a source after the entire path word. -/
theorem path_final_row (hm : 0 < m) (j : V) :
    mutateWord B (pathWord v m) (v m) j = delta (v (m-1)) j := by
  rw [path_prefix_row B m v f hinj hf hz hd hr m (by omega) m (by omega) (by omega),
    hr m (by omega)]
  simp only [lt_self_iff_false, ite_false, ite_eq_left hm, true_and, and_self,
    sub_zero, add_zero]
  ring

end Path
end FgStrip.TriangleShell
