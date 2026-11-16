import FgStrip.CommonEdge.Mutation

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

set_option maxHeartbeats 300000

/-- The first column's incoming neighbour, including the omitted-pivot case. -/
def anchor {n} (r t : ℕ) (skipFirst : Bool) (v : Grid n) : ℤ :=
  if skipFirst then (if r = t then 0 else e (r-1) r v) else e (r-1) (r-1) v

/-- Negative part of the complete pre-mutation expression. -/
def pivotNeg {n} (r t : ℕ) (skipFirst : Bool) (i j : ℕ) (v : Grid n) : ℤ :=
  (if i = r then anchor r t skipFirst v else
    if j = i-1 then e (i-1) (i-1) v else e (i-1) j v) +
  e (i+1) j v + (if i = t then e t t v else 0)

/-- Positive part, with the extra last-column neighbours before its top mutation. -/
def pivotPos {n} (r t : ℕ) (skipFirst : Bool) (i j : ℕ) (v : Grid n) : ℤ :=
  e i (j-1) v +
  (if j = i-1 then
    if i = t then e (t+1) t v + (if skipFirst = true ∧ r = t then 0 else e (t-1) t v)
    else e i i v
  else e i (j+1) v)

def pivotRow {n} (r t : ℕ) (skipFirst : Bool) (i j : ℕ) (v : Grid n) : ℤ :=
  pivotPos r t skipFirst i j v - pivotNeg r t skipFirst i j v

/-- Original lower-triangle expression. -/
def originalLower {n} (i j : ℕ) (v : Grid n) : ℤ :=
  e (i+1) (j+1) v - e (i+1) j v - e i (j+1) v +
  e i (j-1) v + e (i-1) j v - e (i-1) (j-1) v

/-- The next column after its left neighbours have been mutated. -/
def columnLower {n} (r i j : ℕ) (v : Grid n) : ℤ :=
  e (i+1) (j+1) v - e (i+1) j v - e i (j+1) v + e i (j-1) v +
  (if i = r then 0 else -e (i-1) j v + e (i-1) (j+1) v)

/-- All future rows after columns below `i` and heights above `j` in column `i`.
Only rows not yet mutated occur in the invariant. -/
def sweepRow {n} (r t : ℕ) (skipFirst : Bool) (i j h l : ℕ) (v : Grid n) : ℤ :=
  if l = h-1 then pivotRow r t skipFirst h l v
  else if h = i ∧ l = j then pivotRow r t skipFirst h l v
  else if h = i ∨ (h = i+1 ∧ j < l) then columnLower r h l v
  else originalLower h l v

/-- The deletion vertex throughout the sweep. -/
def targetRow {n} (r t : ℕ) (skipFirst : Bool) (i j : ℕ) (v : Grid n) : ℤ :=
  if i = t ∧ j < t-1 then
    -e t (j+1) v + e t j v - (if skipFirst = true ∧ r = t then e (t-1) t v else 0)
  else e t (t-1) v - e (t+1) t v - e (t-1) t v

theorem e_mul {n a b c d} (v : Grid n) :
    e a b v * e c d v = if a=c ∧ b=d then e a b v else 0 := by
  unfold e
  split_ifs <;> omega

/-- The positive and negative supports in each pivot expression are disjoint. -/
theorem pivot_parts {n r t i j} (hr : 2 ≤ r) (hi : r ≤ i) (hit : i ≤ t)
    (hj : 0 < j) (hji : j < i) (skipFirst : Bool) (v : Grid n) :
    posPart (pivotRow r t skipFirst i j v)=pivotPos r t skipFirst i j v ∧
    posPart (-pivotRow r t skipFirst i j v)=pivotNeg r t skipFirst i j v := by
  have hp : 0 ≤ pivotPos r t skipFirst i j v := by
    have := e_nonneg (i := i) (j := j-1) v
    have := e_nonneg (i := t+1) (j := t) v
    have := e_nonneg (i := t-1) (j := t) v
    have := e_nonneg (i := i) (j := i) v
    have := e_nonneg (i := i) (j := j+1) v
    unfold pivotPos
    split_ifs <;> omega
  have hn : 0 ≤ pivotNeg r t skipFirst i j v := by
    have := e_nonneg (i := r-1) (j := r) v
    have := e_nonneg (i := r-1) (j := r-1) v
    have := e_nonneg (i := i-1) (j := i-1) v
    have := e_nonneg (i := i-1) (j := j) v
    have := e_nonneg (i := i+1) (j := j) v
    have := e_nonneg (i := t) (j := t) v
    unfold pivotNeg anchor
    split_ifs <;> omega
  have hz : pivotPos r t skipFirst i j v * pivotNeg r t skipFirst i j v=0 := by
    unfold pivotPos pivotNeg anchor
    split_ifs <;>
      simp only [add_mul, mul_add, zero_mul, mul_zero, e_mul] <;>
      simp (disch := omega) only [ite_eq_right, zero_add, add_zero]
  unfold pivotRow posPart
  rcases mul_eq_zero.mp hz with h | h
  · rw [h]
    simp [max_eq_left hn, max_eq_right (neg_nonpos.mpr hn)]
  · rw [h]
    simp [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]

/-- Only the next vertex below and the next column at the same height meet
an unprocessed pivot. This includes every later column. -/
theorem sweep_entry {n r t i j h l} (hr : 2  ≤  r) (hi : r  ≤  i) (hit : i  ≤  t)
    (hj : 0  <  j) (hji : j  <  i) (hih : i  ≤  h) (hht : h  ≤  t)
    (hl : 0  <  l) (hlh : l  <  h) (hfuture : h = i → l  <  j)
    (skipFirst : Bool) (k : Grid n) (hki : k.i = i) (hkj : k.j = j) :
    sweepRow r t skipFirst i j h l k =
      (if h = i ∧ l+1 = j then -1 else 0) + (if h = i+1 ∧ l = j then 1 else 0) := by
  by_cases hsame : h = i
  · have hlt := hfuture hsame
    subst h
    by_cases hadj : l+1=j
    · have hlj : l=j-1 := by omega
      subst l
      simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, columnLower, e, hki, hkj, hadj]
    · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, columnLower, e, hki, hkj, hadj]
  · by_cases hnext : h=i+1
    · subst h
      by_cases htop : l=i
      · subst l
        simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor,
          e, hki, hkj]
      · by_cases hlevel : l=j
        · subst l
          simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, originalLower, e, hki, hkj]
        · by_cases hpassed : j<l
          · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, columnLower, e, hki, hkj, hpassed]
          · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, originalLower, e, hki, hkj, hpassed]
    · by_cases htop : l=h-1
      · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor,
          e, hki, hkj, htop]
      · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, originalLower, e, hki, hkj, htop]

theorem sweep_entry_after {n r t i j h l} (hr : 2  ≤  r) (hi : r  ≤  i) (hit : i  ≤  t)
    (hj : 0  <  j) (hji : j  <  i) (hih : i  ≤  h) (hht : h  ≤  t)
    (hl : 0  <  l) (hlh : l  <  h) (hfuture : h = i → l  <  j)
    (skipFirst : Bool) (k : Grid n) (hki : k.i = i) (hkj : k.j = j) :
    sweepRow r t skipFirst i (j-1) h l k =
      (if h = i ∧ l+1 = j then 1 else 0) + (if h = i+1 ∧ l = j then -1 else 0) := by
  by_cases hsame : h = i
  · have hlt := hfuture hsame
    subst h
    by_cases hadj : l+1=j
    · have hlj : l=j-1 := by omega
      subst l
      simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor, columnLower, e, hki, hkj, hadj]
    · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor, columnLower, e, hki, hkj, hadj]
  · by_cases hnext : h=i+1
    · subst h
      by_cases htop : l=i
      · subst l
        simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor,
          e, hki, hkj]
      · by_cases hlevel : l=j
        · subst l
          simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, columnLower, originalLower, e, hki, hkj]
        · by_cases hpassed : j<l
          · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor, columnLower, e, hki, hkj, hpassed]
          · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, columnLower, originalLower, e, hki, hkj, hpassed]
    · by_cases htop : l=h-1
      · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, pivotRow, pivotPos, pivotNeg, anchor,
          e, hki, hkj, htop]
      · simp (disch := omega) [ite_eq_left, ite_eq_right, sweepRow, columnLower, originalLower, e, hki, hkj, htop]

theorem target_entry {n r t i j} (hr : 2  ≤  r) (hi : r  ≤  i) (hit : i  ≤  t)
    (hj : 0  <  j) (hji : j  <  i) (skipFirst : Bool) (k : Grid n)
    (hki : k.i = i) (hkj : k.j = j) :
    targetRow r t skipFirst i j k = if i = t then 1 else 0 := by
  unfold targetRow e
  rw [hki,hkj]
  repeat' first | assumption | contradiction | omega | split

/-- One actual mutation advances every pending row. -/
theorem sweep_step {n r t i j h l} (hr : 2  ≤  r) (hi : r  ≤  i) (hit : i  ≤  t)
    (hj : 0  <  j) (hji : j  <  i) (hih : i  ≤  h) (hht : h  ≤  t)
    (hl : 0  <  l) (hlh : l  <  h) (hfuture : h = i → l  <  j)
    (skipFirst : Bool) (k v : Grid n) (hki : k.i = i) (hkj : k.j = j) :
    (if v = k then -sweepRow r t skipFirst i j h l v else
      sweepRow r t skipFirst i j h l v +
        mutationTerm (sweepRow r t skipFirst i j h l k)
          (pivotRow r t skipFirst i j v)) =
    sweepRow r t skipFirst i (j-1) h l v := by
  rw [sweep_entry hr hi hit hj hji hih hht hl hlh hfuture skipFirst k hki hkj]
  have hvk : v = k ↔ v.i = i ∧ v.j = j := by
    constructor
    · intro he; subst v; exact ⟨hki,hkj⟩
    · rintro ⟨hvi,hvj⟩; exact Grid.ext (hvi.trans hki.symm) (hvj.trans hkj.symm)
  by_cases hv : v=k
  · subst v
    simp only [ite_true]
    rw [sweep_entry hr hi hit hj hji hih hht hl hlh hfuture skipFirst k hki hkj,
      sweep_entry_after hr hi hit hj hji hih hht hl hlh hfuture skipFirst k hki hkj]
    split_ifs <;> omega
  · have he : e i j v=0 := by simp [e, mt hvk.mpr hv]
    simp only [ite_eq_right hv]
    unfold mutationTerm
    rw [(pivot_parts hr hi hit hj hji skipFirst v).1,
      (pivot_parts hr hi hit hj hji skipFirst v).2]
    have hi1 : i-1+1=i := by omega
    by_cases hsame : h=i
    · have hlt := hfuture hsame
      rw [hsame] at *
      by_cases hadj : l+1=j
      · have hlj : l=j-1 := by omega
        rw [hlj]
        have hjj : j-1+1=j := by omega
        have hnottop : j-1≠i-1 := by omega
        simp (disch := omega) only [and_true, true_and, true_or, or_true, false_or, or_false, ite_true, ite_false, sweepRow, pivotRow, pivotPos, pivotNeg,
          columnLower, originalLower, hjj, ite_eq_left, ite_eq_right]
        split_ifs <;> simp_all [posPart, Nat.sub_add_cancel (show 1 ≤ i by omega)] <;> (try omega) <;> (try ring)
      · have hn : l≠j-1 := by omega
        simp (disch := omega) only [and_true, true_and, true_or, or_true, false_or, or_false, ite_true, ite_false, sweepRow, ite_eq_left, ite_eq_right]
        norm_num [posPart]
    · by_cases hnext : h=i+1
      · rw [hnext] at *
        by_cases hlvl : l=j
        · rw [hlvl]
          simp (disch := omega) only [and_true, true_and, true_or, or_true, false_or, or_false, ite_true, ite_false, sweepRow, pivotRow, pivotPos, pivotNeg,
            columnLower, originalLower, ite_eq_left, ite_eq_right,
            show i+1-1=i by omega]
          norm_num [posPart]
          split_ifs <;> simp_all [posPart, Nat.sub_add_cancel (show 1 ≤ i by omega)] <;> (try omega) <;> (try ring)
        · have hsamecond : (j<l) ↔ (j-1<l) := by omega
          simp (disch := omega) only [and_true, true_and, true_or, or_true, false_or, or_false, ite_true, ite_false, sweepRow, hsamecond, ite_eq_left, ite_eq_right]
          norm_num [posPart]
      · simp (disch := omega) only [and_true, true_and, true_or, or_true, false_or, or_false, ite_true, ite_false, sweepRow, ite_eq_left, ite_eq_right]
        norm_num [posPart]

/-- The deletion expression advances by the same actual mutation. -/
theorem target_step {n r t i j} (hr : 2  ≤  r) (hi : r  ≤  i) (hit : i  ≤  t)
    (hj : 0  <  j) (hji : j  <  i) (skipFirst : Bool) (k v : Grid n)
    (hki : k.i = i) (hkj : k.j = j) :
    (if v = k then -targetRow r t skipFirst i j v else
      targetRow r t skipFirst i j v +
        mutationTerm (targetRow r t skipFirst i j k)
          (pivotRow r t skipFirst i j v)) =
    targetRow r t skipFirst i (j-1) v := by
  rw [target_entry hr hi hit hj hji skipFirst k hki hkj]
  have hvk : v = k ↔ v.i = i ∧ v.j = j := by
    constructor
    · intro he; subst v; exact ⟨hki,hkj⟩
    · rintro ⟨hvi,hvj⟩; exact Grid.ext (hvi.trans hki.symm) (hvj.trans hkj.symm)
  by_cases hv : v=k
  · subst v
    simp only [ite_true]
    by_cases ht : i=t <;>
      simp (disch := omega) only [and_true, true_and, true_or, or_true, ite_true, ite_false, targetRow, e, hki, hkj, ite_eq_left, ite_eq_right] <;>
      (try split_ifs) <;> (try omega)
  · have he : e i j v=0 := by simp [e, mt hvk.mpr hv]
    simp only [ite_eq_right hv]
    unfold mutationTerm
    rw [(pivot_parts hr hi hit hj hji skipFirst v).1,
      (pivot_parts hr hi hit hj hji skipFirst v).2]
    by_cases ht : i=t
    · have hjj : j-1+1=j := by omega
      rw [ht] at he hi hji hit hki ⊢
      simp (disch := omega) only [and_true, true_and, true_or, or_true, ite_true, ite_false, targetRow, pivotPos, ite_eq_left, ite_eq_right, hjj]
      norm_num [posPart]
      (try split_ifs) <;> (try omega) <;> simp_all [posPart] <;> ring
    · simp (disch := omega) only [and_true, true_and, true_or, or_true, ite_true, ite_false, targetRow, ite_eq_left, ite_eq_right]
      norm_num [posPart]

end FgStrip.CommonEdge
