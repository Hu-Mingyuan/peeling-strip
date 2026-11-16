import FgStrip.CommonEdge.Mutation
import FgStrip.CommonEdge.Words

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

/-- All diagonal vertices are pairwise disconnected in the concrete matrix. -/
theorem diagonal_zero {n k l} (hk : 0 < k) (hkn : k < n) (hl : 0 < l) (hln : l < n) :
    matrix n (diag k hk hkn) (diag l hl hln)=0 := by
  rw [diagonal_row]
  simp only [e, diag_i, diag_j]
  split_ifs <;> omega

/-- The four diagonal neighbours split into their two exact signed parts. -/
theorem diagonal_parts {n k} (hk : 0 < k) (hkn : k < n) (v : Grid n) :
    posPart (matrix n (diag k hk hkn) v)=e k (k-1) v + e k (k+1) v ∧
    posPart (-matrix n (diag k hk hkn) v)=e (k+1) k v + e (k-1) k v := by
  rw [diagonal_row]
  unfold posPart e
  split_ifs <;> omega

/-- A top vertex meets precisely its two adjacent diagonal pivots. -/
theorem top_diagonal {n i k} (hi0 : 2 ≤ i) (hin : i < n) (hk : 0 < k) (hkn : k < n) :
    matrix n (X i (i-1) (by omega) (by omega) hin) (diag k hk hkn) =
      (if k=i-1 then 1 else 0) - (if k=i then 1 else 0) := by
  rw [lower_row]
  simp only [e, diag_i, diag_j]
  split_ifs <;> omega

/-- Lower vertices do not meet a diagonal pivot. -/
theorem lower_diagonal_zero {n i j k} (hj : 0 < j) (hji : j+1 < i)
    (hin : i < n) (hk : 0 < k) (hkn : k < n) :
    matrix n (X i j hj (by omega) hin) (diag k hk hkn)=0 := by
  rw [lower_row]
  simp only [e, diag_i, diag_j]
  split_ifs <;> omega

/-- The exact correction from the earlier of the two diagonal neighbours. -/
def previousCorrection {n} (i : ℕ) (v : Grid n) : ℤ :=
  -2*e (i-1) (i-1) v + e (i-1) (i-2) v + e (i-1) i v

/-- The exact correction from the later diagonal neighbour. -/
def nextCorrection {n} (i : ℕ) (v : Grid n) : ℤ :=
  2*e i i v - e (i+1) i v - e (i-1) i v

/-- Each actual diagonal mutation has an explicitly evaluated correction.
The second word will sum these over a different interval of live pivots. -/
theorem top_diagonal_correction {n i k} (hi0 : 2 ≤ i) (hin : i < n)
    (hk : 0 < k) (hkn : k < n) (v : Grid n) :
    rowCorrection (matrix n) (X i (i-1) (by omega) (by omega) hin) (diag k hk hkn) v =
      (if k=i-1 then previousCorrection i v else 0) +
      (if k=i then nextCorrection i v else 0) := by
  have heq : v=diag k hk hkn ↔ v.i=k ∧ v.j=k := by
    constructor
    · intro h; subst v; exact ⟨rfl,rfl⟩
    · rintro ⟨hi,hj⟩; exact Grid.ext hi hj
  unfold rowCorrection
  by_cases hv : v=diag k hk hkn
  · subst v
    rw [if_pos rfl, top_diagonal hi0 hin hk hkn]
    simp only [previousCorrection, nextCorrection, e, diag_i, diag_j]
    split_ifs <;> omega
  · rw [if_neg hv, top_diagonal hi0 hin hk hkn]
    have hv' := mt heq.mpr hv
    unfold mutationTerm
    rw [(diagonal_parts hk hkn v).1, (diagonal_parts hk hkn v).2]
    by_cases hprev : k=i-1
    · have hnext : k≠i := by omega
      simp only [ite_eq_left hprev, ite_eq_right hnext]
      norm_num only [posPart, max_self, max_eq_right (by omega : (-1:ℤ) ≤ 0),
        max_eq_left (by omega : (0:ℤ) ≤ 1), zero_mul, one_mul, zero_sub, sub_zero, add_zero]
      have he : e (i-1) (i-1) v=0 := by
        unfold e
        rw [ite_eq_right]
        simpa only [hprev] using hv'
      simp only [previousCorrection, hprev, he, zero_mul, mul_zero, neg_zero, zero_add,
        show i-1-1=i-2 by omega, show i-1+1=i by omega]
    · by_cases hnext : k=i
      · simp only [ite_eq_right hprev, ite_eq_left hnext]
        norm_num only [posPart, max_self, max_eq_right (by omega : (-1:ℤ) ≤ 0),
          max_eq_left (by omega : (0:ℤ) ≤ 1), zero_mul, one_mul, zero_sub, sub_zero, zero_add]
        have he : e i i v=0 := by
          unfold e
          rw [ite_eq_right]
          simpa only [hnext] using hv'
        simp only [nextCorrection, hnext, he, mul_zero]
        ring
      · simp [hprev,hnext,posPart]


section Word
variable {n p : ℕ} (hn : 2*p+3 ≤ n) (b : Bool)

theorem diagonalWord_nodup : (diagonalWord hn b).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_range)
  intro q hq k hk he
  have hq' := List.mem_range.mp hq
  have hk' := List.mem_range.mp hk
  have hv := congrArg (fun x : wordLive (n := n) p b => x.val.i) he
  simp only [diagonalPath_i] at hv
  omega

theorem diagonalWord_disconnected (k : wordLive (n := n) p b)
    (hk : k ∈ diagonalWord hn b) (l : wordLive (n := n) p b)
    (hl : l ∈ diagonalWord hn b) : matrix n k.val l.val=0 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hl
  exact diagonal_zero _ _ _ _

theorem target_after_diagonal (v : wordLive (n := n) p b) :
    mutateWord (restrictMatrix (matrix n) Subtype.val) (diagonalWord hn b)
      (target hn b) v =
    e (n-p-1) (n-p-2) v.val - e (n-p) (n-p-1) v.val -
      e (n-p-2) (n-p-1) v.val := by
  rw [row_mutateWord_zero]
  · change matrix n (diag _ _ _) v.val = _
    rw [diagonal_row]
    have ht : n-p-1+1=n-p := by omega
    have ht' : n-p-1-1=n-p-2 := by omega
    rw [ht,ht',target_upper_zero hn v]
    ring
  · intro k hk
    exact (forwardWord_avoids hn b k (List.mem_append_left _ hk)).symm
  · intro k hk
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
    exact diagonal_zero _ _ _ _

theorem lower_after_diagonal (i j : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (hj : 0 < j) (hji : j+1 < i) (v : wordLive (n := n) p b) :
    mutateWord (restrictMatrix (matrix n) Subtype.val) (diagonalWord hn b)
      (columnPath hn b i hi hit (i-1-j)) v =
    e (i+1) (j+1) v.val - e (i+1) j v.val - e i (j+1) v.val +
      e i (j-1) v.val + e (i-1) j v.val - e (i-1) (j-1) v.val := by
  have hx : (columnPath hn b i hi hit (i-1-j)).val=X i j hj (by omega) (by omega) := by
    apply Grid.ext
    · rfl
    · change max 1 (i-1-(i-1-j))=j
      omega
  rw [row_mutateWord_zero]
  · change matrix n _ v.val = _
    rw [hx,lower_row]
  · intro k hk he
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
    have hei := congrArg (fun u : wordLive (n := n) p b => u.val.i) he
    have hej := congrArg (fun u : wordLive (n := n) p b => u.val.j) he
    simp only [hx, diagonalPath_i, diagonalPath_j] at hei hej
    change i=_ at hei
    change j=_ at hej
    omega
  · intro k hk
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
    change matrix n _ _=0
    rw [hx]
    exact lower_diagonal_zero hj hji (by omega) _ _

end Word
end FgStrip.CommonEdge
