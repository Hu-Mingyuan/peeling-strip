import FgStrip.CommonEdge.Diagonal
import FgStrip.CommonEdge.Sweep

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

variable {n p : ℕ} (hn : 2*p+3 ≤ n) (b : Bool)

/-- Sum the actual diagonal corrections over the chosen live interval. The
omitted-pivot word has a different lower bound in this calculation. -/
theorem top_after_diagonal_interval (i : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (v : wordLive (n := n) p b) :
    mutateWord (restrictMatrix (matrix n) Subtype.val) (diagonalWord hn b)
      (columnPath hn b i hi hit 0) v =
    originalLower i (i-1) v.val +
      (if start (p := p) b ≤ i-1 ∧ i-1 < n-p-1 then previousCorrection i v.val else 0) +
      (if start (p := p) b ≤ i ∧ i < n-p-1 then nextCorrection i v.val else 0) := by
  have hx : (columnPath hn b i hi hit 0).val=X i (i-1) (by omega) (by omega) (by omega) := by
    apply Grid.ext
    · rfl
    · change max 1 (i-1-0)=i-1
      omega
  have hu : columnPath hn b i hi hit 0 ∉ diagonalWord hn b := by
    intro hk
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hk
    have hei := congrArg (fun u : wordLive (n := n) p b => u.val.i) he
    have hej := congrArg (fun u : wordLive (n := n) p b => u.val.j) he
    simp only [columnPath_i, columnPath_j, diagonalPath_i, diagonalPath_j] at hei hej
    omega
  rw [independent_word_row _ (SkewSymmetric.restrictMatrix (B := matrix n) matrix_skew _) _
    (diagonalWord_nodup hn b) (diagonalWord_disconnected hn b) _ hu]
  have hbase : restrictMatrix (matrix n) Subtype.val (columnPath hn b i hi hit 0) v =
      originalLower i (i-1) v.val := by
    change matrix n _ v.val=_
    rw [hx,lower_row]
    rfl
  rw [hbase]
  have hstart : start (p := p) b ≤ n-p-1 := by cases b <;> simp [start] <;> omega
  have hmap : (diagonalWord hn b).map (fun k =>
      rowCorrection (restrictMatrix (matrix n) Subtype.val) (columnPath hn b i hi hit 0) k v) =
      (List.range (n-p-1-start (p := p) b)).map (fun q =>
        (if start (p := p) b+q=i-1 then previousCorrection i v.val else 0)+
        (if start (p := p) b+q=i then nextCorrection i v.val else 0)) := by
    simp only [diagonalWord, pathWord, List.map_map]
    apply List.map_congr_left
    intro q hq
    have hq' := List.mem_range.mp hq
    have hmin : min (start (p := p) b+q) (n-p-1)=start (p := p) b+q := by omega
    have hcorr : rowCorrection (restrictMatrix (matrix n) Subtype.val)
        (columnPath hn b i hi hit 0) (diagonalPath hn b q) v =
        rowCorrection (matrix n) (columnPath hn b i hi hit 0).val
          (diagonalPath hn b q).val v.val := by
      simp only [rowCorrection, restrictMatrix, Matrix.submatrix, Subtype.ext_iff] <;> rfl
    change rowCorrection _ _ _ _=_
    rw [hcorr,hx]
    change rowCorrection _ _ (diag _ _ _) _=_
    rw [top_diagonal_correction (by omega) (by omega), hmin]
  rw [hmap, List.sum_map_add, range_indicator_sum, range_indicator_sum]
  have hsum : start (p := p) b+(n-p-1-start (p := p) b)=n-p-1 := by omega
  rw [hsum]
  ring

/-- Complete top-row expressions after the actual ordinary or modified diagonal word. -/
theorem top_after_diagonal (i : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (v : wordLive (n := n) p b) :
    mutateWord (restrictMatrix (matrix n) Subtype.val) (diagonalWord hn b)
      (columnPath hn b i hi hit 0) v =
    pivotRow (p+2) (n-p-1) b i (i-1) v.val := by
  rw [top_after_diagonal_interval hn b i hi hit v]
  have hi1 : i-1+1=i := by omega
  have hi2 : i-1-1=i-2 := by omega
  have hr1 : p+2-1=p+1 := by omega
  have hfirst : i=p+2 → e (i-1) (i-2) v.val=0 := by
    intro h
    have hf := first_column_left_zero hn (b := b) (j := p) (by omega) v
    simpa [h, show p+2-1=p+1 by omega, show p+2-2=p by omega] using hf
  have homit : b=true → i=p+2 → e (i-1) (i-1) v.val=0 := by
    intro hb hi'
    subst b
    simpa [hi', hr1] using omitted_diagonal_zero v
  cases b <;> by_cases hr : i=p+2 <;> by_cases ht : i=n-p-1 <;>
    simp (disch := omega) only [start, Bool.false_eq_true,
      ite_true, ite_false, and_true, true_and, false_and,
      originalLower, previousCorrection, nextCorrection,
      pivotRow, pivotPos, pivotNeg, anchor, hi1, hi2, hr1, ite_eq_left, ite_eq_right] <;>
    simp_all <;> try ring

end FgStrip.CommonEdge
