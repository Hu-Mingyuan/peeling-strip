import FgStrip.CommonEdge.State

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell
variable {n p : ℕ} (hn : 2*p+3 ≤ n) (b : Bool)

/-- A bounded prefix of the concrete column word. -/
def columnsPrefix (q : ℕ) (hq : q ≤ n-p-1-(p+2)+1) : List (wordLive (n := n) p b) :=
  (List.range q).attach.flatMap fun k =>
    columnWord hn b (p+2+k.val) (by omega) (by
      have hk := List.mem_range.mp k.property
      omega)

@[simp] theorem columnsPrefix_zero : columnsPrefix hn b 0 (by omega)=[] := rfl

/-- A total family used only to compare dependent finite prefixes. -/
def totalColumn (q : ℕ) : List (wordLive (n := n) p b) :=
  columnWord hn b (min (p+2+q) (n-p-1)) (by omega) (by omega)

theorem columnsPrefix_flatMap (q : ℕ) (hq : q ≤ n-p-1-(p+2)+1) :
    columnsPrefix hn b q hq=(List.range q).flatMap (totalColumn hn b) := by
  calc
    _ = (List.range q).attach.flatMap (fun k => totalColumn hn b k.val) := by
      apply List.flatMap_congr
      intro k hk
      have hmem := List.mem_range.mp k.property
      have hm : min (p+2+k.val) (n-p-1)=p+2+k.val := by omega
      simp only [totalColumn, hm]
    _ = _ := by
      rw [← List.flatMap_map, List.attach_map_subtype_val]

theorem columnsPrefix_succ (q : ℕ) (hq : q+1 ≤ n-p-1-(p+2)+1) :
    columnsPrefix hn b (q+1) hq=columnsPrefix hn b q (by omega) ++
      columnWord hn b (p+2+q) (by omega) (by omega) := by
  rw [columnsPrefix_flatMap, columnsPrefix_flatMap, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hm : min (p+2+q) (n-p-1)=p+2+q := by omega
  simp only [totalColumn, hm]

theorem prefix_ready (q : ℕ) (hq : q ≤ n-p-1-(p+2)) :
    SweepState hn b
      (mutateWord (mutateWord (restrictMatrix (matrix n) Subtype.val) (diagonalWord hn b))
        (columnsPrefix hn b q (by omega))) (p+2+q) (p+2+q-1) := by
  induction q with
  | zero => simpa only [columnsPrefix_zero, mutateWord_nil, Nat.add_zero,
      show p+2-1=p+1 by omega] using initial_state hn b
  | succ q ih =>
    rw [columnsPrefix_succ, mutateWord_append]
    have hs := (ih (by omega)).column hn b (by omega) (by omega)
    have hnxt := hs.next hn b (by omega) (by omega)
    convert hnxt using 1 <;> omega

/-- The complete actual word leaves the deletion vertex a sink. In the shortest
modified case its row retains the extra negative upper-triangle neighbour. -/
theorem forward_target_row (v : wordLive (n := n) p b) :
    mutateWord (restrictMatrix (matrix n) Subtype.val) (forwardWord hn b) (target hn b) v =
      -e (n-p-1) 1 v.val -
        (if b=true ∧ p+2=n-p-1 then e (n-p-2) (n-p-1) v.val else 0) := by
  have hs := (prefix_ready hn b (n-p-1-(p+2)) (by omega)).column hn b (by omega) (by omega)
  have hi : p+2+(n-p-1-(p+2))=n-p-1 := by omega
  have hw : columnsWord hn b=
      columnsPrefix hn b (n-p-1-(p+2)) (by omega) ++
        columnWord hn b (n-p-1) (by omega) (by omega) := by
    change columnsPrefix hn b (n-p-1-(p+2)+1) (by omega)=_
    rw [columnsPrefix_succ]
    simp only [hi]
  have hrow := hs.1 v
  simp only [hi] at hrow
  rw [forwardWord, mutateWord_append, hw, mutateWord_append]
  rw [hrow]
  simp (disch := omega) [targetRow, e_zero_bottom, ite_eq_left, ite_eq_right,
    show n-p-1-1=n-p-2 by omega]

theorem forward_sink : IsSink
    (mutateWord (restrictMatrix (matrix n) Subtype.val) (forwardWord hn b)) (target hn b) := by
  intro v
  rw [forward_target_row hn b]
  have h1 := e_nonneg (i := n-p-1) (j := 1) v.val
  have h2 := e_nonneg (i := n-p-2) (j := n-p-1) v.val
  split_ifs <;> omega

end FgStrip.CommonEdge
