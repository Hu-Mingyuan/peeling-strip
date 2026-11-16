import FgStrip.CommonEdge.Top

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

variable {n p : ℕ} (hn : 2*p+3 ≤ n) (b : Bool)

/-- A lower-interior point in either live set, with unclamped coordinates. -/
def lowerPoint (i j : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (hj : 0 < j) (hji : j < i) : wordLive (n := n) p b :=
  ⟨X i j hj hji (by omega), X_live hn hi hit hj hji, by
    intro hb he
    have h : i=p+1 := he.1
    omega⟩

@[simp] theorem lowerPoint_i (i j hi hit hj hji) :
    (lowerPoint hn b i j hi hit hj hji).val.i=i := rfl
@[simp] theorem lowerPoint_j (i j hi hit hj hji) :
    (lowerPoint hn b i j hi hit hj hji).val.j=j := rfl

theorem columnPath_lowerPoint (i j : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (hj : 0 < j) (hji : j < i) :
    columnPath hn b i hi hit (i-1-j)=lowerPoint hn b i j hi hit hj hji := by
  apply Subtype.ext
  apply Grid.ext
  · rfl
  · change max 1 (i-1-(i-1-j))=j
    omega

/-- Complete expressions on every live column for the target and all future pivots. -/
def SweepState (B : Matrix (wordLive (n := n) p b) (wordLive (n := n) p b) ℤ) (i j : ℕ) : Prop :=
  (∀ v, B (target hn b) v=targetRow (p+2) (n-p-1) b i j v.val) ∧
  ∀ h l (hh : p+2 ≤ h) (ht : h ≤ n-p-1) (hl : 0 < l) (hlh : l < h),
    i ≤ h → (h=i → l ≤ j) → ∀ v,
    B (lowerPoint hn b h l hh ht hl hlh) v=sweepRow (p+2) (n-p-1) b i j h l v.val

/-- A single concrete mutation advances the full future-row invariant. -/
theorem SweepState.step {B : Matrix (wordLive (n := n) p b) (wordLive (n := n) p b) ℤ}
    {i j : ℕ} (hi : p+2 ≤ i) (hit : i ≤ n-p-1) (hj : 0 < j) (hji : j < i)
    (hstate : SweepState hn b B i j) :
    SweepState hn b (mutate B (lowerPoint hn b i j hi hit hj hji)) i (j-1) := by
  let k := lowerPoint hn b i j hi hit hj hji
  have hpiv : ∀ v, B k v=pivotRow (p+2) (n-p-1) b i j v.val := by
    intro v
    rw [hstate.2 i j hi hit hj hji (by omega) (by omega)]
    simp [sweepRow]
  constructor
  · intro v
    have hne : target hn b ≠ k := by
      intro he
      have hei := congrArg (fun x : wordLive (n := n) p b => x.val.i) he
      have hej := congrArg (fun x : wordLive (n := n) p b => x.val.j) he
      simp only [target_i, target_j, k, lowerPoint_i, lowerPoint_j] at hei hej
      omega
    change (if target hn b=k ∨ v=k then -B (target hn b) v else
      B (target hn b) v+mutationTerm (B (target hn b) k) (B k v))=_
    simp only [hne, false_or]
    rw [hstate.1 v, hstate.1 k, hpiv v]
    have heq : v=k ↔ v.val=k.val := Subtype.ext_iff
    simp only [heq]
    exact target_step (by omega) hi hit hj hji b k.val v.val rfl rfl
  · intro h l hh ht hl hlh hih hfuture v
    have hstrict : h=i → l < j := by intro he; have := hfuture he; omega
    have hweak : h=i → l ≤ j := by intro he; have := hfuture he; omega
    have hne : lowerPoint hn b h l hh ht hl hlh ≠ k := by
      intro he
      have hei := congrArg (fun x : wordLive (n := n) p b => x.val.i) he
      have hej := congrArg (fun x : wordLive (n := n) p b => x.val.j) he
      simp only [k, lowerPoint_i, lowerPoint_j] at hei hej
      have := hstrict hei
      omega
    change (if lowerPoint hn b h l hh ht hl hlh=k ∨ v=k then
      -B (lowerPoint hn b h l hh ht hl hlh) v else
      B (lowerPoint hn b h l hh ht hl hlh) v+
        mutationTerm (B (lowerPoint hn b h l hh ht hl hlh) k) (B k v))=_
    simp only [hne, false_or]
    rw [hstate.2 h l hh ht hl hlh hih hweak v,
      hstate.2 h l hh ht hl hlh hih hweak k, hpiv v]
    have heq : v=k ↔ v.val=k.val := Subtype.ext_iff
    simp only [heq]
    exact sweep_step (by omega) hi hit hj hji hih ht hl hlh hstrict b k.val v.val rfl rfl

/-- Actual mutation of a prefix of one descending column. -/
theorem SweepState.column_prefix {B : Matrix (wordLive (n := n) p b) (wordLive (n := n) p b) ℤ}
    {i : ℕ} (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (hstate : SweepState hn b B i (i-1)) (q : ℕ) (hq : q ≤ i-1) :
    SweepState hn b (mutateWord B (pathWord (columnPath hn b i hi hit) q)) i (i-1-q) := by
  induction q with
  | zero => simpa [pathWord] using hstate
  | succ q ih =>
    have hj : 0 < i-1-q := by omega
    have hji : i-1-q < i := by omega
    have he : columnPath hn b i hi hit q=lowerPoint hn b i (i-1-q) hi hit hj hji := by
      apply Subtype.ext
      apply Grid.ext
      · rfl
      · change max 1 (i-1-q)=i-1-q
        omega
    rw [pathWord_succ, mutateWord_append]
    simp only [mutateWord_cons, mutateWord_nil, he]
    have hs := (ih (by omega)).step hn b hi hit hj hji
    simpa only [show i-1-q-1=i-1-(q+1) by omega] using hs

theorem SweepState.column {B : Matrix (wordLive (n := n) p b) (wordLive (n := n) p b) ℤ}
    {i : ℕ} (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (hstate : SweepState hn b B i (i-1)) :
    SweepState hn b (mutateWord B (columnWord hn b i hi hit)) i 0 := by
  simpa only [columnWord, Nat.sub_self] using hstate.column_prefix hn b hi hit (i-1) (by omega)

/-- Finishing a column gives exactly the invariant for the next column. -/
theorem SweepState.next {B : Matrix (wordLive (n := n) p b) (wordLive (n := n) p b) ℤ}
    {i : ℕ} (hi : p+2 ≤ i) (hit : i < n-p-1)
    (hstate : SweepState hn b B i 0) : SweepState hn b B (i+1) i := by
  constructor
  · intro v
    rw [hstate.1]
    simp (disch := omega) [targetRow, ite_eq_left, ite_eq_right]
  · intro h l hh ht hl hlh hih hfuture v
    rw [hstate.2 h l hh ht hl hlh (by omega) (by omega)]
    unfold sweepRow
    split_ifs <;> (first | rfl | omega)

/-- The initial sweep invariant follows from the actual diagonal calculation,
including the missing first pivot and the absent first-column labels. -/
theorem initial_state : SweepState hn b
    (mutateWord (restrictMatrix (matrix n) Subtype.val) (diagonalWord hn b)) (p+2) (p+1) := by
  constructor
  · intro v
    rw [target_after_diagonal hn b]
    simp (disch := omega) only [targetRow, ite_eq_right,
      show n-p-1-1=n-p-2 by omega, show n-p-1+1=n-p by omega]
  · intro h l hh ht hl hlh hih hfuture v
    by_cases htop : l=h-1
    · have he : lowerPoint hn b h l hh ht hl hlh=columnPath hn b h hh ht 0 := by
        apply Subtype.ext
        apply Grid.ext
        · rfl
        · change l=max 1 (h-1-0)
          omega
      rw [he,top_after_diagonal hn b]
      simp only [sweepRow, htop, ite_true]
    · have hlt : l+1 < h := by omega
      rw [← columnPath_lowerPoint hn b h l hh ht hl hlh, lower_after_diagonal hn b h l hh ht hl hlt]
      change originalLower h l v.val=sweepRow (p+2) (n-p-1) b (p+2) (p+1) h l v.val
      by_cases hfirst : h=p+2
      · have hz1 : e (h-1) l v.val=0 := by
          have hz := first_column_left_zero hn (b := b) (j := l) (by omega) v
          simpa only [hfirst, show p+2-1=p+1 by omega] using hz
        have hz2 : e (h-1) (l-1) v.val=0 := by
          have hz := first_column_left_zero hn (b := b) (j := l-1) (by omega) v
          simpa only [hfirst, show p+2-1=p+1 by omega] using hz
        simp (disch := omega) only [sweepRow, columnLower, originalLower,
          and_true, true_and, true_or, or_true, ite_true, ite_false, ite_eq_left, ite_eq_right,
          hz1, hz2]
        ring
      · simp (disch := omega) only [sweepRow, ite_eq_left, ite_eq_right]

end FgStrip.CommonEdge
