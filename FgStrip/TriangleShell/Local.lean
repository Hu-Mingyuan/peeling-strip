import FgStrip.TriangleShell.Geometry

namespace FgStrip.TriangleShell
open Triangle

section Local
variable {n p a : ℕ} (hn : 2*p+1 ≤ n) (ha : 1 ≤ a) (hap : a ≤ p)

/-- Extend the finite line by its last vertex. Only indices through `n-p-2` are used. -/
def linePath (i : ℕ) : firstLive (n := n) p a :=
  lineVertex hn ha hap (min (i+1) (n-p-1)) (by omega) (by omega)

@[simp] theorem linePath_a (i : ℕ) : (linePath hn ha hap i).val.a = a := rfl

theorem linePath_b (i : ℕ) (hi : i ≤ n-p-2) :
    (linePath hn ha hap i).val.b = i+1 := by
  change min (i+1) (n-p-1) = i+1
  omega

theorem linePath_c (i : ℕ) (hi : i ≤ n-p-2) :
    (linePath hn ha hap i).val.c = n-a-(i+1) := by
  change n-a-min (i+1) (n-p-1) = _
  congr 1
  omega

theorem linePath_injective (i : ℕ) (hi : i ≤ n-p-2) (k : ℕ) (hk : k ≤ n-p-2)
    (h : linePath hn ha hap i = linePath hn ha hap k) : i=k := by
  have he := congrArg (fun x : firstLive (n := n) p a => x.val.b) h
  rw [linePath_b hn ha hap i hi, linePath_b hn ha hap k hk] at he
  omega

theorem linePath_interior (i : ℕ) :
    0 < (linePath hn ha hap i).val.a ∧ 0 < (linePath hn ha hap i).val.b ∧
      0 < (linePath hn ha hap i).val.c :=
  lineVertex_interior

theorem onLine_eq_delta (i : ℕ) (hi : i ≤ n-p-2) (j : firstLive (n := n) p a) :
    onLine a (i+1) j.val = delta (linePath hn ha hap i) j := by
  have ht := j.val.total
  have hpath := (linePath hn ha hap i).val.total
  have he : (j.val.a=a ∧ j.val.b=i+1) ↔ j=linePath hn ha hap i := by
    constructor
    · rintro ⟨hj₁,hj₂⟩
      apply Subtype.ext
      apply Vertex.ext
      · simpa using hj₁
      · simpa [linePath_b hn ha hap i hi] using hj₂
      · have ha' := linePath_a hn ha hap i
        have hb' := linePath_b hn ha hap i hi
        omega
    · intro h; subst j
      simp [linePath_b hn ha hap i hi]
  simp only [onLine, delta, he]

/-- Original rows for the path induction; the endpoint omits only proved absent labels. -/
theorem linePath_original_row (i : ℕ) (hi : i ≤ n-p-2)
    (j : firstLive (n := n) p a) :
    restrictMatrix (matrix n) Subtype.val (linePath hn ha hap i) j =
      off a i j.val - (if i < n-p-2 then off a (i+1) j.val else 0) +
      (if i < n-p-2 then delta (linePath hn ha hap (i+1)) j else 0) -
      (if 0 < i then delta (linePath hn ha hap (i-1)) j else 0) := by
  have hpos := linePath_interior hn ha hap i
  rw [restrictMatrix_apply, matrix_interior_row _ _ hpos.1 hpos.2.1 hpos.2.2,
    linePath_a, linePath_b hn ha hap i hi]
  simp only [Nat.add_sub_cancel]
  have hprev : onLine a i j.val =
      if 0 < i then delta (linePath hn ha hap (i-1)) j else 0 := by
    by_cases hp : 0 < i
    · have hi' : i-1 ≤ n-p-2 := by omega
      have h := onLine_eq_delta hn ha hap (i-1) hi' j
      have he : i-1+1=i := by omega
      simpa [hp, he] using h
    · have hi0 : i=0 := by omega
      subst i
      simpa using onLine_zero_zero hap j
  rw [hprev]
  by_cases hlt : i < n-p-2
  · simp only [ite_eq_left hlt]
    rw [onLine_eq_delta hn ha hap (i+1) (by omega)]
  · have hit : i+1=n-p-1 := by omega
    have hit' : i+1+1=n-p := by omega
    simp only [ite_eq_right hlt, sub_zero, add_zero]
    rw [hit, off_endpoint_zero hn ha hap, show n-p-1+1=n-p by omega,
      onLine_after_zero]
    ring

/-- Complete endpoint expression after the actual listed mutation word. -/
theorem first_final_row (hn4 : 4 ≤ n) (j : firstLive (n := n) p a) :
    mutateWord (restrictMatrix (matrix n) Subtype.val)
      (pathWord (linePath hn ha hap) (n-p-2)) (linePath hn ha hap (n-p-2)) j =
      delta (linePath hn ha hap (n-p-2-1)) j := by
  apply path_final_row (restrictMatrix (matrix n) Subtype.val) (n-p-2)
    (linePath hn ha hap) (fun i j => off a i j.val)
  · exact linePath_injective hn ha hap
  · intro i hi j; exact off_nonneg _
  · intro i hi k hk
    exact off_line_zero _ (linePath_a hn ha hap k)
  · intro j; exact off_disjoint j.val
  · exact linePath_original_row hn ha hap
  · omega

/-- The endpoint is interior, and each listed pivot is present and different from it. -/
theorem first_word_avoids (k : firstLive (n := n) p a)
    (hk : k ∈ pathWord (linePath hn ha hap) (n-p-2)) :
    k ≠ linePath hn ha hap (n-p-2) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
  have hi' : i < n-p-2 := List.mem_range.mp hi
  intro he
  have := linePath_injective hn ha hap i (by omega) (n-p-2) (by omega) he
  omega

/-- The actual word in the surviving type, with the target excluded by proof. -/
def firstWord : List (Remaining (linePath hn ha hap (n-p-2))) :=
  (pathWord (linePath hn ha hap) (n-p-2)).attach.map
    (fun k => ⟨k.val, first_word_avoids hn ha hap k.val k.property⟩)

@[simp] theorem firstWord_map :
    (firstWord hn ha hap).map Subtype.val = pathWord (linePath hn ha hap) (n-p-2) := by
  simp only [firstWord, List.map_map, Function.comp_def]
  exact List.attach_map_subtype_val _

/-- No finite-rank calculation is used for the rank-three endpoint. -/
theorem rank_three_row (hn3 : n=3) (j : firstLive (n := n) p a) :
    restrictMatrix (matrix n) Subtype.val (linePath hn ha hap (n-p-2)) j = 0 := by
  have hp1 : p=1 := by omega
  have ha1 : a=1 := by omega
  have ht := j.val.total
  obtain ⟨⟨hc,hac,hbc,he⟩, hj⟩ := j.property
  have hja : j.val.a=1 := by omega
  have hjb : j.val.b=1 := by omega
  have hjc : j.val.c=1 := by omega
  have heq : j=linePath hn ha hap (n-p-2) := by
    apply Subtype.ext
    apply Vertex.ext
    · simp [hja, ha1]
    · rw [linePath_b hn ha hap _ (by omega)]
      omega
    · rw [linePath_c hn ha hap _ (by omega)]
      omega
  rw [heq, restrictMatrix_apply]
  have hskew := mapMatrix_skew (n := n) id
    (linePath hn ha hap (n-p-2)).val (linePath hn ha hap (n-p-2)).val
  change matrix n _ _ = -matrix n _ _ at hskew
  omega

/-- A concrete first-family deletion move, with no assumed local identity. -/
def firstMove : DeletionMove (firstLive (n := n) p a)
    (restrictMatrix (matrix n) Subtype.val) where
  vertex := linePath hn ha hap (n-p-2)
  word := firstWord hn ha hap
  source_or_sink := by
    unfold ValidDeletionWord
    rw [firstWord_map]
    left
    intro j
    by_cases hn4 : 4 ≤ n
    · rw [first_final_row hn ha hap hn4]
      exact delta_nonneg _ _
    · have hn3 : n=3 := by omega
      have hm : n-p-2=0 := by omega
      simp only [hm, pathWord_zero, mutateWord_nil]
      have h := rank_three_row hn ha hap hn3 j
      rw [hm] at h
      rw [h]

@[simp] theorem firstMove_vertex :
    (firstMove hn ha hap).vertex = linePath hn ha hap (n-p-2) := rfl

end Local
end FgStrip.TriangleShell
