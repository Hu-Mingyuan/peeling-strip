import FgStrip.TriangleShell.Cycles
import FgStrip.TriangleShell.Path

namespace FgStrip.TriangleShell
open Triangle

/-- The manuscript's strictly interior corner subsets. -/
def cornerSet {n : ℕ} (p : ℕ) : Set (Vertex n) :=
  {v | 0 < v.a ∧ 0 < v.b ∧ 0 < v.c ∧ (v.a+v.c ≤ p ∨ v.b+v.c ≤ p)}

/-- Boundary omission, both side depths, and removal of `C_p`. -/
def baseLive {n : ℕ} (p : ℕ) : Set (Vertex n) :=
  {v | 0 < v.c ∧ p < v.a+v.c ∧ p < v.b+v.c ∧
    (v.a=0 ∨ v.b=0 → v.c+p < n)}

/-- Explicit correspondence with the manuscript's live set. -/
theorem baseLive_iff {n p : ℕ} (hp : p < n) (v : Vertex n) :
    v ∈ baseLive p ↔ 0 < v.c ∧
      ((v.a=0 ∨ v.b=0) → p < v.c ∧ v.c < n-p) ∧ v ∉ cornerSet p := by
  have ht := v.total
  simp only [baseLive, cornerSet, Set.mem_ofPred_eq]
  omega

/-- Before deleting `s_a`, the earlier first-family vertices have `a' > a`. -/
def firstLive {n : ℕ} (p a : ℕ) : Set (Vertex n) :=
  {v | v ∈ baseLive p ∧ (v.b=n-p-1 → v.a ≤ a)}

@[simp] theorem cornerSet_exchange {n p : ℕ} (v : Vertex n) :
    exchange v ∈ cornerSet p ↔ v ∈ cornerSet p := by
  simp only [cornerSet, Set.mem_ofPred_eq, exchange_a, exchange_b, exchange_c]
  tauto

@[simp] theorem baseLive_exchange {n p : ℕ} (v : Vertex n) :
    exchange v ∈ baseLive p ↔ v ∈ baseLive p := by
  simp only [baseLive, Set.mem_ofPred_eq, exchange_a, exchange_b, exchange_c]
  tauto

/-- The shell is exactly the two indicated coordinate lines. -/
theorem shell_iff {n p : ℕ} (v : Vertex n) :
    v ∈ cornerSet (p+1) ∧ v ∉ cornerSet p ↔
      0 < v.a ∧ 0 < v.b ∧ 0 < v.c ∧ p < v.a+v.c ∧ p < v.b+v.c ∧
      (v.a+v.c=p+1 ∨ v.b+v.c=p+1) := by
  simp only [cornerSet, Set.mem_ofPred_eq]
  omega

/-- The two shell families meet only in the odd endpoint. -/
theorem shell_overlap {n p : ℕ} (hn : 2*p+1 ≤ n) (v : Vertex n)
    (hc : 0 < v.c) (ha : v.a+v.c=p+1) (hb : v.b+v.c=p+1) :
    n=2*p+1 ∧ v.a=p ∧ v.b=p ∧ v.c=1 := by
  have := v.total
  omega

/-- The source order is decreasing first coordinate. -/
theorem firstLive_start {n p : ℕ} (hn : 2*p+1 ≤ n) :
    firstLive (n := n) p p = baseLive p := by
  ext v
  have ht := v.total
  simp only [firstLive, baseLive, Set.mem_ofPred_eq]
  omega

/-- Every point in the path, including its endpoint, is present and interior. -/
def lineVertex {n p a : ℕ} (hn : 2*p+1 ≤ n) (ha : 1 ≤ a) (hap : a ≤ p)
    (b : ℕ) (hb : 1 ≤ b) (hbt : b ≤ n-p-1) : firstLive (n := n) p a :=
  ⟨Vertex.mk a b (n-a-b) (by omega) (by omega) (by omega) (by omega), by
    simp only [firstLive, baseLive, Set.mem_ofPred_eq, Vertex.mk_a, Vertex.mk_b,
      Vertex.mk_c]
    omega⟩

@[simp] theorem lineVertex_a {n p a hn ha hap b hb hbt} :
    (lineVertex (n := n) (p := p) (a := a) hn ha hap b hb hbt).val.a = a := rfl
@[simp] theorem lineVertex_b {n p a hn ha hap b hb hbt} :
    (lineVertex (n := n) (p := p) (a := a) hn ha hap b hb hbt).val.b = b := rfl
@[simp] theorem lineVertex_c {n p a hn ha hap b hb hbt} :
    (lineVertex (n := n) (p := p) (a := a) hn ha hap b hb hbt).val.c = n-a-b := rfl

theorem lineVertex_interior {n p a hn ha hap b hb hbt} :
    0 < (lineVertex (n := n) (p := p) (a := a) hn ha hap b hb hbt).val.a ∧
    0 < (lineVertex (n := n) (p := p) (a := a) hn ha hap b hb hbt).val.b ∧
    0 < (lineVertex (n := n) (p := p) (a := a) hn ha hap b hb hbt).val.c := by
  simp only [lineVertex_a, lineVertex_b, lineVertex_c]
  omega

/-- Indicators of `A_b` and `B_b`, automatically zero when the label is absent. -/
def off {n : ℕ} (a b : ℕ) (j : Vertex n) : ℤ :=
  (if j.a+1=a ∧ j.b=b+1 then 1 else 0) +
  (if j.a=a+1 ∧ j.b=b then 1 else 0)

theorem off_nonneg {n a b} (j : Vertex n) : 0 ≤ off a b j := by
  unfold off
  split_ifs <;> omega

theorem off_line_zero {n a b} (j : Vertex n) (ha : j.a=a) : off a b j = 0 := by
  unfold off
  split_ifs <;> omega

theorem off_disjoint {n a b} (j : Vertex n) : off a b j = 0 ∨ off a (b+1) j = 0 := by
  unfold off
  split_ifs <;> omega

/-- Coordinate indicators on the fixed line. -/
def onLine {n : ℕ} (a b : ℕ) (j : Vertex n) : ℤ :=
  if j.a=a ∧ j.b=b then 1 else 0

/-- The unmutated complete interior expression, derived from the six cycle directions. -/
theorem matrix_interior_row {n : ℕ} (u j : Vertex n)
    (ha : 0 < u.a) (hb : 0 < u.b) (hc : 0 < u.c) :
    matrix n u j = off u.a (u.b-1) j - off u.a u.b j +
      onLine u.a (u.b+1) j - onLine u.a (u.b-1) j := by
  have hu := u.total
  have hj := j.total
  rw [matrix_eq]
  unfold off onLine
  have e₁ : (j.a+1=u.a ∧ j.b=u.b ∧ j.c=u.c+1 ∧ 0 < u.b) ↔
      (j.a+1=u.a ∧ j.b=u.b-1+1) := by omega
  have e₂ : (j.a=u.a+1 ∧ j.b+1=u.b ∧ j.c=u.c ∧ 0 < u.c) ↔
      (j.a=u.a+1 ∧ j.b=u.b-1) := by omega
  have e₃ : (j.a=u.a ∧ j.b=u.b+1 ∧ j.c+1=u.c ∧ 0 < u.a) ↔
      (j.a=u.a ∧ j.b=u.b+1) := by omega
  have e₄ : (u.a+1=j.a ∧ u.b=j.b ∧ u.c=j.c+1 ∧ 0 < j.b) ↔
      (j.a=u.a+1 ∧ j.b=u.b) := by omega
  have e₅ : (u.a=j.a+1 ∧ u.b+1=j.b ∧ u.c=j.c ∧ 0 < j.c) ↔
      (j.a+1=u.a ∧ j.b=u.b+1) := by omega
  have e₆ : (u.a=j.a ∧ u.b=j.b+1 ∧ u.c+1=j.c ∧ 0 < j.a) ↔
      (j.a=u.a ∧ j.b=u.b-1) := by omega
  simp only [e₁,e₂,e₃,e₄,e₅,e₆]
  ring

/-- The incoming off-line labels at `s_a` have already been removed. -/
theorem off_endpoint_zero {n p a : ℕ} (hn : 2*p+1 ≤ n)
    (ha : 1 ≤ a) (hap : a ≤ p) (j : firstLive (n := n) p a) :
    off a (n-p-1) j.val = 0 := by
  have ht := j.val.total
  obtain ⟨⟨hc,hac,hbc,he⟩, hj⟩ := j.property
  unfold off
  split_ifs <;> omega

/-- The next point beyond the endpoint lies in a removed corner region. -/
theorem onLine_after_zero {n p a : ℕ} (j : firstLive (n := n) p a) :
    onLine a (n-p) j.val = 0 := by
  have ht := j.val.total
  obtain ⟨⟨hc,hac,hbc,he⟩, hj⟩ := j.property
  unfold onLine
  split_ifs <;> omega

/-- The point preceding the first pivot lies on a deleted side portion. -/
theorem onLine_zero_zero {n p a : ℕ} (hap : a ≤ p)
    (j : firstLive (n := n) p a) : onLine a 0 j.val = 0 := by
  have ht := j.val.total
  obtain ⟨⟨hc,hac,hbc,he⟩, hj⟩ := j.property
  unfold onLine
  split_ifs <;> omega

end FgStrip.TriangleShell
