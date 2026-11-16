import FgStrip.TwoTriangle
import FgStrip.TriangleShell

/-! Common-edge live sets and supported words. Blueprint §§3–5. -/
namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

/-- The interiors and common edge; the two interfaces are excluded. -/
def support (n : ℕ) : Set (Grid n) :=  {u | 0   <   u.i  ∧  u.i   <   n}

/-- Depth `p` on all three edges and `C_(p+1)` in both interiors. -/
def live {n : ℕ} (p : ℕ) : Set (Grid n) := 
  {u | ¬deletedEdge p u  ∧  ¬CX (p+1) u.val  ∧  ¬CY (p+1) u.val}

/-- Coordinates of the two endpoints to remove. A set counts coincidence once. -/
def endpoints {n : ℕ} (p : ℕ) : Set (Grid n) := 
  {u | u.i = u.j  ∧  (u.j = p+1 ∨ u.j = n-p-1)}

def finish {n : ℕ} (p : ℕ) : Set (Grid n) :=  live p \ endpoints p

/-- Coordinates can denote an absent label; its coefficient is then zero. -/
def e {n : ℕ} (i j : ℕ) (u : Grid n) : ℤ := 
  if u.i = i  ∧  u.j = j then 1 else 0

theorem e_nonneg {n i j} (u : Grid n) : 0   ≤   e i j u :=  by
  unfold e; split_ifs  <;> omega

theorem e_zero_bottom {n i} (u : Grid n) : e i 0 u = 0 :=  by
  have :=  u.j_pos
  simp [e, show u.j≠0 by omega]

/-- A proof-friendly equivalent form, still quantifying over the full grid. -/
theorem mem_live_iff {n p} (u : Grid n) : u ∈ live p ↔
    ((u.i = 0 ∨ u.i = u.j ∨ u.i = n) → p  <  u.j  ∧  u.j+p  <  n)  ∧ 
    (u.j  <  u.i  ∧  u.i  <  n → p+1  <  u.i  ∧  u.i-u.j  <  n-p-1)  ∧ 
    (0  <  u.i  ∧  u.i  <  u.j → u.i  <  n-p-1  ∧  u.j-u.i  <  n-p-1) :=  by
  have :=  u.i_le; have :=  u.j_pos; have :=  u.j_lt
  simp only [live, Set.mem_ofPred_eq, deletedEdge, EdgeDepth, CX, CY]
  change _ ↔ _
  change ¬((u.i = 0 ∨ u.i = u.j ∨ u.i = n)  ∧  (u.j  ≤  p ∨ n-p  ≤  u.j))  ∧ 
    ¬(0  <  u.j  ∧  u.j  <  u.i  ∧  u.i  <  n  ∧  (n-(u.i-u.j)  ≤  p+1 ∨ u.i  ≤  p+1))  ∧ 
    ¬(0  <  u.i  ∧  u.i  <  u.j  ∧  u.j  <  n  ∧  (n-(u.j-u.i)  ≤  p+1 ∨ n-u.i  ≤  p+1)) ↔ _
  omega

theorem live_halfturn {n p} (u : Grid n) : H u ∈ live p ↔ u ∈ live p :=  by
  have :=  u.i_le; have :=  u.j_pos; have :=  u.j_lt
  rw [mem_live_iff, mem_live_iff, H_i, H_j]
  omega

theorem endpoints_live {n p} (hn : 2*p+2  ≤  n) : endpoints (n :=  n) p ⊆ live p :=  by
  intro u hu
  have :=  u.j_pos; have :=  u.j_lt
  rcases hu with ⟨hij,hj | hj⟩  <;> rw [mem_live_iff]  <;> omega

theorem endpoints_supported {n p} : endpoints (n :=  n) p ⊆ support n :=  by
  intro u hu
  have :=  u.j_pos; have :=  u.j_lt
  exact ⟨by change 0  <  u.i; rw [hu.1]; assumption,
    by change u.i  <  n; rw [hu.1]; assumption⟩

theorem deleted_exact {n p} (hn : 2*p+2  ≤  n) :
    live (n :=  n) p \ finish p  =  endpoints p :=  by
  ext u
  have :=  endpoints_live hn (a :=  u)
  simp only [finish, Set.mem_sdiff]
  tauto

/-- The diagonal vertex with an explicit numerical index. -/
def diag {n} (k : ℕ) (h0 : 0  <  k) (hn : k  <  n) : Grid n := 
  D ⟨⟨k,hn⟩,h0⟩
@[simp] theorem diag_i {n k h0 hn} : (diag (n :=  n) k h0 hn).i = k :=  rfl
@[simp] theorem diag_j {n k h0 hn} : (diag (n :=  n) k h0 hn).j = k :=  rfl

theorem diag_live {n p k} (h0 : p  <  k) (hn : k+p  <  n) :
    diag k (by omega) (by omega) ∈ live (n :=  n) p :=  by
  rw [mem_live_iff]; simp only [diag_i, diag_j]; omega

theorem X_live {n p i j} (hn : 2*p+3  ≤  n) (hi : p+2  ≤  i) (hit : i  ≤  n-p-1)
    (hj : 0  <  j) (hji : j  <  i) : X i j hj hji (by omega) ∈ live (n :=  n) p :=  by
  rw [mem_live_iff]
  change ((i = 0 ∨ i = j ∨ i = n) → _)  ∧  _
  dsimp [X, Grid.i, Grid.j]
  omega

/-- Live set for either calculation. In the second, `D_(p+1)` is absent. -/
def wordLive {n} (p : ℕ) (skipFirst : Bool) : Set (Grid n) := 
  {u | u ∈ live p  ∧  (skipFirst = true → ¬(u.i = p+1  ∧  u.j = p+1))}

theorem wordLive_false {n p} : wordLive (n :=  n) p false = live p :=  by
  ext u; simp [wordLive]

/-- All pivots, in their geometric ranges, excluding the deletion vertex. -/
def pivotRegion {n} (p : ℕ) (skipFirst : Bool) (u : Grid n) : Prop := 
  (u.i = u.j  ∧  p+1+(if skipFirst then 1 else 0)  ≤  u.i  ∧  u.i  <  n-p-1) ∨
  (p+2  ≤  u.i  ∧  u.i  ≤  n-p-1  ∧  u.j  <  u.i)

theorem pivot_live {n p skipFirst} (hn : 2*p+3  ≤  n) {u : Grid n}
    (hu : pivotRegion p skipFirst u) : u ∈ wordLive p skipFirst :=  by
  have :=  u.i_le; have :=  u.j_pos; have :=  u.j_lt
  rw [wordLive, Set.mem_ofPred_eq, mem_live_iff]
  change ((u.i = u.j ∧ p+1+(if skipFirst then 1 else 0)  ≤  u.i ∧ u.i  <  n-p-1) ∨
    (p+2  ≤  u.i ∧ u.i  ≤  n-p-1 ∧ u.j  <  u.i)) at hu
  cases skipFirst  <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> simp only [Grid.i, Grid.j] at * <;> (try simp only [false_implies, and_true]) <;> omega

theorem pivot_supported {n p skipFirst} (hn : 2*p+3  ≤  n) {u : Grid n}
    (hu : pivotRegion p skipFirst u) : u ∈ support n :=  by
  have :=  u.j_pos
  dsimp [pivotRegion] at hu
  dsimp [support]
  split_ifs at hu  <;> omega

theorem pivot_avoids {n p skipFirst} {u : Grid n} (hu : pivotRegion p skipFirst u) :
    ¬(u.i = n-p-1  ∧  u.j = n-p-1) :=  by
  dsimp [pivotRegion] at hu
  omega

end FgStrip.CommonEdge
