import FgStrip.CommonEdge.Geometry

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

variable {n p : ℕ} (hn : 2*p+3 ≤ n) (skipFirst : Bool)

/-- First diagonal index, shifted by one for the modified word. -/
def start : ℕ := p+1+(if skipFirst then 1 else 0)

/-- The common deletion vertex in the coordinates of either calculation. -/
def target : wordLive (n := n) p skipFirst :=
  ⟨diag (n-p-1) (by omega) (by omega), diag_live (by omega) (by omega), by
    intro _ he
    have h : n-p-1=p+1 := he.1
    omega⟩

/-- A total diagonal path; only its prefix below `t` is used. -/
def diagonalPath (q : ℕ) : wordLive (n := n) p skipFirst :=
  let k := min (start (p := p) skipFirst+q) (n-p-1)
  ⟨diag k (by unfold k start; split_ifs <;> omega) (by unfold k; omega),
    diag_live (by unfold k start; split_ifs <;> omega) (by unfold k; omega), by
      intro hb he
      have hk : k=p+1 := he.1
      unfold k at hk
      simp only [start, hb, ite_true] at hk
      omega⟩

/-- The displayed diagonal word, in increasing order. -/
def diagonalWord : List (wordLive (n := n) p skipFirst) :=
  pathWord (diagonalPath hn skipFirst) (n-p-1-start (p := p) skipFirst)

/-- One lower-triangle column, with its actual live vertices. -/
def columnPath (i : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1) (q : ℕ) :
    wordLive (n := n) p skipFirst :=
  let j := max 1 (i-1-q)
  ⟨X i j (by unfold j; omega) (by unfold j; omega) (by omega),
    X_live hn hi hit (by unfold j; omega) (by unfold j; omega), by
      intro _ he
      have he' : i=p+1 := he.1
      omega⟩

def columnWord (i : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1) :
    List (wordLive (n := n) p skipFirst) :=
  pathWord (columnPath hn skipFirst i hi hit) (i-1)

/-- Columns `r,...,t`, each read from top to bottom. -/
def columnsWord : List (wordLive (n := n) p skipFirst) :=
  ((List.range (n-p-1-(p+2)+1)).attach).flatMap fun q =>
    columnWord hn skipFirst (p+2+q.val) (by omega) (by
      have hq := List.mem_range.mp q.property
      omega)

def forwardWord : List (wordLive (n := n) p skipFirst) :=
  diagonalWord hn skipFirst ++ columnsWord hn skipFirst

@[simp] theorem target_i : (target hn skipFirst).val.i=n-p-1 := rfl
@[simp] theorem target_j : (target hn skipFirst).val.j=n-p-1 := rfl
@[simp] theorem diagonalPath_i (q : ℕ) :
    (diagonalPath hn skipFirst q).val.i=min (start (p := p) skipFirst+q) (n-p-1) := rfl
@[simp] theorem diagonalPath_j (q : ℕ) :
    (diagonalPath hn skipFirst q).val.j=min (start (p := p) skipFirst+q) (n-p-1) := rfl
@[simp] theorem columnPath_i (i hi hit q) :
    (columnPath hn skipFirst i hi hit q).val.i=i := rfl
@[simp] theorem columnPath_j (i hi hit q) :
    (columnPath hn skipFirst i hi hit q).val.j=max 1 (i-1-q) := rfl

theorem diagonalWord_region (k : wordLive (n := n) p skipFirst)
    (hk : k ∈ diagonalWord hn skipFirst) : pivotRegion p skipFirst k.val := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
  have hq' := List.mem_range.mp hq
  left
  simp only [diagonalPath_i, diagonalPath_j, start] at *
  cases skipFirst <;> simp_all [start] <;> omega

theorem columnWord_region (i : ℕ) (hi : p+2 ≤ i) (hit : i ≤ n-p-1)
    (k : wordLive (n := n) p skipFirst) (hk : k ∈ columnWord hn skipFirst i hi hit) :
    pivotRegion p skipFirst k.val := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hk
  right
  simp only [columnPath_i, columnPath_j]
  omega

theorem forwardWord_region (k : wordLive (n := n) p skipFirst)
    (hk : k ∈ forwardWord hn skipFirst) : pivotRegion p skipFirst k.val := by
  rcases List.mem_append.mp hk with hd | hc
  · exact diagonalWord_region hn skipFirst k hd
  · obtain ⟨q,hq,hkq⟩ := List.mem_flatMap.mp hc
    exact columnWord_region hn skipFirst _ _ _ k hkq

theorem forwardWord_supported (k : wordLive (n := n) p skipFirst)
    (hk : k ∈ forwardWord hn skipFirst) : k.val ∈ support n :=
  pivot_supported hn (forwardWord_region hn skipFirst k hk)

theorem forwardWord_avoids (k : wordLive (n := n) p skipFirst)
    (hk : k ∈ forwardWord hn skipFirst) : k ≠ target hn skipFirst := by
  intro he
  have ha := pivot_avoids (forwardWord_region hn skipFirst k hk)
  apply ha
  rw [he]
  exact ⟨rfl,rfl⟩

/-- The forward word on the surviving subtype, so target avoidance is part of its type. -/
def deletionWord : List (Remaining (target hn skipFirst)) :=
  (forwardWord hn skipFirst).attach.map fun k =>
    ⟨k.val, forwardWord_avoids hn skipFirst k.val k.property⟩

@[simp] theorem deletionWord_map : (deletionWord hn skipFirst).map Subtype.val =
    forwardWord hn skipFirst := by
  simp only [deletionWord, List.map_map, Function.comp_def]
  exact List.attach_map_subtype_val _

theorem deletionWord_supported (k : Remaining (target hn skipFirst))
    (hk : k ∈ deletionWord hn skipFirst) : k.val.val ∈ support n := by
  apply forwardWord_supported hn skipFirst k.val
  rw [← deletionWord_map hn skipFirst]
  exact List.mem_map.mpr ⟨k,hk,rfl⟩

end FgStrip.CommonEdge
