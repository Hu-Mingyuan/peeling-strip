import FgStrip.Rounds.Transport

namespace FgStrip.Rounds
open TriangleShell

/-- Triangle numbering in the manuscript starts at one. -/
def faceIndex {N : ℕ} (f : Strip.Face N) : ℕ :=
  2*f.1.val + if f.2 then 2 else 1

theorem faceIndex_bounds {N} (f : Strip.Face N) :
    1 ≤ faceIndex f ∧ faceIndex f ≤ 2*N := by
  have := f.1.isLt
  rcases f with ⟨i,b⟩
  cases b <;> simp only [faceIndex, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Exact transverse-edge depth after round `p`, including both protected ends. -/
def edgeDepth (N p j : ℕ) : ℕ := min p (min j (2*N-j))

/-- Exact triangle corner depth after round `p`. -/
def faceDepth (N p i : ℕ) : ℕ := min p (min i (2*N-i+1))

/-- An arbitrary edge/triangle depth profile on the actual glued strip. -/
def profileLive {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) : Set (Strip.Vertex n N) :=
  {v | (∀ j k, Strip.edgeEmbedding hN j k=v →
      d j < k.val ∧ k.val < n-d j) ∧
    ∀ f (x : Triangle.Interior n), Strip.interiorEmbedding f x=v →
      x.val ∉ cornerSet (c f)}

/-- The precise round invariant's live set, on the glued representation. -/
def roundLive {n N} (hN : 0 < N) (p : ℕ) : Set (Strip.Vertex n N) :=
  profileLive hN (fun j => edgeDepth N p j.val) (fun f => faceDepth N p (faceIndex f))

@[simp] theorem edgeDepth_zero (N j : ℕ) : edgeDepth N 0 j=0 := by simp [edgeDepth]
@[simp] theorem faceDepth_zero (N i : ℕ) : faceDepth N 0 i=0 := by simp [faceDepth]
@[simp] theorem edgeDepth_left (N p : ℕ) : edgeDepth N p 0=0 := by simp [edgeDepth]
@[simp] theorem edgeDepth_right (N p : ℕ) : edgeDepth N p (2*N)=0 := by simp [edgeDepth]

theorem edgeDepth_central {N p j} (hl : p ≤ j) (hr : p+j ≤ 2*N) :
    edgeDepth N p j=p := by simp only [edgeDepth]; omega

theorem faceDepth_central {N p i} (hl : p ≤ i) (hr : p+i ≤ 2*N+1) :
    faceDepth N p i=p := by simp only [faceDepth]; omega

theorem edgeDepth_mono {N p q j} (hpq : p ≤ q) : edgeDepth N p j ≤ edgeDepth N q j := by
  simp only [edgeDepth]; omega

theorem faceDepth_mono {N p q i} (hpq : p ≤ q) : faceDepth N p i ≤ faceDepth N q i := by
  simp only [faceDepth]; omega

@[simp] theorem cornerSet_zero {n} : cornerSet (n := n) 0=∅ := by
  ext v
  simp only [cornerSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  omega

@[simp] theorem cornerSet_one {n} : cornerSet (n := n) 1=∅ := by
  ext v
  simp only [cornerSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  omega

theorem cornerSet_mono {n p q} (hpq : p ≤ q) :
    cornerSet (n := n) p ⊆ cornerSet q := by
  intro v hv
  simp only [cornerSet, Set.mem_setOf_eq] at *
  omega

@[simp] theorem roundLive_zero {n N} (hN : 0 < N) :
    roundLive (n := n) hN 0=Set.univ := by
  ext v
  simp only [roundLive, profileLive, Set.mem_setOf_eq, Set.mem_univ, iff_true,
    edgeDepth_zero, faceDepth_zero, cornerSet_zero, Set.mem_empty_iff_false,
    not_false_eq_true, implies_true, and_true, Nat.sub_zero]
  intro j k _
  exact ⟨k.pos,k.lt⟩

theorem profileLive_edge {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (j : Strip.EdgeIndex N) (k : Triangle.EdgeWeight n) :
    Strip.edgeEmbedding hN j k ∈ profileLive hN d c ↔
      d j < k.val ∧ k.val < n-d j := by
  constructor
  · intro hv; exact hv.1 j k rfl
  · intro hk
    constructor
    · intro l m he
      have hew := congrArg (fun v : Strip.Vertex n N => Strip.weight v.val) he
      change Strip.weight (Strip.edgeVertex hN l m).val =
        Strip.weight (Strip.edgeVertex hN j k).val at hew
      rw [Strip.weight_edgeVertex, Strip.weight_edgeVertex] at hew
      obtain ⟨rfl,rfl⟩ := Strip.edgeWeight_injective hew
      exact hk
    · intro f x he
      exact (Strip.interior_ne_edge hN f x j k he).elim

theorem profileLive_interior {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (f : Strip.Face N) (x : Triangle.Interior n) :
    Strip.interiorEmbedding f x ∈ profileLive hN d c ↔ x.val ∉ cornerSet (c f) := by
  constructor
  · intro hv; exact hv.2 f x rfl
  · intro hx
    constructor
    · intro j k he
      exact (Strip.interior_ne_edge hN f x j k he.symm).elim
    · intro g y he
      have hh := (Strip.interior_glue_eq_iff g f y x.val).mp (congrArg Subtype.val he)
      rcases hh with ⟨rfl,hh⟩
      simpa only [hh] using hx

theorem roundLive_antitone {n N} (hN : 0 < N) {p q} (hpq : p ≤ q) :
    roundLive (n := n) hN q ⊆ roundLive hN p := by
  intro v hv
  constructor
  · intro j k he
    have hh := hv.1 j k he
    have hd := edgeDepth_mono (N := N) (j := j.val) hpq
    dsimp at hh ⊢
    omega
  · intro f x he hc
    exact hv.2 f x he (cornerSet_mono (faceDepth_mono hpq) hc)

/-- The prescribed terminal depth removes the middle edge for every parity of `N`. -/
theorem middle_not_mem_roundLive {n N} (hN : 0 < N) (hNq : n/2 ≤ N)
    (v : Strip.Vertex n N) (hv : v ∈ Strip.middle hN) :
    v ∉ roundLive hN (n/2) := by
  obtain ⟨k,rfl⟩ := hv
  intro hl
  have hk := (profileLive_edge hN _ _ (Strip.middleEdge N) k).mp hl
  have hd : edgeDepth N (n/2) (Strip.middleEdge N).val=n/2 :=
    edgeDepth_central hNq (by simp only [Strip.middleEdge]; omega)
  rw [hd] at hk
  omega

/-- No protected edge vertex belongs to the prescribed deleted set. -/
theorem protected_mem_roundLive {n N} (hN : 0 < N) (p : ℕ)
    (v : Strip.Vertex n N) (hv : v ∈ Strip.protectedSet hN) : v ∈ roundLive hN p := by
  rcases hv with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · apply (profileLive_edge hN _ _ _ _).mpr
    change edgeDepth N p 0 < k.val ∧ k.val < n-edgeDepth N p 0
    simpa using And.intro k.pos k.lt
  · apply (profileLive_edge hN _ _ _ _).mpr
    change edgeDepth N p (2*N) < k.val ∧ k.val < n-edgeDepth N p (2*N)
    simpa using And.intro k.pos k.lt

end FgStrip.Rounds
