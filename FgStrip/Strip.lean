import FgStrip.Triangle

/-! The strip is glued by weights at its distinct polygon vertices.
No local mutation or deletion assertion is an input to this construction. -/

namespace FgStrip
namespace Strip
open Triangle

/-- `false` denotes the top side and `true` the bottom side. -/
abbrev Polygon (N : ℕ) := Bool × Fin (N + 1)
/-- `(i,false)` is `(T_{i+1},T_i,B_i)`; `(i,true)` is
`(B_i,B_{i+1},T_{i+1})`, in the displayed cyclic orders. -/
abbrev Face (N : ℕ) := Fin N × Bool

def corner₀ {N : ℕ} (f : Face N) : Polygon N :=
  if f.2 then (true, f.1.castSucc) else (false, f.1.succ)
def corner₁ {N : ℕ} (f : Face N) : Polygon N :=
  if f.2 then (true, f.1.succ) else (false, f.1.castSucc)
def corner₂ {N : ℕ} (f : Face N) : Polygon N :=
  if f.2 then (false, f.1.succ) else (true, f.1.castSucc)

@[simp] theorem corner₀_ne_corner₁ {N : ℕ} (f : Face N) : corner₀ f ≠ corner₁ f := by
  rcases f with ⟨i, b⟩; cases b <;> simp [corner₀, corner₁, Fin.ext_iff]
@[simp] theorem corner₀_ne_corner₂ {N : ℕ} (f : Face N) : corner₀ f ≠ corner₂ f := by
  rcases f with ⟨i, b⟩; cases b <;> simp [corner₀, corner₂]
@[simp] theorem corner₁_ne_corner₂ {N : ℕ} (f : Face N) : corner₁ f ≠ corner₂ f := by
  rcases f with ⟨i, b⟩; cases b <;> simp [corner₁, corner₂]

/-- Barycentric weights extended by zero to all named polygon vertices. -/
def localWeight {n N : ℕ} (f : Face N) (p : Triangle.Vertex n) (v : Polygon N) : ℕ :=
  (if v = corner₀ f then p.a else 0) +
  (if v = corner₁ f then p.b else 0) +
  (if v = corner₂ f then p.c else 0)

@[simp] theorem localWeight_corner₀ {n N} (f : Face N) (p : Triangle.Vertex n) :
    localWeight f p (corner₀ f) = p.a := by simp [localWeight]
@[simp] theorem localWeight_corner₁ {n N} (f : Face N) (p : Triangle.Vertex n) :
    localWeight f p (corner₁ f) = p.b := by
  simp [localWeight, Ne.symm (corner₀_ne_corner₁ f)]
@[simp] theorem localWeight_corner₂ {n N} (f : Face N) (p : Triangle.Vertex n) :
    localWeight f p (corner₂ f) = p.c := by
  simp [localWeight, Ne.symm (corner₀_ne_corner₂ f), Ne.symm (corner₁_ne_corner₂ f)]

theorem localWeight_injective {n N} (f : Face N) :
    Function.Injective (localWeight (n := n) f) := by
  intro p q h
  apply Triangle.Vertex.ext
  · simpa using congrFun h (corner₀ f)
  · simpa using congrFun h (corner₁ f)
  · simpa using congrFun h (corner₂ f)

abbrev Copy (n N : ℕ) := Face N × Triangle.Vertex n
def copyWeight {n N} (r : Copy n N) : Polygon N → ℕ := localWeight r.1 r.2

/-- Equal weights at the named endpoints implement the edge gluing.
Weights away from a face are zero. In particular, positive interior weights
cannot be identified with a vertex on another face. -/
def gluing (n N : ℕ) : Setoid (Copy n N) := Setoid.ker copyWeight
def Glued (n N : ℕ) := Quotient (gluing n N)
noncomputable instance {n N} : Fintype (Glued n N) := by
  classical
  exact Quotient.fintype _
noncomputable instance {n N} : DecidableEq (Glued n N) := Classical.decEq _

def glue {n N} (f : Face N) (p : Triangle.Vertex n) : Glued n N :=
  Quotient.mk (gluing n N) (f, p)
def weight {n N} : Glued n N → Polygon N → ℕ := Setoid.kerLift copyWeight

@[simp] theorem weight_glue {n N} (f : Face N) (p : Triangle.Vertex n) :
    weight (glue f p) = localWeight f p := rfl

theorem weight_injective {n N} : Function.Injective (weight (n := n) (N := N)) :=
  Setoid.kerLift_injective _

@[simp] theorem glue_eq_iff {n N} (f g : Face N) (p q : Triangle.Vertex n) :
    glue f p = glue g q ↔ localWeight f p = localWeight g q :=
  ⟨fun h => congrArg weight h, fun h => Quotient.sound h⟩

theorem glue_injective {n N} (f : Face N) : Function.Injective (glue (n := n) f) := by
  intro p q h
  exact localWeight_injective f ((glue_eq_iff f f p q).mp h)

/-- The quotient is exactly the finite image of the barycentric weight map. -/
noncomputable def gluedEquivWeightImage (n N : ℕ) :
    Glued n N ≃ Set.range (copyWeight (n := n) (N := N)) :=
  Setoid.quotientKerEquivRange _

/-- Having positive weights on both sides of the strip. -/
def Mixed {N} (w : Polygon N → ℕ) : Prop :=
  (∃ i, 0 < w (false, i)) ∧ (∃ i, 0 < w (true, i))

/-- In each displayed oriented face the actual boundary side is exactly `c=0`. -/
theorem mixed_localWeight_iff {n N} (f : Face N) (p : Triangle.Vertex n) :
    Mixed (localWeight f p) ↔ 0 < p.c := by
  have ht := p.total
  have hc := p.c_lt
  rcases f with ⟨i, b⟩
  cases b
  · constructor
    · rintro ⟨_, j, hj⟩
      simp only [localWeight, corner₀, corner₁, corner₂, Bool.false_eq_true,
        ↓reduceIte, Prod.mk.injEq, Bool.true_eq_false, false_and,
        true_and, zero_add] at hj
      split_ifs at hj <;> omega
    · intro h
      constructor
      · by_cases ha : 0 < p.a
        · exact ⟨i.succ, by simpa [corner₀] using
            (show 0 < localWeight (i, false) p (corner₀ (i, false)) by simpa using ha)⟩
        · exact ⟨i.castSucc, by simpa [corner₁] using
            (show 0 < localWeight (i, false) p (corner₁ (i, false)) by simp; omega)⟩
      · exact ⟨i.castSucc, by simpa [corner₂] using
          (show 0 < localWeight (i, false) p (corner₂ (i, false)) by simpa using h)⟩
  · constructor
    · rintro ⟨⟨j, hj⟩, _⟩
      simp only [localWeight, corner₀, corner₁, corner₂, ↓reduceIte,
        Prod.mk.injEq, Bool.false_eq_true, false_and, true_and, zero_add] at hj
      split_ifs at hj <;> omega
    · intro h
      constructor
      · exact ⟨i.succ, by simpa [corner₂] using
          (show 0 < localWeight (i, true) p (corner₂ (i, true)) by simpa using h)⟩
      · by_cases ha : 0 < p.a
        · exact ⟨i.castSucc, by simpa [corner₀] using
            (show 0 < localWeight (i, true) p (corner₀ (i, true)) by simpa using ha)⟩
        · exact ⟨i.succ, by simpa [corner₁] using
            (show 0 < localWeight (i, true) p (corner₁ (i, true)) by simp; omega)⟩

/-- The actual top and bottom boundary lattice vertices, after gluing. -/
def Boundary {n N} (v : Glued n N) : Prop :=
  ∃ (f : Face N) (p : Triangle.Vertex n), p.c = 0 ∧ glue f p = v

theorem boundary_iff_not_mixed {n N} (v : Glued n N) :
    Boundary v ↔ ¬Mixed (weight v) := by
  induction v using Quotient.inductionOn with
  | h r =>
    rcases r with ⟨f, p⟩
    change Boundary (glue f p) ↔ ¬Mixed (weight (glue f p))
    rw [weight_glue, mixed_localWeight_iff]
    constructor
    · rintro ⟨g, q, hq, heq⟩ hp
      have hw := congrArg (fun v => Mixed (weight v)) heq
      simp only [weight_glue, mixed_localWeight_iff] at hw
      simp [hq, hp] at hw
    · intro hp
      exact ⟨f, p, by omega, rfl⟩

/-- Retained vertices. This removes only the actual boundary, after gluing. -/
def Vertex (n N : ℕ) := {v : Glued n N // Mixed (weight v)}
noncomputable instance {n N} : Fintype (Vertex n N) := by
  classical
  exact inferInstanceAs (Fintype {v : Glued n N // Mixed (weight v)})
noncomputable instance {n N} : DecidableEq (Vertex n N) := Classical.decEq _

/-- The entire retained part of a face embeds in the strip. -/
def faceEmbedding {n N} (f : Face N) :
    {p : Triangle.Vertex n // 0 < p.c} ↪ Vertex n N where
  toFun p := ⟨glue f p.1, (mixed_localWeight_iff f p.1).mpr p.2⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    exact glue_injective f (congrArg Subtype.val h)

def interiorEmbedding {n N} (f : Face N) : Triangle.Interior n ↪ Vertex n N :=
  { toFun := fun p => faceEmbedding f ⟨p.1, p.2.2.2⟩
    inj' := by
      intro p q h
      apply Subtype.ext
      exact congrArg (fun r : {v : Triangle.Vertex n // 0 < v.c} => r.1)
        ((faceEmbedding f).injective h) }

/-- Count all triangle arrows after gluing, before boundary omission. -/
noncomputable def arrowCount {n N} (u v : Glued n N) : ℕ :=
  ∑ f : Face N, Triangle.arrowCount (glue f) u v

noncomputable def gluedMatrix (n N : ℕ) : Matrix (Glued n N) (Glued n N) ℤ :=
  fun u v => (arrowCount u v : ℤ) - arrowCount v u

/-- Integer strip matrix: the cycle sum, restricted after actual boundary omission. -/
noncomputable def matrix (n N : ℕ) : Matrix (Vertex n N) (Vertex n N) ℤ :=
  fun u v => gluedMatrix n N u.1 v.1

theorem matrix_eq_signed_count {n N} (u v : Vertex n N) :
    matrix n N u v = (arrowCount u.1 v.1 : ℤ) - arrowCount v.1 u.1 := rfl

theorem matrix_eq_sum {n N} (u v : Vertex n N) :
    matrix n N u v = ∑ f : Face N, ∑ t : Triangle.Cell n,
      Triangle.cycleEntry (glue f t.first) (glue f t.second) (glue f t.third) u.1 v.1 := by
  simp [matrix, gluedMatrix, arrowCount, Triangle.arrowCount, Triangle.cycleEntry,
    Nat.cast_sum, Finset.sum_sub_distrib]

theorem matrix_skew {n N} (u v : Vertex n N) : matrix n N u v = -matrix n N v u := by
  simp only [matrix_eq_signed_count]; omega

@[simp] theorem matrix_diag {n N} (u : Vertex n N) : matrix n N u u = 0 := by
  simp [matrix_eq_signed_count]

/-- Transverse edges in their source order, including both end edges. -/
abbrev EdgeIndex (N : ℕ) := Fin (2 * N + 1)

def edgeTop {N} (j : EdgeIndex N) : Fin (N + 1) :=
  ⟨(j.val + 1) / 2, by have := j.isLt; omega⟩
def edgeBottom {N} (j : EdgeIndex N) : Fin (N + 1) :=
  ⟨j.val / 2, by have := j.isLt; omega⟩

/-- The weight `k` is the weight at the bottom endpoint of `e_j`. -/
def edgeWeight {n N} (j : EdgeIndex N) (k : EdgeWeight n) (v : Polygon N) : ℕ :=
  (if v = (false, edgeTop j) then n - k.val else 0) +
  (if v = (true, edgeBottom j) then k.val else 0)

@[simp] theorem edgeWeight_top {n N} (j : EdgeIndex N) (k : EdgeWeight n) :
    edgeWeight j k (false, edgeTop j) = n - k.val := by simp [edgeWeight]
@[simp] theorem edgeWeight_bottom {n N} (j : EdgeIndex N) (k : EdgeWeight n) :
    edgeWeight j k (true, edgeBottom j) = k.val := by simp [edgeWeight]

theorem mixed_edgeWeight {n N} (j : EdgeIndex N) (k : EdgeWeight n) :
    Mixed (edgeWeight j k) := by
  exact ⟨⟨edgeTop j, by simp; have := k.lt; omega⟩, ⟨edgeBottom j, by simp; exact k.pos⟩⟩

/-- An explicit triangle copy representing each transverse edge point.
Only `N>0` is needed; neither the rank bound nor any parity condition is used. -/
def edgeCopy {n N} (hN : 0 < N) (j : EdgeIndex N) (k : EdgeWeight n) : Copy n N :=
  if hj : j.val < 2 * N then
    ((⟨j.val / 2, by omega⟩, false),
      if j.val % 2 = 0 then k.bc else
        Triangle.Vertex.mk (n - k.val) 0 k.val (by have := k.lt; omega)
          (by have := k.lt; have := k.pos; omega) (by have := k.lt; omega) k.lt)
  else
    ((⟨N - 1, by omega⟩, true),
      Triangle.Vertex.mk 0 k.val (n - k.val) (by have := k.lt; omega)
        (by have := k.lt; omega) k.lt (by have := k.pos; have := k.lt; omega))

theorem edgeCopy_weight {n N} (hN : 0 < N) (j : EdgeIndex N) (k : EdgeWeight n) :
    copyWeight (edgeCopy hN j k) = edgeWeight j k := by
  have hjb := j.isLt
  unfold edgeCopy
  split_ifs with hj he
  · have heq : (j.val + 1) / 2 = j.val / 2 := by omega
    funext v
    rcases v with ⟨b, i⟩
    cases b <;> simp [copyWeight, localWeight, corner₀, corner₁, corner₂,
      edgeWeight, EdgeWeight.bc, edgeTop, edgeBottom, Fin.ext_iff, heq]
  · have heq : (j.val + 1) / 2 = j.val / 2 + 1 := by omega
    funext v
    rcases v with ⟨b, i⟩
    cases b <;> simp [copyWeight, localWeight, corner₀, corner₁, corner₂,
      edgeWeight, edgeTop, edgeBottom, Fin.ext_iff, heq]
  · have hje : j.val = 2 * N := by omega
    have hs : N - 1 + 1 = N := by omega
    funext v
    rcases v with ⟨b, i⟩
    cases b <;> simp [copyWeight, localWeight, corner₀, corner₁, corner₂,
      edgeWeight, edgeTop, edgeBottom, Fin.ext_iff, hje, hs, Nat.add_div]

/-- Every noncorner lattice point on every `e_j` survives boundary omission. -/
def edgeVertex {n N} (hN : 0 < N) (j : EdgeIndex N) (k : EdgeWeight n) : Vertex n N :=
  ⟨glue (edgeCopy hN j k).1 (edgeCopy hN j k).2, by
    change Mixed (copyWeight (edgeCopy hN j k))
    rw [edgeCopy_weight]
    exact mixed_edgeWeight j k⟩

@[simp] theorem weight_edgeVertex {n N} (hN : 0 < N) (j : EdgeIndex N)
    (k : EdgeWeight n) : weight (edgeVertex hN j k).1 = edgeWeight j k :=
  edgeCopy_weight hN j k

/-- Both the edge index and its weight are recovered from the glued vertex. -/
theorem edgeWeight_injective {n N} {j l : EdgeIndex N} {k m : EdgeWeight n}
    (h : edgeWeight j k = edgeWeight l m) : j = l ∧ k = m := by
  have hb := congrFun h (true, edgeBottom j)
  have ht := congrFun h (false, edgeTop j)
  simp only [edgeWeight_bottom, edgeWeight_top] at hb ht
  simp only [edgeWeight, Prod.mk.injEq, Bool.true_eq_false, false_and,
    ↓reduceIte, true_and, zero_add, Bool.false_eq_true, add_zero] at hb ht
  have hbi : edgeBottom j = edgeBottom l := by
    by_contra hn
    simp [hn] at hb
    have := k.pos
    omega
  have hti : edgeTop j = edgeTop l := by
    by_contra hn
    simp [hn] at ht
    have := k.lt
    omega
  have hkm : k.val = m.val := by simpa [hbi] using hb
  constructor
  · apply Fin.ext
    have h1 := congrArg Fin.val hbi
    have h2 := congrArg Fin.val hti
    simp only [edgeBottom, edgeTop] at h1 h2
    omega
  · apply Subtype.ext
    exact Fin.ext hkm

def edgeEmbedding {n N} (hN : 0 < N) (j : EdgeIndex N) : EdgeWeight n ↪ Vertex n N where
  toFun := edgeVertex hN j
  inj' := by
    intro k m h
    exact (edgeWeight_injective (by
      simpa using congrArg (fun v : Vertex n N => weight v.1) h)).2

/-- `L(e_j)`, including `j=0` and `j=2*N`. -/
def edgeSet {n N} (hN : 0 < N) (j : EdgeIndex N) : Set (Vertex n N) :=
  Set.range (edgeEmbedding hN j)

def leftEdge (N : ℕ) : EdgeIndex N := ⟨0, by omega⟩
def rightEdge (N : ℕ) : EdgeIndex N := ⟨2 * N, by omega⟩
def middleEdge (N : ℕ) : EdgeIndex N := ⟨N, by omega⟩

def protectedSet {n N} (hN : 0 < N) : Set (Vertex n N) :=
  edgeSet hN (leftEdge N) ∪ edgeSet hN (rightEdge N)
def internal {n N} (hN : 0 < N) : Set (Vertex n N) := (protectedSet hN)ᶜ
def middle {n N} (hN : 0 < N) : Set (Vertex n N) := edgeSet hN (middleEdge N)

theorem edgeSet_disjoint {n N} (hN : 0 < N) {j l : EdgeIndex N} (hjl : j ≠ l) :
    Disjoint (edgeSet (n := n) hN j) (edgeSet hN l) := by
  rw [Set.disjoint_left]
  rintro v ⟨k, rfl⟩ ⟨m, hm⟩
  have hw := congrArg (fun v : Vertex n N => weight v.1) hm
  change weight (edgeVertex hN l m).1 = weight (edgeVertex hN j k).1 at hw
  simp only [weight_edgeVertex] at hw
  exact hjl (edgeWeight_injective hw).1.symm

theorem edgeSet_subset_internal {n N} (hN : 0 < N) (j : EdgeIndex N)
    (h0 : j ≠ leftEdge N) (h2 : j ≠ rightEdge N) :
    edgeSet (n := n) hN j ⊆ internal hN := by
  intro v hv
  rintro (hl | hr)
  · exact Set.disjoint_left.mp (edgeSet_disjoint hN h0) hv hl
  · exact Set.disjoint_left.mp (edgeSet_disjoint hN h2) hv hr

theorem middle_subset_internal {n N} (hN : 0 < N) :
    middle (n := n) hN ⊆ internal hN := by
  apply edgeSet_subset_internal
  · intro h; have := congrArg Fin.val h; simp [middleEdge, leftEdge] at this; omega
  · intro h; have := congrArg Fin.val h; simp [middleEdge, rightEdge] at this; omega

/-- The middle edge is `T_{(N+1)/2} B_{N/2}` for every `N`. -/
theorem middle_endpoints (N : ℕ) :
    (edgeTop (middleEdge N)).val = (N + 1) / 2 ∧
    (edgeBottom (middleEdge N)).val = N / 2 := ⟨rfl, rfl⟩

theorem middle_endpoints_odd (r : ℕ) :
    (edgeTop (middleEdge (2 * r + 1))).val = r + 1 ∧
    (edgeBottom (middleEdge (2 * r + 1))).val = r := by
  simp only [edgeTop, edgeBottom, middleEdge]
  omega

/-- No two different faces of the same kind are glued at noncorner points. -/
theorem glue_same_side_iff {n N} (i j : Fin N) (b : Bool)
    (p q : Triangle.Vertex n) :
    glue (i, b) p = glue (j, b) q ↔ i = j ∧ p = q := by
  constructor
  · intro h
    have hw := (glue_eq_iff _ _ _ _).mp h
    have h0 := congrFun hw (corner₀ (i, b))
    have h1 := congrFun hw (corner₁ (i, b))
    have h2 := congrFun hw (corner₂ (i, b))
    simp only [localWeight_corner₀, localWeight_corner₁, localWeight_corner₂] at h0 h1 h2
    have hi : i = j := by
      by_contra hn
      have hv : i.val ≠ j.val := fun h => hn (Fin.ext h)
      have ht := p.total
      have ha := p.a_lt
      have hb := p.b_lt
      have hc := p.c_lt
      cases b <;>
        simp [localWeight, corner₀, corner₁, corner₂, Fin.ext_iff, hv] at h0 h1 h2 <;>
        split_ifs at h0 h1 <;> omega
    subst j
    exact ⟨rfl, glue_injective _ h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The complete list of identifications between opposite kinds of faces.
The first case is `e_(2*i+1)`; the second is `e_(2*i)` with `i=j+1`.
All equalities match weights at the actual named endpoints. -/
theorem glue_opposite_iff {n N} (i j : Fin N) (p q : Triangle.Vertex n) :
    glue (i, false) p = glue (j, true) q ↔
      (i = j ∧ p.b = 0 ∧ q.b = 0 ∧ p.a = q.c ∧ p.c = q.a) ∨
      (i.val = j.val + 1 ∧ p.a = 0 ∧ q.a = 0 ∧ p.b = q.c ∧ p.c = q.b) := by
  constructor
  · intro h
    have hw := (glue_eq_iff _ _ _ _).mp h
    have h0 := congrFun hw (corner₀ (i, false))
    have h1 := congrFun hw (corner₁ (i, false))
    have h2 := congrFun hw (corner₂ (i, false))
    simp only [localWeight_corner₀, localWeight_corner₁, localWeight_corner₂] at h0 h1 h2
    have hpt := p.total
    have hqt := q.total
    by_cases hij : i = j
    · subst j
      simp [localWeight, corner₀, corner₁, corner₂, Fin.ext_iff] at h0 h1 h2
      exact Or.inl ⟨rfl, h1, by omega, h0, h2⟩
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases hs : i.val = j.val + 1
      · simp [localWeight, corner₀, corner₁, corner₂, Fin.ext_iff, hs] at h0 h1 h2
        exact Or.inr ⟨hs, h0, by omega, h1, h2⟩
      · simp [localWeight, corner₀, corner₁, corner₂, Fin.ext_iff, hv, hs] at h0 h1
        have := p.c_lt
        omega
  · intro h
    apply (glue_eq_iff _ _ _ _).mpr
    rcases h with ⟨rfl, hb, hqb, ha, hc⟩ | ⟨hi, ha, hqa, hb, hc⟩
    · funext v
      rcases v with ⟨b, l⟩
      cases b <;> simp [localWeight, corner₀, corner₁, corner₂, hb, hqb, ha, hc]
    · funext v
      rcases v with ⟨b, l⟩
      cases b <;> simp [localWeight, corner₀, corner₁, corner₂,
        Fin.ext_iff, hi, ha, hqa, hb, hc]

/-- An interior lattice point belongs to just one triangle copy. -/
theorem interior_glue_eq_iff {n N} (f g : Face N) (p : Triangle.Interior n)
    (q : Triangle.Vertex n) : glue f p.1 = glue g q ↔ f = g ∧ p.1 = q := by
  rcases f with ⟨i, b⟩
  rcases g with ⟨j, d⟩
  cases b <;> cases d
  · simpa using glue_same_side_iff i j false p.1 q
  · constructor
    · intro h
      rcases (glue_opposite_iff i j p.1 q).mp h with
        ⟨_, hb, _, _, _⟩ | ⟨_, ha, _, _, _⟩
      · exact (Nat.ne_of_gt p.2.2.1 hb).elim
      · exact (Nat.ne_of_gt p.2.1 ha).elim
    · rintro ⟨h, _⟩
      have := congrArg Prod.snd h
      cases this
  · constructor
    · intro h
      rcases (glue_opposite_iff j i q p.1).mp h.symm with
        ⟨_, _, hb, _, _⟩ | ⟨_, _, ha, _, _⟩
      · exact (Nat.ne_of_gt p.2.2.1 hb).elim
      · exact (Nat.ne_of_gt p.2.1 ha).elim
    · rintro ⟨h, _⟩
      have := congrArg Prod.snd h
      cases this
  · simpa using glue_same_side_iff i j true p.1 q

/-- An interior point cannot be a transverse edge point. -/
theorem interior_ne_edge {n N} (hN : 0 < N) (f : Face N) (p : Triangle.Interior n)
    (j : EdgeIndex N) (k : EdgeWeight n) : interiorEmbedding f p ≠ edgeVertex hN j k := by
  intro h
  have he := (interior_glue_eq_iff f (edgeCopy hN j k).1 p (edgeCopy hN j k).2).mp
    (congrArg Subtype.val h)
  have hp : 0 < (edgeCopy hN j k).2.a ∧ 0 < (edgeCopy hN j k).2.b := by
    rw [← he.2]
    exact ⟨p.2.1, p.2.2.1⟩
  unfold edgeCopy at hp
  split_ifs at hp <;> simp [EdgeWeight.bc] at hp

theorem interior_mem_internal {n N} (hN : 0 < N) (f : Face N)
    (p : Triangle.Interior n) : interiorEmbedding f p ∈ internal hN := by
  rintro (⟨k, hk⟩ | ⟨k, hk⟩)
  · exact interior_ne_edge hN f p _ k hk.symm
  · exact interior_ne_edge hN f p _ k hk.symm

/-- The edge labels enumerate exactly `n-1` points. -/
def edgeWeightEquiv (n : ℕ) : EdgeWeight n ≃ Fin (n - 1) where
  toFun k := ⟨k.val - 1, by have := k.lt; have := k.pos; omega⟩
  invFun k := ⟨⟨k.val + 1, by have := k.isLt; omega⟩, by simp⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    change k.val - 1 + 1 = k.val
    have := k.pos
    omega
  right_inv k := by apply Fin.ext; simp [EdgeWeight.val]

theorem card_edgeWeight (n : ℕ) : Fintype.card (EdgeWeight n) = n - 1 := by
  rw [Fintype.card_congr (edgeWeightEquiv n), Fintype.card_fin]

theorem card_edgeSet {n N} (hN : 0 < N) (j : EdgeIndex N) :
    Nat.card (edgeSet (n := n) hN j) = n - 1 := by
  unfold edgeSet
  rw [Nat.card_congr (Equiv.ofInjective (edgeEmbedding hN j) (edgeEmbedding hN j).injective).symm]
  rw [Nat.card_eq_fintype_card, card_edgeWeight]

@[simp] theorem boundary_glue_iff {n N} (f : Face N) (p : Triangle.Vertex n) :
    Boundary (glue f p) ↔ p.c = 0 := by
  rw [boundary_iff_not_mixed, weight_glue, mixed_localWeight_iff]
  omega

/-- Equivalence with literal omission of the actual top and bottom boundary. -/
def retainedEquivOmitBoundary (n N : ℕ) :
    Vertex n N ≃ {v : Glued n N // ¬Boundary v} where
  toFun v := ⟨v.1, fun h => (boundary_iff_not_mixed v.1).mp h v.2⟩
  invFun v := ⟨v.1, by
    by_contra h
    exact v.2 ((boundary_iff_not_mixed v.1).mpr h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Boundary omission restricts the glued matrix without changing retained entries. -/
theorem matrix_omitBoundary {n N} (u v : Vertex n N) :
    matrix n N u v = gluedMatrix n N
      ((retainedEquivOmitBoundary n N) u).1
      ((retainedEquivOmitBoundary n N) v).1 := rfl

@[simp] theorem gluedEquivWeightImage_apply {n N} (u : Glued n N) :
    ((gluedEquivWeightImage n N) u).1 = weight u := rfl

/-- The signed entries can equivalently be computed with the concrete polygon
weight vectors. This is proved using injectivity of the quotient's weight map. -/
theorem matrix_concrete_entries {n N} (u v : Vertex n N) :
    matrix n N u v = ∑ f : Face N, ∑ t : Triangle.Cell n,
      Triangle.cycleEntry (localWeight f t.first) (localWeight f t.second)
        (localWeight f t.third) (weight u.1) (weight v.1) := by
  classical
  rw [matrix_eq_sum]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro t _
  simp only [← weight_glue, Triangle.cycleEntry, Triangle.cycleCount,
    weight_injective.eq_iff]

/-- The endpoints of every even and odd edge agree with Section 1. -/
theorem edge_endpoints_even {N} (i : Fin (N + 1)) :
    (edgeTop (⟨2 * i.val, by have := i.isLt; omega⟩ : EdgeIndex N)).val = i.val ∧
    (edgeBottom (⟨2 * i.val, by have := i.isLt; omega⟩ : EdgeIndex N)).val = i.val := by
  simp only [edgeTop, edgeBottom]
  omega

theorem edge_endpoints_odd {N} (i : Fin N) :
    (edgeTop (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : EdgeIndex N)).val = i.val + 1 ∧
    (edgeBottom (⟨2 * i.val + 1, by have := i.isLt; omega⟩ : EdgeIndex N)).val = i.val := by
  simp only [edgeTop, edgeBottom]
  omega

end Strip
end FgStrip
