import FgStrip.Strip
import FgStrip.Mutation

/-! Finite oriented triangles, glued by endpoint weights, with marked boundary
sides omitted. The strip faces have exactly the orders in `Strip.Face`. -/
namespace FgStrip.AmbientTriangulation
open Triangle

/-- Extra polygon vertices and extra oriented faces are independent finite sets. -/
structure Data (N : ℕ) (X O : Type*) where
  outside₀ : O → Strip.Polygon N ⊕ X
  outside₁ : O → Strip.Polygon N ⊕ X
  outside₂ : O → Strip.Polygon N ⊕ X
  distinct₀₁ : ∀ o, outside₀ o ≠ outside₁ o
  distinct₀₂ : ∀ o, outside₀ o ≠ outside₂ o
  distinct₁₂ : ∀ o, outside₁ o ≠ outside₂ o
  /-- Side `k` is opposite corner `k`; precisely its zero coordinate is omitted. -/
  boundarySides : Strip.Face N ⊕ O → Finset (Fin 3)

variable {n N : ℕ} {X O : Type*}

/-- Extend polygon weights by zero at the extra polygon vertices. -/
def extendWeight (w : Strip.Polygon N → ℕ) : Strip.Polygon N ⊕ X → ℕ :=
  Sum.elim w (fun _ => 0)

theorem extendWeight_injective :
    Function.Injective (extendWeight (N := N) (X := X)) := by
  intro u v h
  funext x
  exact congrFun h (Sum.inl x)

@[simp] theorem extendWeight_eq_iff (u v : Strip.Polygon N → ℕ) :
    extendWeight (X := X) u = extendWeight v ↔ u = v :=
  extendWeight_injective.eq_iff

def coordinate (p : Triangle.Vertex n) (k : Fin 3) : ℕ :=
  ![p.a, p.b, p.c] k

namespace Data
variable (d : Data N X O)

def corner₀ : Strip.Face N ⊕ O → Strip.Polygon N ⊕ X :=
  Sum.elim (fun f => Sum.inl (Strip.corner₀ f)) d.outside₀
def corner₁ : Strip.Face N ⊕ O → Strip.Polygon N ⊕ X :=
  Sum.elim (fun f => Sum.inl (Strip.corner₁ f)) d.outside₁
def corner₂ : Strip.Face N ⊕ O → Strip.Polygon N ⊕ X :=
  Sum.elim (fun f => Sum.inl (Strip.corner₂ f)) d.outside₂

noncomputable def localWeight (f : Strip.Face N ⊕ O) (p : Triangle.Vertex n)
    (v : Strip.Polygon N ⊕ X) : ℕ := by
  classical
  exact (if v = d.corner₀ f then p.a else 0) +
    (if v = d.corner₁ f then p.b else 0) + (if v = d.corner₂ f then p.c else 0)

@[simp] theorem localWeight_strip (f : Strip.Face N) (p : Triangle.Vertex n) :
    d.localWeight (Sum.inl f) p = extendWeight (Strip.localWeight f p) := by
  classical
  funext v
  cases v <;> simp [localWeight, corner₀, corner₁, corner₂, extendWeight, Strip.localWeight]

theorem localWeight_injective (f : Strip.Face N ⊕ O) :
    Function.Injective (d.localWeight (n := n) f) := by
  classical
  cases f with
  | inl f =>
    intro p q h
    simp only [localWeight_strip, extendWeight_eq_iff] at h
    exact Strip.localWeight_injective f h
  | inr o =>
    intro p q h
    apply Triangle.Vertex.ext
    · have := congrFun h (d.outside₀ o)
      simpa [localWeight, corner₀, corner₁, corner₂, d.distinct₀₁, d.distinct₀₂] using this
    · have := congrFun h (d.outside₁ o)
      simpa [localWeight, corner₀, corner₁, corner₂, Ne.symm (d.distinct₀₁ o),
        d.distinct₁₂] using this
    · have := congrFun h (d.outside₂ o)
      simpa [localWeight, corner₀, corner₁, corner₂, Ne.symm (d.distinct₀₂ o),
        Ne.symm (d.distinct₁₂ o)] using this

/-- Finite image representation of the glued lattice points. Equality is
exactly equality of weights at all named polygon vertices. -/
def Glued (n : ℕ) := Set.range (fun r : (Strip.Face N ⊕ O) × Triangle.Vertex n =>
  d.localWeight r.1 r.2)

noncomputable instance [Fintype O] : Fintype (d.Glued n) := by
  classical
  unfold Glued
  exact Fintype.ofFinite _

noncomputable def glue (f : Strip.Face N ⊕ O) (p : Triangle.Vertex n) : d.Glued n :=
  ⟨d.localWeight f p, ⟨(f,p), rfl⟩⟩

@[simp] theorem glue_eq_iff (f g : Strip.Face N ⊕ O) (p q : Triangle.Vertex n) :
    d.glue f p = d.glue g q ↔ d.localWeight f p = d.localWeight g q :=
  Subtype.ext_iff

/-- All and only the strip's equal-endpoint-weight identifications survive. -/
theorem strip_glue_eq_iff (f g : Strip.Face N) (p q : Triangle.Vertex n) :
    d.glue (Sum.inl f) p = d.glue (Sum.inl g) q ↔ Strip.glue f p = Strip.glue g q := by
  rw [d.glue_eq_iff, d.localWeight_strip, d.localWeight_strip,
    extendWeight_eq_iff, Strip.glue_eq_iff]

/-- Literal quotient by equal endpoint weights, equivalent to the finite image. -/
noncomputable def quotientEquiv (n : ℕ) :
    Quotient (Setoid.ker (fun r : (Strip.Face N ⊕ O) × Triangle.Vertex n =>
      d.localWeight r.1 r.2)) ≃ d.Glued n := Setoid.quotientKerEquivRange _

/-- Omit all points represented on any designated actual boundary segment. -/
def Omitted (w : Strip.Polygon N ⊕ X → ℕ) : Prop :=
  ∃ (f : Strip.Face N ⊕ O) (p : Triangle.Vertex n),
    (∃ k ∈ d.boundarySides f, coordinate p k = 0) ∧ d.localWeight f p = w

def Vertex (n : ℕ) := {v : d.Glued n // ¬d.Omitted (n := n) v.1}
noncomputable instance [Fintype O] : Fintype (d.Vertex n) := by
  classical
  unfold Vertex
  infer_instance
noncomputable instance : DecidableEq (d.Vertex n) := Classical.decEq _

/-- Each face maps its retained local points injectively into the glued lattice. -/
noncomputable def retainedFaceEmbedding (f : Strip.Face N ⊕ O) :
    {p : Triangle.Vertex n // ¬d.Omitted (n := n) (d.localWeight f p)} ↪ d.Vertex n where
  toFun p := ⟨d.glue f p.1, p.2⟩
  inj' := by
    intro p q h
    exact Subtype.ext (d.localWeight_injective f
      (congrArg (fun v : d.Vertex n => v.1.1) h))

/-- Geometric boundary compatibility: exactly the actual top/bottom segments
are omitted from every displayed strip face. No matrix condition occurs here. -/
def BoundaryCompatible (n : ℕ) : Prop :=
  ∀ (f : Strip.Face N) (p : Triangle.Vertex n),
    d.Omitted (n := n) (extendWeight (Strip.localWeight f p)) ↔ p.c = 0

/-- Outside faces meet strip lattice points only on omitted segments or on the
two protected transverse edges, with equal weights at their named endpoints. -/
def FaceIncidence (n : ℕ) : Prop :=
  ∀ (o : O) (p : Triangle.Vertex n) (f : Strip.Face N) (q : Triangle.Vertex n),
    d.localWeight (Sum.inr o) p = extendWeight (Strip.localWeight f q) →
      q.c = 0 ∨ ∃ (j : Strip.EdgeIndex N) (k : EdgeWeight n),
        (j = Strip.leftEdge N ∨ j = Strip.rightEdge N) ∧
        Strip.localWeight f q = Strip.edgeWeight j k

/-- The given strip gluing, before any omission, maps into the ambient gluing. -/
noncomputable def stripGlued (v : Strip.Glued n N) : d.Glued n :=
  ⟨extendWeight (Strip.weight v), by
    induction v using Quotient.inductionOn with
    | h r => exact ⟨(Sum.inl r.1, r.2), d.localWeight_strip r.1 r.2⟩⟩

theorem stripGlued_injective : Function.Injective (d.stripGlued (n := n)) := by
  intro u v h
  exact Strip.weight_injective (extendWeight_injective (congrArg Subtype.val h))

@[simp] theorem stripGlued_glue (f : Strip.Face N) (p : Triangle.Vertex n) :
    d.stripGlued (Strip.glue f p) = d.glue (Sum.inl f) p := by
  apply Subtype.ext
  exact (d.localWeight_strip f p).symm

theorem omitted_stripGlued_iff (hb : d.BoundaryCompatible n) (v : Strip.Glued n N) :
    d.Omitted (n := n) (d.stripGlued v).1 ↔ Strip.Boundary v := by
  induction v using Quotient.inductionOn with
  | h r => exact (hb r.1 r.2).trans (Strip.boundary_glue_iff r.1 r.2).symm

/-- No distinct retained strip vertices are identified in the ambient lattice. -/
noncomputable def embedding (hb : d.BoundaryCompatible n) : Strip.Vertex n N ↪ d.Vertex n where
  toFun x := ⟨d.stripGlued x.1, by
    intro h
    exact (Strip.boundary_iff_not_mixed x.1).mp
      ((d.omitted_stripGlued_iff hb x.1).mp h) x.2⟩
  inj' := by
    intro x y h
    exact Subtype.ext (d.stripGlued_injective (congrArg Subtype.val h))

@[simp] theorem embedding_weight (hb : d.BoundaryCompatible n) (x : Strip.Vertex n N) :
    (d.embedding hb x).1.1 = extendWeight (Strip.weight x.1) := rfl

@[simp] theorem embedding_face (hb : d.BoundaryCompatible n) (f : Strip.Face N)
    (p : {p : Triangle.Vertex n // 0 < p.c}) :
    (d.embedding hb (Strip.faceEmbedding f p)).1 = d.glue (Sum.inl f) p.1 :=
  d.stripGlued_glue f p.1

@[simp] theorem embedding_edge_weight (hb : d.BoundaryCompatible n) (hN : 0 < N)
    (j : Strip.EdgeIndex N) (k : EdgeWeight n) :
    (d.embedding hb (Strip.edgeEmbedding hN j k)).1.1 =
      extendWeight (Strip.edgeWeight j k) := by
  change extendWeight (Strip.weight (Strip.edgeVertex hN j k).1) = _
  rw [Strip.weight_edgeVertex]

/-- A retained ambient point on a strip face comes from the retained strip. -/
theorem mem_range_of_strip_weight (hb : d.BoundaryCompatible n)
    (u : d.Vertex n) (f : Strip.Face N) (p : Triangle.Vertex n)
    (h : u.1.1 = extendWeight (Strip.localWeight f p)) :
    u ∈ Set.range (d.embedding hb) := by
  have hp : 0 < p.c := by
    by_contra hn
    have hc : p.c = 0 := by omega
    exact u.2 (h ▸ (hb f p).mpr hc)
  refine ⟨Strip.faceEmbedding f ⟨p,hp⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact h.symm

/-- Incidence, before counting arrows: an outside face contains no retained
internal strip point. The outside point itself need not be retained. -/
theorem outside_ne_internal (hb : d.BoundaryCompatible n) (hi : d.FaceIncidence n)
    (hN : 0 < N) (x : Strip.Vertex n N) (hx : x ∈ Strip.internal hN)
    (o : O) (p : Triangle.Vertex n) :
    (d.embedding hb x).1.1 ≠ d.localWeight (Sum.inr o) p := by
  intro h
  obtain ⟨⟨f,q⟩, heq⟩ := (Strip.gluedEquivWeightImage n N x.1).2
  change Strip.localWeight f q = Strip.weight x.1 at heq
  have hc : 0 < q.c := (Strip.mixed_localWeight_iff f q).mp (heq ▸ x.2)
  have hw : d.localWeight (Sum.inr o) p = extendWeight (Strip.localWeight f q) := by
    rw [heq]; exact h.symm
  rcases hi o p f q hw with hz | ⟨j,k,hj,hk⟩
  · omega
  · have hxk : x = Strip.edgeVertex hN j k := by
      apply Subtype.ext
      apply Strip.weight_injective
      rw [Strip.weight_edgeVertex, ← heq, hk]
    rcases hj with rfl | rfl
    · exact hx (Or.inl ⟨k, hxk.symm⟩)
    · exact hx (Or.inr ⟨k, hxk.symm⟩)

end Data
end FgStrip.AmbientTriangulation
