import FgStrip.AmbientTriangulation.Matrix

namespace FgStrip.AmbientTriangulation
open Triangle

/-- The strip with its two end interfaces retained and no outside faces. -/
def stripOnly (N : ℕ) : Data N Empty Empty where
  outside₀ := Empty.elim
  outside₁ := Empty.elim
  outside₂ := Empty.elim
  distinct₀₁ := fun o => o.elim
  distinct₀₂ := fun o => o.elim
  distinct₁₂ := fun o => o.elim
  boundarySides := Sum.elim (fun _ => {2}) Empty.elim

theorem stripOnly_boundaryCompatible (n N : ℕ) : (stripOnly N).BoundaryCompatible n := by
  intro f p
  constructor
  · rintro ⟨g,q,⟨k,hk,hq⟩,heq⟩
    cases g with
    | inr o => exact o.elim
    | inl g =>
      have hk2 : k = 2 := by simpa [stripOnly] using hk
      subst k
      have hqc : q.c = 0 := hq
      simp only [Data.localWeight_strip, extendWeight_eq_iff] at heq
      have hm := congrArg Strip.Mixed heq
      simp only [Strip.mixed_localWeight_iff] at hm
      simp [hqc] at hm
      omega
  · intro hp
    exact ⟨Sum.inl f, p, ⟨2, by simp [stripOnly], hp⟩,
      (stripOnly N).localWeight_strip f p⟩

theorem stripOnly_faceIncidence (n N : ℕ) : (stripOnly N).FaceIncidence n := by
  intro o
  exact o.elim

@[simp] theorem stripOnly_exterior (n N : ℕ) : (stripOnly N).exterior n = 0 := by
  classical
  funext u v
  simp [Data.exterior]

/-- The example supplies all hypotheses uniformly, with no parity restriction. -/
theorem stripOnly_matrix (n N : ℕ) :
    (stripOnly N).matrix n =
      zeroExtension ((stripOnly N).embedding (stripOnly_boundaryCompatible n N))
        (Strip.matrix n N) := by
  rw [(stripOnly N).matrix_split,
    (stripOnly N).stripContribution_eq_zeroExtension (stripOnly_boundaryCompatible n N),
    stripOnly_exterior, add_zero]

/-- With no exterior faces, every retained ambient point is a strip point. -/
theorem stripOnly_embedding_surjective (n N : ℕ) :
    Function.Surjective ((stripOnly N).embedding (stripOnly_boundaryCompatible n N)) := by
  intro u
  obtain ⟨⟨f,p⟩,hp⟩ := u.1.2
  cases f with
  | inr o => exact o.elim
  | inl f =>
    apply (stripOnly N).mem_range_of_strip_weight (stripOnly_boundaryCompatible n N) u f p
    exact hp.symm.trans ((stripOnly N).localWeight_strip f p)

/-- In the permitted ranks and lengths the example has an actual retained point. -/
theorem stripOnly_nonempty {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) :
    Nonempty ((stripOnly N).Vertex n) := by
  let k : EdgeWeight n := ⟨⟨1, by omega⟩, by change 0 < (1 : ℕ); decide⟩
  exact ⟨(stripOnly N).embedding (stripOnly_boundaryCompatible n N)
    (Strip.edgeVertex hN (Strip.middleEdge N) k)⟩

/-- There is also an internal point: the example does not satisfy incidence only
because the internal strip is empty. -/
theorem stripOnly_internal_nonempty {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) :
    ∃ x : Strip.Vertex n N, x ∈ Strip.internal hN := by
  let k : EdgeWeight n := ⟨⟨1, by omega⟩, by change 0 < (1 : ℕ); decide⟩
  exact ⟨Strip.edgeVertex hN (Strip.middleEdge N) k,
    Strip.middle_subset_internal hN ⟨k,rfl⟩⟩

end FgStrip.AmbientTriangulation
