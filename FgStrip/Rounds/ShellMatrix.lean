import FgStrip.Rounds.Transport

namespace FgStrip.Rounds
open TriangleShell AmbientTriangulation

/-- Retained local triangle labels; the actual boundary side is absent. -/
abbrev Retained (n : ℕ) := {x : Triangle.Vertex n // 0 < x.c}

noncomputable def retainedMatrix (n : ℕ) : Matrix (Retained n) (Retained n) ℤ :=
  restrictMatrix (Triangle.matrix n) Subtype.val

def retainedSupport (n : ℕ) : Set (Retained n) := Subtype.val ⁻¹' interiorSet n

def retainedLive {n} (p : ℕ) : Set (Retained n) := Subtype.val ⁻¹' baseLive p

def retainedFinish {n} (p : ℕ) : Set (Retained n) :=
  Subtype.val ⁻¹' (baseLive p \ cornerSet (p+1))

theorem retainedMatrix_skew (n : ℕ) : SkewSymmetric (retainedMatrix n) :=
  (show SkewSymmetric (Triangle.matrix n) from fun x y => Triangle.mapMatrix_skew id x y).restrictMatrix Subtype.val

/-- The retained face contribution agrees with the local matrix at every entry. -/
theorem face_contribution_apply {n N} (f : Strip.Face N) (x y : Retained n) :
    TwoTriangle.faceContribution f (Strip.faceEmbedding f x) (Strip.faceEmbedding f y) =
      retainedMatrix n x y := by
  classical
  change Triangle.mapMatrix (Strip.glue f) (Strip.glue f x.val) (Strip.glue f y.val) =
    Triangle.mapMatrix id x.val y.val
  simp only [Triangle.mapMatrix_eq_sum, Triangle.cycleEntry, Triangle.cycleCount,
    (Strip.glue_injective f).eq_iff, id_eq]

theorem face_contribution_row_zero {n N} (f : Strip.Face N) (u v : Strip.Vertex n N)
    (hu : u ∉ Set.range (Strip.faceEmbedding (n := n) f)) :
    TwoTriangle.faceContribution f u v=0 := by
  classical
  have hx : ∀ p : Triangle.Vertex n, u.val ≠ Strip.glue f p := by
    intro p hp
    have hm : Strip.Mixed (Strip.weight (Strip.glue f p)) := by
      rw [← hp]
      exact u.property
    have hc : 0 < p.c := (Strip.mixed_localWeight_iff f p).mp hm
    exact hu ⟨⟨p,hc⟩,Subtype.ext hp.symm⟩
  simp [TwoTriangle.faceContribution, Triangle.mapMatrix_eq_sum,
    Triangle.cycleEntry, Triangle.cycleCount, hx]

/-- The complete retained face contribution, with zero columns outside the face. -/
theorem face_contribution_extension {n N} (f : Strip.Face N) :
    TwoTriangle.faceContribution (n := n) f =
      zeroExtension (Strip.faceEmbedding f) (retainedMatrix n) := by
  classical
  funext u v
  by_cases hu : u ∈ Set.range (Strip.faceEmbedding (n := n) f)
  · obtain ⟨x,rfl⟩ := hu
    by_cases hv : v ∈ Set.range (Strip.faceEmbedding (n := n) f)
    · obtain ⟨y,rfl⟩ := hv
      rw [zeroExtension_apply,face_contribution_apply]
    · rw [zeroExtension_col_zero _ _ _ _ hv]
      change Triangle.mapMatrix (Strip.glue f) _ _=0
      rw [Triangle.mapMatrix_skew]
      change -TwoTriangle.faceContribution f v (Strip.faceEmbedding f x)=0
      rw [face_contribution_row_zero f _ _ hv,neg_zero]
  · rw [zeroExtension_row_zero _ _ _ _ hu,face_contribution_row_zero f _ _ hu]

/-- At every interior point, the selected face supplies the entire strip row. -/
theorem face_supported_rows {n N} (f : Strip.Face N) (x : Retained n)
    (hx : x ∈ retainedSupport n) (y : Strip.Vertex n N) :
    Strip.matrix n N (Strip.faceEmbedding f x) y =
      zeroExtension (Strip.faceEmbedding f) (retainedMatrix n) (Strip.faceEmbedding f x) y := by
  classical
  rw [← face_contribution_extension,Strip.matrix_eq_sum]
  change (∑ g : Strip.Face N, ∑ t : Triangle.Cell n,
    Triangle.cycleEntry (Strip.glue g t.first) (Strip.glue g t.second)
      (Strip.glue g t.third) (Strip.glue f x.val) y.val) = _
  rw [TwoTriangle.faceContribution,Triangle.mapMatrix_eq_sum]
  apply Finset.sum_eq_single f
  · intro g _ hgf
    apply Finset.sum_eq_zero
    intro t _
    have hne (p : Triangle.Vertex n) : Strip.glue f x.val ≠ Strip.glue g p := by
      intro he
      have hh := (Strip.interior_glue_eq_iff f g ⟨x.val,hx⟩ p).mp he
      exact hgf hh.1.symm
    exact cycleEntry_row_zero _ _ _ _ _ (hne _) (hne _) (hne _)
  · intro hf
    exact (hf (Finset.mem_univ f)).elim

/-- The concrete triangle-shell sequence with the omitted boundary removed from
its coordinate type. -/
theorem retained_shell_sequence {n p} (hp : 1 ≤ p) (hn : 2*p+1 ≤ n) :
    Sequence (retainedMatrix n) (retainedSupport n) (retainedLive p) (retainedFinish p) := by
  classical
  exact sequence_pull (shell_deletion hp hn)
    ⟨Subtype.val,Subtype.val_injective⟩ (fun x hx => ⟨⟨x,hx.1⟩,rfl⟩)

/-- The actual shell moves in any strip face on the exact current live set. -/
theorem shell_sequence_on_live {n N p} (f : Strip.Face N)
    (hp : 1 ≤ p) (hn : 2*p+1 ≤ n)
    (U : Set (Strip.Vertex n N))
    (hU : Strip.faceEmbedding f ⁻¹' U=retainedLive p) :
    Sequence (Strip.matrix n N) (Strip.faceEmbedding f '' retainedSupport n) U
      (U \ Strip.faceEmbedding f '' (retainedLive p \ retainedFinish p)) := by
  classical
  exact sequence_of_rows (retained_shell_sequence hp hn) (retainedMatrix_skew n)
    (Strip.faceEmbedding f) (Strip.matrix n N) Strip.matrix_skew (face_supported_rows f) U hU

/-- Shell pivots and deletions are internal to the strip for every face. -/
theorem shell_support_internal {n N} (hN : 0 < N) (f : Strip.Face N) :
    Strip.faceEmbedding f '' retainedSupport n ⊆ Strip.internal hN := by
  rintro y ⟨x,hx,rfl⟩
  exact Strip.interior_mem_internal hN f ⟨x.val,hx⟩

end FgStrip.Rounds
