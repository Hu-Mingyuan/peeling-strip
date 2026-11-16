import FgStrip.TwoTriangle.Embedding

namespace FgStrip.TwoTriangle
open Triangle

noncomputable def faceContribution {n N} (f : Strip.Face N) :
    Matrix (Strip.Vertex n N) (Strip.Vertex n N) ℤ :=
  fun u v => mapMatrix (Strip.glue f) u.1 v.1

namespace Pair
variable {n N : ℕ}
noncomputable def contribution (s : Pair N) :
    Matrix (Strip.Vertex n N) (Strip.Vertex n N) ℤ :=
  faceContribution s.faceX + faceContribution s.faceY
noncomputable def remainder (s : Pair N) :
    Matrix (Strip.Vertex n N) (Strip.Vertex n N) ℤ :=
  ∑ f ∈ (Finset.univ.erase s.faceX).erase s.faceY, faceContribution f

def sign : Pair N → ℤ
  | .odd _ => 1
  | .even _ _ => -1

theorem mapped_x (s : Pair N) (u v : Grid n) :
    mapMatrix s.gx (s.embed u).1 (s.embed v).1 = mapMatrix x u.1 v.1 := by
  classical
  have hu (p : Triangle.Vertex n) : (s.embed u).1 = s.gx p ↔ u.1 = x p := by
    rw [eq_comm, s.gx_eq_embed_iff, eq_comm]
  have hv (p : Triangle.Vertex n) : (s.embed v).1 = s.gx p ↔ v.1 = x p := by
    rw [eq_comm, s.gx_eq_embed_iff, eq_comm]
  simp only [mapMatrix_eq_sum, cycleEntry, cycleCount, hu, hv]

theorem mapped_y (s : Pair N) (u v : Grid n) :
    mapMatrix s.gy (s.embed u).1 (s.embed v).1 = mapMatrix y u.1 v.1 := by
  classical
  have hu (p : Triangle.Vertex n) : (s.embed u).1 = s.gy p ↔ u.1 = y p := by
    rw [eq_comm, s.gy_eq_embed_iff, eq_comm]
  have hv (p : Triangle.Vertex n) : (s.embed v).1 = s.gy p ↔ v.1 = y p := by
    rw [eq_comm, s.gy_eq_embed_iff, eq_comm]
  simp only [mapMatrix_eq_sum, cycleEntry, cycleCount, hu, hv]

theorem contribution_eq (s : Pair N) (u v : Grid n) :
    s.contribution (s.embed u) (s.embed v) = s.sign * matrix n u v := by
  classical
  have hx := s.mapped_x u v
  have hy := s.mapped_y u v
  cases s with
  | odd i =>
    change mapMatrix (Strip.glue (i,false)) _ _ + mapMatrix (Strip.glue (i,true)) _ _ =
      1 * (mapMatrix x u.1 v.1 + mapMatrix y u.1 v.1)
    change mapMatrix (Strip.glue (i,false)) _ _ = _ at hx
    change mapMatrix (Strip.glue (i,true) ∘ rot) _ _ = _ at hy
    rw [mapMatrix_rot] at hy
    rw [hx, hy, one_mul]
  | even i hi =>
    change mapMatrix (Strip.glue (i,true)) _ _ + mapMatrix (Strip.glue (⟨i.val+1,hi⟩,false)) _ _ =
      -1 * (mapMatrix x u.1 v.1 + mapMatrix y u.1 v.1)
    change mapMatrix (Strip.glue (i,true) ∘ swap) _ _ = _ at hx
    change mapMatrix ((Strip.glue (⟨i.val+1,hi⟩,false) ∘ swap) ∘ rot) _ _ = _ at hy
    rw [mapMatrix_swap] at hx
    rw [mapMatrix_rot, mapMatrix_swap] at hy
    omega

theorem strip_decomposition (s : Pair N) :
    Strip.matrix n N = s.contribution + s.remainder := by
  classical
  funext u v
  have hs : Strip.matrix n N u v = ∑ f : Strip.Face N, faceContribution f u v := by
    simp only [Strip.matrix_eq_sum, faceContribution, mapMatrix_eq_sum]
  rw [hs]
  have hxy := s.faces_ne
  have he : s.faceY ∈ Finset.univ.erase s.faceX := by simp [Ne.symm hxy]
  have h1 := Finset.sum_erase_add (Finset.univ : Finset (Strip.Face N))
    (fun f => faceContribution f u v) (Finset.mem_univ s.faceX)
  have h2 := Finset.sum_erase_add (Finset.univ.erase s.faceX)
    (fun f => faceContribution f u v) he
  simp only [contribution, remainder, Matrix.add_apply, Matrix.sum_apply]
  omega

/-- An exterior face cannot contain a lower-triangle point off R. -/
theorem gx_ne_outside (s : Pair N) (p : Triangle.Vertex n) (ha : 0 < p.a)
    (g : Strip.Face N) (hgX : g ≠ s.faceX) (hgY : g ≠ s.faceY)
    (q : Triangle.Vertex n) : s.gx p ≠ Strip.glue g q := by
  rcases g with ⟨j,b⟩
  cases s with
  | odd i =>
    cases b
    · intro he
      have hh := (Strip.glue_same_side_iff i j false p q).mp he
      exact hgX (by simp [faceX, hh.1])
    · intro he
      rcases (Strip.glue_opposite_iff i j p q).mp he with hh | hh
      · exact hgY (by simp [faceY, hh.1])
      · omega
  | even i hi =>
    cases b
    · intro he
      have hh := (Strip.glue_opposite_iff j i q (swap p)).mp he.symm
      simp only [swap, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c] at hh
      rcases hh with hh | hh
      · omega
      · exact hgY (by simp [faceY, Fin.ext_iff, hh.1])
    · intro he
      have hh := (Strip.glue_same_side_iff i j true (swap p) q).mp he
      exact hgX (by simp [faceX, hh.1])

/-- An exterior face cannot contain an upper-triangle point off L. -/
theorem gy_ne_outside (s : Pair N) (p : Triangle.Vertex n) (hb : 0 < p.b)
    (g : Strip.Face N) (hgX : g ≠ s.faceX) (hgY : g ≠ s.faceY)
    (q : Triangle.Vertex n) : s.gy p ≠ Strip.glue g q := by
  rcases g with ⟨j,b⟩
  cases s with
  | odd i =>
    cases b
    · intro he
      have hh := (Strip.glue_opposite_iff j i q (rot p)).mp he.symm
      simp only [rot, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c] at hh
      rcases hh with hh | hh
      · exact hgX (by simp [faceX, hh.1])
      · omega
    · intro he
      have hh := (Strip.glue_same_side_iff i j true (rot p) q).mp he
      exact hgY (by simp [faceY, hh.1])
  | even i hi =>
    cases b
    · intro he
      have hh := (Strip.glue_same_side_iff ⟨i.val+1,hi⟩ j false (swap (rot p)) q).mp he
      exact hgY (by simp [faceY, hh.1])
    · intro he
      have hh := (Strip.glue_opposite_iff ⟨i.val+1,hi⟩ j (swap (rot p)) q).mp he
      simp only [swap, rot, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c] at hh
      rcases hh with hh | hh
      · omega
      · exact hgX (by simp [faceX, Fin.ext_iff]; omega)

theorem embed_ne_outside (s : Pair N) (u : Grid n) (hi : 0 < u.i) (hin : u.i < n)
    (g : Strip.Face N) (hgX : g ≠ s.faceX) (hgY : g ≠ s.faceY)
    (q : Triangle.Vertex n) : (s.embed u).1 ≠ Strip.glue g q := by
  unfold embed
  split_ifs with h
  · exact s.gx_ne_outside (u.lower h) (by dsimp [Grid.lower]; omega) g hgX hgY q
  · exact s.gy_ne_outside (u.upper (by omega)) hi g hgX hgY q

theorem remainder_row_zero (s : Pair N) (u : Grid n) (hi : 0 < u.i) (hin : u.i < n)
    (v : Strip.Vertex n N) : s.remainder (s.embed u) v = 0 := by
  classical
  simp only [remainder, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro g hg
  have hg' := Finset.mem_erase.mp hg
  have hg'' := Finset.mem_erase.mp hg'.2
  have hn := s.embed_ne_outside u hi hin g hg''.1 hg'.1
  simp only [faceContribution, mapMatrix_eq_sum]
  apply Finset.sum_eq_zero
  intro t _
  simp [cycleEntry, cycleCount, hn t.first, hn t.second, hn t.third]

theorem contribution_skew (s : Pair N) (u v : Strip.Vertex n N) :
    s.contribution u v = -s.contribution v u := by
  change mapMatrix _ _ _ + mapMatrix _ _ _ = -(mapMatrix _ _ _ + mapMatrix _ _ _)
  rw [mapMatrix_skew (Strip.glue s.faceX), mapMatrix_skew (Strip.glue s.faceY)]; ring

theorem remainder_skew (s : Pair N) (u v : Strip.Vertex n N) :
    s.remainder u v = -s.remainder v u := by
  have h := congrFun (congrFun (s.strip_decomposition (n := n)) u) v
  have h' := congrFun (congrFun (s.strip_decomposition (n := n)) v) u
  have hs := Strip.matrix_skew u v
  have hc := s.contribution_skew u v
  simp only [Matrix.add_apply] at h h'
  omega
end Pair
end FgStrip.TwoTriangle
