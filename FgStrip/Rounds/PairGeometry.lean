import FgStrip.Rounds.PairMatrix
import FgStrip.Rounds.Invariant

namespace FgStrip.Rounds
open TriangleShell TwoTriangle CommonEdge

theorem pair_tx_interior {n N} (s : Pair N) (x : Triangle.Interior n) :
    0 < (s.tx x.val).a ∧ 0 < (s.tx x.val).b ∧ 0 < (s.tx x.val).c := by
  have hx := x.property
  cases s <;> simpa [Pair.tx, swap, and_comm, and_left_comm] using hx

theorem pair_ty_interior {n N} (s : Pair N) (x : Triangle.Interior n) :
    0 < (s.ty x.val).a ∧ 0 < (s.ty x.val).b ∧ 0 < (s.ty x.val).c := by
  have hx := x.property
  cases s <;> simpa [Pair.ty, rot, swap, and_comm, and_left_comm, and_assoc] using hx

theorem pair_lower_interior {n N} (s : Pair N) (u : Grid n)
    (hj : u.j < u.i) (hi : u.i < n) :
    ∃ x : Triangle.Interior n, s.embed u=Strip.interiorEmbedding s.faceX x ∧
      ∀ p, x.val ∈ cornerSet p ↔ CX p u.val := by
  let x : Triangle.Interior n := ⟨u.lower (by omega), by
    have := u.j_pos
    dsimp [Grid.lower]
    omega⟩
  refine ⟨⟨s.tx x.val,pair_tx_interior s x⟩,?_,?_⟩
  · apply Subtype.ext
    exact ((s.gx_eq_embed_iff x.val u).mpr (u.x_lower (by omega))).symm
  · intro p
    change BarycentricC p (s.tx x.val) ↔ CX p u.val
    rw [s.CX_face, u.x_lower]

theorem pair_upper_interior {n N} (s : Pair N) (u : Grid n)
    (hi : 0 < u.i) (hj : u.i < u.j) :
    ∃ x : Triangle.Interior n, s.embed u=Strip.interiorEmbedding s.faceY x ∧
      ∀ p, x.val ∈ cornerSet p ↔ CY p u.val := by
  let x : Triangle.Interior n := ⟨u.upper (by omega), by
    have := u.j_lt
    dsimp [Grid.upper]
    omega⟩
  refine ⟨⟨s.ty x.val,pair_ty_interior s x⟩,?_,?_⟩
  · apply Subtype.ext
    exact ((s.gy_eq_embed_iff x.val u).mpr (u.y_upper (by omega))).symm
  · intro p
    change BarycentricC p (s.ty x.val) ↔ CY p u.val
    rw [s.CY_face, u.y_upper]

/-- The permitted two-triangle support contains no protected end-edge vertex. -/
theorem pair_support_internal {n N} (hN : 0 < N) (s : Pair N) :
    s.embed '' support n ⊆ Strip.internal hN := by
  rintro y ⟨u,hu,rfl⟩
  by_cases hd : u.i=u.j
  · let k : Triangle.EdgeWeight n := ⟨⟨u.j,u.j_lt⟩,u.j_pos⟩
    have he : u=D k := Grid.ext hd rfl
    rw [he,s.embed_D_edge hN]
    apply Strip.edgeSet_subset_internal hN s.commonEdge
    · cases s <;> simp only [Pair.commonEdge, Strip.leftEdge, ne_eq, Fin.mk.injEq] <;> omega
    · cases s with
      | odd i => have := i.isLt; simp only [Pair.commonEdge, Strip.rightEdge, ne_eq, Fin.mk.injEq]; omega
      | even i hi => simp only [Pair.commonEdge, Strip.rightEdge, ne_eq, Fin.mk.injEq]; omega
    · exact ⟨s.stripWeight k,rfl⟩
  · by_cases hl : u.j < u.i
    · obtain ⟨x,hx,_⟩ := pair_lower_interior s u hl hu.2
      rw [hx]
      exact Strip.interior_mem_internal hN _ x
    · obtain ⟨x,hx,_⟩ := pair_upper_interior s u hu.1 (by omega)
      rw [hx]
      exact Strip.interior_mem_internal hN _ x

theorem stripWeight_live {n N} (s : Pair N) (p : ℕ) (k : Triangle.EdgeWeight n) :
    (p < (s.stripWeight k).val ∧ (s.stripWeight k).val < n-p) ↔
      (p < k.val ∧ k.val < n-p) := by
  have h := not_congr (s.depth_stripWeight p k)
  simpa only [EdgeDepth,not_or,Nat.not_le] using h

theorem profile_pair_D {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (s : Pair N) (k : Triangle.EdgeWeight n) :
    s.embed (D k) ∈ profileLive hN d c ↔ d s.commonEdge < k.val ∧ k.val < n-d s.commonEdge := by
  rw [s.embed_D_edge hN,profileLive_edge,stripWeight_live]

theorem profile_pair_L {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (s : Pair N) (k : Triangle.EdgeWeight n) :
    s.embed (L k) ∈ profileLive hN d c ↔ d s.lastEdge < k.val ∧ k.val < n-d s.lastEdge := by
  rw [s.embed_L_edge hN,profileLive_edge,stripWeight_live]

theorem profile_pair_R {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (s : Pair N) (k : Triangle.EdgeWeight n) :
    s.embed (R k) ∈ profileLive hN d c ↔ d s.firstEdge < k.val ∧ k.val < n-d s.firstEdge := by
  rw [s.embed_R_edge hN,profileLive_edge,stripWeight_live]

theorem profile_pair_X {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (s : Pair N) (u : Grid n) (hj : u.j<u.i) (hi : u.i<n) :
    s.embed u ∈ profileLive hN d c ↔ ¬CX (c s.faceX) u.val := by
  obtain ⟨x,hx,hc⟩ := pair_lower_interior s u hj hi
  rw [hx,profileLive_interior,hc]

theorem profile_pair_Y {n N} (hN : 0 < N) (d : Strip.EdgeIndex N → ℕ)
    (c : Strip.Face N → ℕ) (s : Pair N) (u : Grid n) (hi : 0<u.i) (hj : u.i<u.j) :
    s.embed u ∈ profileLive hN d c ↔ ¬CY (c s.faceY) u.val := by
  obtain ⟨x,hx,hc⟩ := pair_upper_interior s u hi hj
  rw [hx,profileLive_interior,hc]

/-- Exactly the extra interface deletions present at the selected pair. -/
def pairExtra {n N} (d : Strip.EdgeIndex N → ℕ) (s : Pair N) : Set (Grid n) :=
  {u | (u.i=0 ∧ EdgeDepth n (d s.lastEdge) u.j) ∨
    (u.i=n ∧ EdgeDepth n (d s.firstEdge) u.j)}

theorem pairExtra_interface {n N} (d : Strip.EdgeIndex N → ℕ) (s : Pair N) :
    ∀ u ∈ pairExtra (n := n) d s, u.i=0 ∨ u.i=n := by
  intro u hu
  exact hu.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- A depth profile gives exactly the local common-edge live set with arbitrary
further interface deletions. -/
theorem profile_pair_preimage {n N p} (hN : 0 < N)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (s : Pair N)
    (hd : d s.commonEdge=p) (hl : p ≤ d s.firstEdge) (hr : p ≤ d s.lastEdge)
    (hx : c s.faceX=p+1) (hy : c s.faceY=p+1) :
    s.embed ⁻¹' profileLive (n := n) hN d c=live p \ pairExtra d s := by
  ext u
  change s.embed u ∈ profileLive hN d c ↔ _
  rcases label_cases u with ⟨k,rfl⟩ | ⟨k,rfl⟩ | ⟨k,rfl⟩ |
    ⟨i,j,hj,hji,hi,rfl⟩ | ⟨i,j,hi,hij,hj,rfl⟩
  · rw [profile_pair_L]
    have := k.pos; have := k.lt
    simp only [Set.mem_sdiff,live,pairExtra,Set.mem_setOf_eq,deletedEdge,EdgeDepth,
      CX,CY,Grid.i,Grid.j,L]
    simp only [true_or, or_true, true_and, false_and, and_false, not_false_eq_true, and_true, Nat.lt_irrefl, Nat.not_lt_zero]
    omega
  · rw [profile_pair_R]
    have := k.pos; have := k.lt
    simp only [Set.mem_sdiff,live,pairExtra,Set.mem_setOf_eq,deletedEdge,EdgeDepth,
      CX,CY,Grid.i,Grid.j,R]
    simp only [true_or, or_true, true_and, false_and, and_false, not_false_eq_true, and_true, Nat.lt_irrefl, Nat.not_lt_zero]
    omega
  · rw [profile_pair_D,hd]
    have := k.pos; have := k.lt
    simp only [Set.mem_sdiff,live,pairExtra,Set.mem_setOf_eq,deletedEdge,EdgeDepth,
      CX,CY,Grid.i,Grid.j,D]
    simp only [true_or, or_true, true_and, false_and, and_false, not_false_eq_true, and_true, Nat.lt_irrefl, Nat.not_lt_zero]
    omega
  · rw [profile_pair_X hN d c s (X i j hj hji hi) hji hi,hx]
    simp only [Set.mem_sdiff,live,pairExtra,Set.mem_setOf_eq,deletedEdge,EdgeDepth,
      CX,CY,Grid.i,Grid.j,X]
    omega
  · rw [profile_pair_Y hN d c s (Y i j hi hij hj) hi hij,hy]
    simp only [Set.mem_sdiff,live,pairExtra,Set.mem_setOf_eq,deletedEdge,EdgeDepth,
      CX,CY,Grid.i,Grid.j,Y]
    omega

/-- Common-edge moves specialized to a proved profile, supported in the strip
interior and checked against every currently live strip column. -/
theorem pair_profile_sequence {n N p} (hN : 0 < N) (hp : p<n/2)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (s : Pair N)
    (hd : d s.commonEdge=p) (hl : p ≤ d s.firstEdge) (hr : p ≤ d s.lastEdge)
    (hx : c s.faceX=p+1) (hy : c s.faceY=p+1) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (profileLive hN d c)
      (profileLive hN d c \ s.embed '' endpoints p) := by
  classical
  exact sequence_support_mono
    (pair_sequence_on_live s hp (pairExtra d s) (pairExtra_interface d s) _
      (profile_pair_preimage hN d c s hd hl hr hx hy))
    (pair_support_internal hN s)

end FgStrip.Rounds
