import FgStrip.Rounds.ShellMatrix
import FgStrip.Rounds.Invariant

namespace FgStrip.Rounds
open TriangleShell TwoTriangle

/-- Side `a=0`, whose strip index depends on the orientation of the face. -/
def faceEdgeA {N} (f : Strip.Face N) : Strip.EdgeIndex N :=
  ⟨2*f.1.val + if f.2 then 2 else 0, by have := f.1.isLt; cases f.2 <;> simp <;> omega⟩

/-- Side `b=0` is the diagonal of the corresponding square. -/
def faceEdgeB {N} (f : Strip.Face N) : Strip.EdgeIndex N :=
  ⟨2*f.1.val+1, by have := f.1.isLt; omega⟩

def faceWeight {n N} (f : Strip.Face N) (k : Triangle.EdgeWeight n) : Triangle.EdgeWeight n :=
  if f.2 then reverseWeight k else k

theorem faceWeight_live {n N} (f : Strip.Face N) (p : ℕ) (k : Triangle.EdgeWeight n) :
    (p < (faceWeight f k).val ∧ (faceWeight f k).val < n-p) ↔
      (p < k.val ∧ k.val < n-p) := by
  have h := not_congr (edgeDepth_reverse p k)
  rcases f with ⟨i,b⟩
  cases b
  · rfl
  · simpa only [faceWeight, ↓reduceIte, EdgeDepth, not_or, Nat.not_le] using h

theorem faceEmbedding_a {n N} (hN : 0 < N) (f : Strip.Face N)
    (x : Retained n) (ha : x.val.a=0) :
    Strip.faceEmbedding f x = Strip.edgeEmbedding hN (faceEdgeA f)
      (faceWeight f ⟨⟨x.val.c,x.val.c_lt⟩,x.property⟩) := by
  have hb : x.val.b=n-x.val.c := by have := x.val.total; omega
  have hc : n-(n-x.val.c)=x.val.c := by have := x.val.c_lt; omega
  apply Subtype.ext
  apply Strip.weight_injective
  change Strip.weight (Strip.glue f x.val) = Strip.weight (Strip.edgeVertex hN _ _).val
  rw [Strip.weight_edgeVertex]
  rcases f with ⟨i,b⟩
  cases b <;> funext ⟨b,j⟩ <;> cases b <;>
    simp [Strip.localWeight,Strip.corner₀,Strip.corner₁,Strip.corner₂,Strip.edgeWeight,
      Strip.edgeTop,Strip.edgeBottom,faceEdgeA,faceWeight,reverseWeight,Triangle.EdgeWeight.val,
      Fin.ext_iff,ha,hb,hc,show (2*i.val+1)/2=i.val by omega,
      show (2*i.val+2+1)/2=i.val+1 by omega,show (2*i.val+2)/2=i.val+1 by omega]

theorem faceEmbedding_b {n N} (hN : 0 < N) (f : Strip.Face N)
    (x : Retained n) (hb : x.val.b=0) :
    Strip.faceEmbedding f x = Strip.edgeEmbedding hN (faceEdgeB f)
      (faceWeight f ⟨⟨x.val.c,x.val.c_lt⟩,x.property⟩) := by
  have ha : x.val.a=n-x.val.c := by have := x.val.total; omega
  have hc : n-(n-x.val.c)=x.val.c := by have := x.val.c_lt; omega
  apply Subtype.ext
  apply Strip.weight_injective
  change Strip.weight (Strip.glue f x.val) = Strip.weight (Strip.edgeVertex hN _ _).val
  rw [Strip.weight_edgeVertex]
  rcases f with ⟨i,b⟩
  cases b <;> funext ⟨b,j⟩ <;> cases b <;>
    simp [Strip.localWeight,Strip.corner₀,Strip.corner₁,Strip.corner₂,Strip.edgeWeight,
      Strip.edgeTop,Strip.edgeBottom,faceEdgeB,faceWeight,reverseWeight,Triangle.EdgeWeight.val,
      Fin.ext_iff,ha,hb,hc,show (2*i.val+1)/2=i.val by omega,
      show (2*i.val+1+1)/2=i.val+1 by omega]

/-- The two transverse sides of `τ_i` have indices `i-1` and `i`. -/
theorem face_edges {N} (f : Strip.Face N) :
    ((faceEdgeA f).val=faceIndex f-1 ∧ (faceEdgeB f).val=faceIndex f) ∨
    ((faceEdgeB f).val=faceIndex f-1 ∧ (faceEdgeA f).val=faceIndex f) := by
  rcases f with ⟨i,b⟩
  cases b <;> simp [faceEdgeA,faceEdgeB,faceIndex] <;> omega

/-- Equal depths on the two sides and `C_p` in the face give precisely the local
triangle-shell live set. -/
theorem profile_face_preimage {n N p} (hN : 0 < N) (hp : p<n)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (f : Strip.Face N)
    (ha : d (faceEdgeA f)=p) (hb : d (faceEdgeB f)=p) (hc : c f=p) :
    Strip.faceEmbedding f ⁻¹' profileLive (n := n) hN d c=retainedLive p := by
  ext x
  change Strip.faceEmbedding f x ∈ profileLive hN d c ↔ x.val ∈ baseLive p
  rw [baseLive_iff hp]
  by_cases hxa : x.val.a=0
  · rw [faceEmbedding_a hN f x hxa,profileLive_edge,ha]
    have hw := faceWeight_live f p (⟨⟨x.val.c,x.val.c_lt⟩,x.property⟩ : Triangle.EdgeWeight n)
    rw [hw]
    have := x.property
    simp only [Triangle.EdgeWeight.val,cornerSet,Set.mem_setOf_eq]
    omega
  · by_cases hxb : x.val.b=0
    · rw [faceEmbedding_b hN f x hxb,profileLive_edge,hb]
      have hw := faceWeight_live f p (⟨⟨x.val.c,x.val.c_lt⟩,x.property⟩ : Triangle.EdgeWeight n)
      rw [hw]
      have := x.property
      simp only [Triangle.EdgeWeight.val,cornerSet,Set.mem_setOf_eq]
      omega
    · let y : Triangle.Interior n := ⟨x.val,by have := x.property; exact ⟨by omega,by omega,this⟩⟩
      have he : Strip.faceEmbedding f x=Strip.interiorEmbedding f y := rfl
      rw [he,profileLive_interior,hc]
      have := x.property
      simp only [y]
      tauto

theorem shell_profile_sequence {n N p} (hN : 0 < N) (hp : 1 ≤ p) (hn : 2*p+1 ≤ n)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (f : Strip.Face N)
    (ha : d (faceEdgeA f)=p) (hb : d (faceEdgeB f)=p) (hc : c f=p) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (profileLive hN d c)
      (profileLive hN d c \ Strip.faceEmbedding f '' (retainedLive p \ retainedFinish p)) := by
  classical
  exact sequence_support_mono
    (shell_sequence_on_live f hp hn _ (profile_face_preimage hN (by omega) d c f ha hb hc))
    (shell_support_internal hN f)

end FgStrip.Rounds
