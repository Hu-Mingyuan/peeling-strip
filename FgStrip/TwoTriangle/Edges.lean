import FgStrip.TwoTriangle.Labels

namespace FgStrip.TwoTriangle
open Triangle
namespace Pair
variable {n N : ℕ}
def firstEdge : Pair N → Strip.EdgeIndex N
  | .odd i => ⟨2*i.val, by have := i.isLt; omega⟩
  | .even i hi => ⟨2*i.val+1, by omega⟩
def lastEdge : Pair N → Strip.EdgeIndex N
  | .odd i => ⟨2*i.val+2, by have := i.isLt; omega⟩
  | .even i hi => ⟨2*i.val+3, by omega⟩
def stripWeight (s : Pair N) (k : EdgeWeight n) : EdgeWeight n :=
  match s with
  | .odd _ => k
  | .even _ _ => reverseWeight k

theorem edges_consecutive (s : Pair N) :
    s.firstEdge.val+1 = s.commonEdge.val ∧ s.commonEdge.val+1 = s.lastEdge.val := by
  cases s <;> dsimp [firstEdge, lastEdge, commonEdge] <;> omega

theorem depth_stripWeight (s : Pair N) (p : ℕ) (k : EdgeWeight n) :
    EdgeDepth n p (s.stripWeight k).val ↔ EdgeDepth n p k.val := by
  cases s
  · rfl
  · exact edgeDepth_reverse p k

theorem embed_D_edge (s : Pair N) (hN : 0 < N) (k : EdgeWeight n) :
    s.embed (D k) = Strip.edgeEmbedding hN s.commonEdge (s.stripWeight k) := by
  let p := Triangle.Vertex.mk (n-k.val) 0 k.val (by have := k.lt; omega)
    (by have := k.pos; have := k.lt; omega) (by have := k.lt; omega) k.lt
  have hp : s.gx p = (s.embed (D k)).1 := (s.gx_eq_embed_iff p _).mpr (x_D k)
  apply Subtype.ext
  apply Strip.weight_injective
  change Strip.weight (s.embed (D k)).1 = Strip.weight (Strip.edgeVertex hN _ _).1
  rw [← hp, Strip.weight_edgeVertex]
  cases s with
  | odd i =>
    have htop : (2*i.val+1+1)/2 = i.val+1 := by omega
    have hbot : (2*i.val+1)/2 = i.val := by omega
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [gx, faceX, tx, Strip.localWeight, Strip.corner₀, Strip.corner₁,
      Strip.corner₂, Strip.edgeWeight, Strip.edgeTop, Strip.edgeBottom, commonEdge,
      stripWeight, p, Fin.ext_iff, htop, hbot]
  | even i hi =>
    have htop : (2*i.val+2+1)/2 = i.val+1 := by omega
    have hbot : (2*i.val+2)/2 = i.val+1 := by omega
    have hk : n-(n-k.1.val)=k.1.val := by have := k.1.isLt; omega
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [gx, faceX, tx, swap, Strip.localWeight, Strip.corner₀, Strip.corner₁,
      Strip.corner₂, Strip.edgeWeight, Strip.edgeTop, Strip.edgeBottom, commonEdge,
      stripWeight, reverseWeight, EdgeWeight.val, p, Fin.ext_iff, htop, hbot, hk]

theorem embed_R_edge (s : Pair N) (hN : 0 < N) (k : EdgeWeight n) :
    s.embed (R k) = Strip.edgeEmbedding hN s.firstEdge (s.stripWeight k) := by
  have hp : s.gx k.bc = (s.embed (R k)).1 := (s.gx_eq_embed_iff k.bc _).mpr (x_R k)
  apply Subtype.ext
  apply Strip.weight_injective
  change Strip.weight (s.embed (R k)).1 = Strip.weight (Strip.edgeVertex hN _ _).1
  rw [← hp, Strip.weight_edgeVertex]
  cases s with
  | odd i =>
    have htop : (2*i.val+1)/2 = i.val := by omega
    have hbot : (2*i.val)/2 = i.val := by omega
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [gx, faceX, tx, Strip.localWeight, Strip.corner₀, Strip.corner₁,
      Strip.corner₂, Strip.edgeWeight, Strip.edgeTop, Strip.edgeBottom, firstEdge,
      stripWeight, EdgeWeight.bc, Fin.ext_iff, htop, hbot]
  | even i hi =>
    have htop : (2*i.val+1+1)/2 = i.val+1 := by omega
    have hbot : (2*i.val+1)/2 = i.val := by omega
    have hk : n-(n-k.1.val)=k.1.val := by have := k.1.isLt; omega
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [gx, faceX, tx, swap, Strip.localWeight, Strip.corner₀, Strip.corner₁,
      Strip.corner₂, Strip.edgeWeight, Strip.edgeTop, Strip.edgeBottom, firstEdge,
      stripWeight, reverseWeight, EdgeWeight.val, EdgeWeight.bc, Fin.ext_iff, htop, hbot, hk]

theorem embed_L_edge (s : Pair N) (hN : 0 < N) (k : EdgeWeight n) :
    s.embed (L k) = Strip.edgeEmbedding hN s.lastEdge (s.stripWeight k) := by
  let p := Triangle.Vertex.mk (n-k.val) 0 k.val (by have := k.lt; omega)
    (by have := k.pos; have := k.lt; omega) (by have := k.lt; omega) k.lt
  have hp : s.gy p = (s.embed (L k)).1 := (s.gy_eq_embed_iff p _).mpr (y_L k)
  apply Subtype.ext
  apply Strip.weight_injective
  change Strip.weight (s.embed (L k)).1 = Strip.weight (Strip.edgeVertex hN _ _).1
  rw [← hp, Strip.weight_edgeVertex]
  cases s with
  | odd i =>
    have htop : (2*i.val+2+1)/2 = i.val+1 := by omega
    have hbot : (2*i.val+2)/2 = i.val+1 := by omega
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [gy, faceY, ty, rot, Strip.localWeight, Strip.corner₀, Strip.corner₁,
      Strip.corner₂, Strip.edgeWeight, Strip.edgeTop, Strip.edgeBottom, lastEdge,
      stripWeight, p, Fin.ext_iff, htop, hbot]
  | even i hi =>
    have htop : (2*i.val+3+1)/2 = i.val+2 := by omega
    have hbot : (2*i.val+3)/2 = i.val+1 := by omega
    have hk : n-(n-k.1.val)=k.1.val := by have := k.1.isLt; omega
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [gy, faceY, ty, swap, rot, Strip.localWeight, Strip.corner₀, Strip.corner₁,
      Strip.corner₂, Strip.edgeWeight, Strip.edgeTop, Strip.edgeBottom, lastEdge,
      stripWeight, reverseWeight, EdgeWeight.val, p, Fin.ext_iff, htop, hbot, hk, Nat.add_assoc]
end Pair
end FgStrip.TwoTriangle
