import FgStrip.Rounds.PairGeometry
import FgStrip.Rounds.FaceGeometry

namespace FgStrip.Rounds
open TriangleShell TwoTriangle CommonEdge

/-- The next two edge endpoints, counted once when they coincide. -/
def edgeLayer {n N} (hN : 0 < N) (j : Strip.EdgeIndex N) (p : ℕ) :
    Set (Strip.Vertex n N) :=
  Strip.edgeEmbedding hN j '' {k | k.val=p+1 ∨ k.val=n-p-1}

theorem stripWeight_involutive {n N} (s : Pair N) (k : Triangle.EdgeWeight n) :
    s.stripWeight (s.stripWeight k)=k := by
  cases s
  · rfl
  · apply Subtype.ext; apply Fin.ext
    have := k.lt
    change n-(n-k.val)=k.val
    omega

theorem stripWeight_endpoint {n N} (s : Pair N) (k : Triangle.EdgeWeight n)
    {p} (hp : p<n/2) :
    ((s.stripWeight k).val=p+1 ∨ (s.stripWeight k).val=n-p-1) ↔
      (k.val=p+1 ∨ k.val=n-p-1) := by
  cases s
  · rfl
  · have := k.lt
    change (n-k.val=p+1 ∨ n-k.val=n-p-1) ↔ _
    omega

theorem pair_endpoints_image {n N p} (hN : 0 < N) (s : Pair N) (hp : p<n/2) :
    s.embed '' endpoints (n := n) p=edgeLayer hN s.commonEdge p := by
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    let k : Triangle.EdgeWeight n := ⟨⟨u.j,u.j_lt⟩,u.j_pos⟩
    have he : u=D k := Grid.ext hu.1 rfl
    rw [he,s.embed_D_edge hN]
    exact ⟨s.stripWeight k,(stripWeight_endpoint s k hp).mpr hu.2,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    refine ⟨D (s.stripWeight k),⟨rfl,(stripWeight_endpoint s k hp).mpr hk⟩,?_⟩
    rw [s.embed_D_edge hN,stripWeight_involutive]

/-- Raising one edge depth removes precisely its next endpoint layer. -/
theorem profile_edge_update {n N p} (hN : 0 < N) (hp : p<n/2)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (j : Strip.EdgeIndex N)
    (hd : d j=p) :
    profileLive (n := n) hN (Function.update d j (p+1)) c =
      profileLive hN d c \ edgeLayer hN j p := by
  classical
  ext v
  constructor
  · intro hv
    refine ⟨⟨?_,hv.2⟩,?_⟩
    · intro l k he
      have hk := hv.1 l k he
      by_cases hl : l=j
      · subst l
        simp only [Function.update_self] at hk
        rw [hd]
        omega
      · simpa only [Function.update_of_ne hl] using hk
    · rintro ⟨k,hk,he⟩
      have hh := hv.1 j k he
      simp only [Function.update_self] at hh
      change k.val=p+1 ∨ k.val=n-p-1 at hk
      omega
  · rintro ⟨hv,hn⟩
    refine ⟨?_,hv.2⟩
    intro l k he
    have hk := hv.1 l k he
    by_cases hl : l=j
    · subst l
      rw [hd] at hk
      simp only [Function.update_self]
      have hh : ¬(k.val=p+1 ∨ k.val=n-p-1) := fun h => hn ⟨k,h,he⟩
      omega
    · simpa only [Function.update_of_ne hl] using hk

/-- Raising one face depth removes precisely the concrete shell output. -/
theorem profile_face_update {n N p} (hN : 0 < N) (hp : p<n)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (f : Strip.Face N)
    (ha : d (faceEdgeA f)=p) (hb : d (faceEdgeB f)=p) (hc : c f=p) :
    profileLive (n := n) hN d (Function.update c f (p+1)) =
      profileLive hN d c \ Strip.faceEmbedding f '' (retainedLive p \ retainedFinish p) := by
  classical
  have hpre := profile_face_preimage hN hp d c f ha hb hc
  ext v
  constructor
  · intro hv
    have hold : v ∈ profileLive hN d c := by
      refine ⟨hv.1,?_⟩
      intro g x he hx
      by_cases hg : g=f
      · subst g
        have hh := hv.2 f x he
        rw [Function.update_self] at hh
        rw [hc] at hx
        exact hh (cornerSet_mono (by omega) hx)
      · exact hv.2 g x he (by simpa only [Function.update_of_ne hg] using hx)
    refine ⟨hold,?_⟩
    rintro ⟨x,hx,he⟩
    have hcorner : x.val ∈ cornerSet (p+1) := by
      have hbase : x.val ∈ baseLive p := hx.1
      by_contra hn
      exact hx.2 ⟨hbase,hn⟩
    let y : Triangle.Interior n := ⟨x.val,hcorner.1,hcorner.2.1,hcorner.2.2.1⟩
    have hy := hv.2 f y he
    rw [Function.update_self] at hy
    exact hy hcorner
  · rintro ⟨hv,hn⟩
    refine ⟨hv.1,?_⟩
    intro g x he hx
    by_cases hg : g=f
    · subst g
      rw [Function.update_self] at hx
      let y : Retained n := ⟨x.val,x.property.2.2⟩
      have hy : y ∈ retainedLive p := by
        rw [← hpre]
        change Strip.interiorEmbedding f x ∈ profileLive hN d c
        rwa [he]
      apply hn
      refine ⟨y,⟨hy,?_⟩,he⟩
      intro hf
      exact hf.2 hx
    · exact hv.2 g x he (by simpa only [Function.update_of_ne hg] using hx)

/-- A complete common-edge step between two explicit profiles. -/
theorem edge_profile_step {n N p} (hN : 0 < N) (hp : p<n/2)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (s : Pair N)
    (hd : d s.commonEdge=p) (hl : p ≤ d s.firstEdge) (hr : p ≤ d s.lastEdge)
    (hx : c s.faceX=p+1) (hy : c s.faceY=p+1) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (profileLive hN d c)
      (profileLive hN (Function.update d s.commonEdge (p+1)) c) := by
  rw [profile_edge_update hN hp d c s.commonEdge hd,← pair_endpoints_image hN s hp]
  exact pair_profile_sequence hN hp d c s hd hl hr hx hy

/-- A complete triangle-interior step between two explicit profiles. -/
theorem face_profile_step {n N p} (hN : 0 < N) (hp : 1 ≤ p) (hn : 2*p+1 ≤ n)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (f : Strip.Face N)
    (ha : d (faceEdgeA f)=p) (hb : d (faceEdgeB f)=p) (hc : c f=p) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (profileLive hN d c)
      (profileLive hN d (Function.update c f (p+1))) := by
  rw [profile_face_update hN (by omega) d c f ha hb hc]
  exact shell_profile_sequence hN hp hn d c f ha hb hc

end FgStrip.Rounds
