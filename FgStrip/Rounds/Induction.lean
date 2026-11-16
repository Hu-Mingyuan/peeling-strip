import FgStrip.Rounds.Batch

namespace FgStrip.Rounds
open TriangleShell TwoTriangle

/-- Triangles whose corner depth increases in the next round. -/
def activeFaces (N p : ℕ) : Finset (Strip.Face N) :=
  Finset.univ.filter fun f => p<faceIndex f ∧ faceIndex f+p ≤ 2*N

/-- Edges whose depth increases in the next round. -/
def activeEdges (N p : ℕ) : Finset (Strip.EdgeIndex N) :=
  Finset.univ.filter fun j => p<j.val ∧ j.val+p<2*N

@[simp] theorem mem_activeFaces {N p} (f : Strip.Face N) :
    f ∈ activeFaces N p ↔ p<faceIndex f ∧ faceIndex f+p ≤ 2*N := by simp [activeFaces]

@[simp] theorem mem_activeEdges {N p} (j : Strip.EdgeIndex N) :
    j ∈ activeEdges N p ↔ p<j.val ∧ j.val+p<2*N := by simp [activeEdges]

theorem raised_edgeDepth (N p : ℕ) :
    raised (fun j : Strip.EdgeIndex N => edgeDepth N p j.val) (activeEdges N p) p =
      fun j => edgeDepth N (p+1) j.val := by
  funext j
  have := j.isLt
  simp only [raised,mem_activeEdges,edgeDepth]
  split_ifs <;> omega

theorem raised_faceDepth (N p : ℕ) :
    raised (fun f : Strip.Face N => faceDepth N p (faceIndex f)) (activeFaces N p) p =
      fun f => faceDepth N (p+1) (faceIndex f) := by
  funext f
  have := faceIndex_bounds f
  simp only [raised,mem_activeFaces,faceDepth]
  split_ifs <;> omega

theorem pair_face_indices {N} (s : Pair N) :
    faceIndex s.faceX=s.commonEdge.val ∧ faceIndex s.faceY=s.commonEdge.val+1 := by
  cases s <;> simp [faceIndex,Pair.faceX,Pair.faceY,Pair.commonEdge] <;> omega

theorem active_face_depths {N p} (f : Strip.Face N) (hf : f ∈ activeFaces N p) :
    edgeDepth N p (faceEdgeA f).val=p ∧ edgeDepth N p (faceEdgeB f).val=p ∧
      faceDepth N p (faceIndex f)=p := by
  have hh := (mem_activeFaces f).mp hf
  have he := face_edges f
  have hb := faceIndex_bounds f
  simp only [edgeDepth,faceDepth]
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rw [ha,hb] <;> omega

theorem active_edge_depths {N p} (j : Strip.EdgeIndex N) (hj : j ∈ activeEdges N p) :
    ∃ s : Pair N, s.commonEdge=j ∧ edgeDepth N p j.val=p ∧
      p ≤ edgeDepth N p s.firstEdge.val ∧ p ≤ edgeDepth N p s.lastEdge.val ∧
      faceDepth N (p+1) (faceIndex s.faceX)=p+1 ∧
      faceDepth N (p+1) (faceIndex s.faceY)=p+1 := by
  have hh := (mem_activeEdges j).mp hj
  let s := Pair.ofEdge j (by omega) (by omega)
  have hs : s.commonEdge=j := Pair.commonEdge_ofEdge j _ _
  have he := s.edges_consecutive
  have hf := pair_face_indices s
  rw [hs] at he hf
  refine ⟨s,hs,?_,?_,?_,?_,?_⟩ <;> simp only [edgeDepth,faceDepth]
  all_goals omega

/-- `C_1` is empty, so the first edge sweep starts from the entire strip. -/
theorem first_profile {n N} (hN : 0 < N) :
    profileLive (n := n) hN (fun _ => 0) (fun _ => 1)=Set.univ := by
  ext v
  simp only [profileLive,Set.mem_setOf_eq,Set.mem_univ,iff_true,cornerSet_one,
    Set.mem_empty_iff_false,not_false_eq_true,implies_true,and_true,Nat.sub_zero]
  intro j k _
  exact ⟨k.pos,k.lt⟩

/-- The first round covers every nonprotected edge, including ranks two and three. -/
theorem first_round {n N} (hn : 2 ≤ n) (hN : 0 < N) :
    Sequence (Strip.matrix n N) (Strip.internal hN) Set.univ (roundLive hN 1) := by
  classical
  have h := batch_edges (n := n) hN (p := 0) (by omega)
    (fun _ => 0) (fun _ => 1) (activeEdges N 0) (by
      intro j hj
      have hh := (mem_activeEdges j).mp hj
      exact ⟨Pair.ofEdge j (by omega) (by omega),Pair.commonEdge_ofEdge j _ _,rfl,
        Nat.le_refl 0,Nat.le_refl 0,rfl,rfl⟩)
  have he : raised (fun _ : Strip.EdgeIndex N => 0) (activeEdges N 0) 0 =
      fun j => edgeDepth N 1 j.val := by simpa using raised_edgeDepth N 0
  have hc : (fun _ : Strip.Face N => 1) = fun f => faceDepth N 1 (faceIndex f) := by
    funext f
    have := faceIndex_bounds f
    simp only [faceDepth]
    omega
  rw [first_profile hN,he,hc] at h
  exact h

/-- The successor round first removes triangle shells, then common-edge layers. -/
theorem next_round {n N p} (hN : 0 < N) (hp : 1 ≤ p) (hn : p<n/2) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (roundLive hN p) (roundLive hN (p+1)) := by
  classical
  have hf := batch_faces (n := n) hN hp (by omega)
    (fun j => edgeDepth N p j.val) (fun f => faceDepth N p (faceIndex f))
    (activeFaces N p) (active_face_depths)
  rw [raised_faceDepth] at hf
  have he := batch_edges (n := n) hN hn (fun j => edgeDepth N p j.val)
    (fun f => faceDepth N (p+1) (faceIndex f)) (activeEdges N p) active_edge_depths
  rw [raised_edgeDepth] at he
  exact hf.trans he

/-- Actual supported moves reach the exact live-set profile for every round up to
`floor(n/2)`. No deletion-existence premise occurs. -/
theorem rounds {n N} (hn : 2 ≤ n) (hN : 0 < N) (p : ℕ) (hp : 1 ≤ p) (hq : p ≤ n/2) :
    Sequence (Strip.matrix n N) (Strip.internal hN) Set.univ (roundLive hN p) := by
  induction p with
  | zero => omega
  | succ p ih =>
    by_cases hz : p=0
    · subst p
      exact first_round hn hN
    · exact (ih (by omega) (by omega)).trans (next_round hN (by omega) (by omega))

end FgStrip.Rounds
