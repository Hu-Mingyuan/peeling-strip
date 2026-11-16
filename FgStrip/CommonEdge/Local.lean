import FgStrip.CommonEdge.Columns
import FgStrip.CommonEdge.Coincident

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell
variable {n p : ℕ} (hn : 2*p+3 ≤ n)

/-- The concrete supported move, for either diagonal interval. -/
def forwardMove (b : Bool) :
    DeletionMove (wordLive (n := n) p b) (restrictMatrix (matrix n) Subtype.val) :=
  ⟨target hn b, deletionWord hn b, by
    unfold ValidDeletionWord
    rw [deletionWord_map]
    exact Or.inr (forward_sink hn b)⟩

theorem forwardMove_supported (b : Bool) : (forwardMove hn b).vertex.val ∈ support n := by
  change 0 < n-p-1 ∧ n-p-1 < n
  omega

def afterFirst {n} (p : ℕ) : Set (Grid n) :=
  {u | u ∈ live p ∧ ¬(u.i=n-p-1 ∧ u.j=n-p-1)}

include hn in
theorem first_sequence : Sequence (matrix n) (support n) (live p) (afterFirst p) := by
  have hout : (forwardMove hn false).liveSet=afterFirst p := by
    ext u
    have he : u=(forwardMove hn false).vertex.val ↔ u.i=n-p-1 ∧ u.j=n-p-1 := by
      constructor
      · intro h; subst u; exact ⟨rfl,rfl⟩
      · rintro ⟨hi,hj⟩; exact Grid.ext hi hj
    simp only [DeletionMove.liveSet, afterFirst, Set.mem_ofPred_eq, wordLive_false, ne_eq, he]
  have hs : Sequence (matrix n) (support n) (wordLive p false) (afterFirst p) := by
    apply Sequence.cons (forwardMove hn false) (forwardMove_supported hn false)
    · exact deletionWord_supported hn false
    · rw [hout]; exact .nil _
  simpa only [wordLive_false] using hs

omit hn in
/-- Half-turn of the once-deleted live set into the independently calculated
modified-word live set. -/
def secondMap (hsize : 2*p+3 ≤ n) (u : afterFirst (n := n) p) : wordLive (n := n) p true :=
  ⟨H u.val, (live_halfturn u.val).mpr u.property.1, by
    clear hn
    intro _ he
    have hi := u.val.i_le
    have hj := u.val.j_lt
    have hi' : n-u.val.i=p+1 := by simpa only [H_i] using he.1
    have hj' : n-u.val.j=p+1 := by simpa only [H_j] using he.2
    exact u.property.2 (by constructor <;> omega)⟩

omit hn in
def secondLift (hsize : 2*p+3 ≤ n) (u : wordLive (n := n) p true) : afterFirst (n := n) p :=
  ⟨H u.val, (live_halfturn u.val).mpr u.property.1, by
    clear hn
    intro he
    have hi := u.val.i_le
    have hj := u.val.j_lt
    have hi' : n-u.val.i=n-p-1 := by simpa only [H_i] using he.1
    have hj' : n-u.val.j=n-p-1 := by simpa only [H_j] using he.2
    exact u.property.2 rfl (by constructor <;> omega)⟩

@[simp] theorem secondMap_lift (u : wordLive (n := n) p true) :
    secondMap hn (secondLift hn u)=u := by
  apply Subtype.ext
  exact H_H u.val

theorem secondMap_injective : Function.Injective (secondMap hn) := by
  intro u v he
  apply Subtype.ext
  have h := congrArg (fun x : wordLive (n := n) p true => H x.val) he
  simpa only [secondMap, H_H] using h

include hn in
/-- The modified word transported back to delete the other endpoint. -/
theorem second_move : ∃ d : DeletionMove (afterFirst (n := n) p)
    (restrictMatrix (matrix n) Subtype.val),
    d.vertex.val ∈ support n ∧ (∀ k ∈ d.word, k.val.val ∈ support n) ∧
    d.liveSet=finish p := by
  let d₀ := forwardMove hn true
  let s := secondLift hn d₀.vertex
  have hW : ∀ k ∈ d₀.word, ∃ l, secondMap hn l=k.val := by
    intro k hk
    exact ⟨secondLift hn k.val, secondMap_lift hn _⟩
  have hm := pullMove d₀ (secondMap hn) (secondMap_injective hn) s (secondMap_lift hn _) hW
  have hmatrix : restrictMatrix (restrictMatrix (matrix n) Subtype.val) (secondMap hn)=
      restrictMatrix (matrix n) (Subtype.val : afterFirst (n := n) p → Grid n) := by
    funext u v
    exact matrix_halfturn u.val v.val
  rw [hmatrix] at hm
  obtain ⟨d,hd,hw⟩ := hm
  have hdi : d.vertex.val.i=p+1 := by
    rw [hd]
    change (H (target hn true).val).i=p+1
    rw [H_i,target_i]
    omega
  have hdj : d.vertex.val.j=p+1 := by
    rw [hd]
    change (H (target hn true).val).j=p+1
    rw [H_j,target_j]
    omega
  refine ⟨d, ?_, ?_, ?_⟩
  · change 0 < d.vertex.val.i ∧ d.vertex.val.i < n
    rw [hdi]
    omega
  · intro k hk
    have hm : secondMap hn k.val ∈ d₀.word.map Subtype.val := by
      rw [← hw]
      exact List.mem_map.mpr ⟨k.val, List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩
    obtain ⟨l,hl,he⟩ := List.mem_map.mp hm
    have hs := deletionWord_supported hn true l hl
    have hei := congrArg (fun x : wordLive (n := n) p true => x.val.i) he
    change l.val.val.i=(H k.val.val).i at hei
    rw [H_i] at hei
    change 0 < l.val.val.i ∧ l.val.val.i < n at hs
    change 0 < k.val.val.i ∧ k.val.val.i < n
    have := k.val.val.i_le
    omega
  · ext u
    have he : u=d.vertex.val ↔ u.i=p+1 ∧ u.j=p+1 := by
      constructor
      · intro h; subst u; exact ⟨hdi,hdj⟩
      · rintro ⟨hi,hj⟩; exact Grid.ext (hi.trans hdi.symm) (hj.trans hdj.symm)
    simp only [DeletionMove.liveSet, afterFirst, finish, endpoints, Set.mem_ofPred_eq,
      Set.mem_sdiff, ne_eq, he]
    rw [and_assoc]
    apply and_congr_right
    intro _
    omega

include hn in
theorem distinct_sequence : Sequence (matrix n) (support n) (live p) (finish p) := by
  obtain ⟨d,hs,hw,hout⟩ := second_move hn
  apply (first_sequence hn).trans
  apply Sequence.cons d hs hw
  rw [hout]
  exact .nil _

/-- Concrete common-edge deletion, with coincident endpoints deleted once. -/
theorem common_edge_sequence {n p : ℕ} (hp : p < n/2) :
    Sequence (matrix n) (support n) (live p) (finish p) := by
  have hn : 2*p+2 ≤ n := by omega
  by_cases hc : n=2*p+2
  · exact coincident_sequence hc
  · exact distinct_sequence (by omega)

end FgStrip.CommonEdge
