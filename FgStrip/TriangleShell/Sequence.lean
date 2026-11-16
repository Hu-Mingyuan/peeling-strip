import FgStrip.TriangleShell.Local
import FgStrip.TriangleShell.Transport

namespace FgStrip.TriangleShell
open Triangle

/-- Mutation and deletion support, excluding all three sides. -/
def interiorSet (n : ℕ) : Set (Vertex n) := {v | 0 < v.a ∧ 0 < v.b ∧ 0 < v.c}

section First
variable {n p a : ℕ} (hn : 2*p+1 ≤ n) (ha : 1 ≤ a) (hap : a ≤ p)

theorem firstMove_target_coordinates :
    (firstMove hn ha hap).vertex.val.a=a ∧
    (firstMove hn ha hap).vertex.val.b=n-p-1 ∧
    (firstMove hn ha hap).vertex.val.c=p+1-a := by
  change (linePath hn ha hap (n-p-2)).val.a=a ∧
    (linePath hn ha hap (n-p-2)).val.b=n-p-1 ∧
    (linePath hn ha hap (n-p-2)).val.c=p+1-a
  rw [linePath_a, linePath_b hn ha hap (n-p-2) (by omega),
    linePath_c hn ha hap (n-p-2) (by omega)]
  omega

theorem firstMove_target_interior : (firstMove hn ha hap).vertex.val ∈ interiorSet n :=
  linePath_interior hn ha hap _

theorem firstMove_word_coordinates (k : Remaining (firstMove hn ha hap).vertex)
    (hk : k ∈ (firstMove hn ha hap).word) :
    k.val.val.a=a ∧ k.val.val ∈ interiorSet n := by
  have hmem : k.val ∈ ((firstWord hn ha hap).map Subtype.val) := List.mem_map.mpr ⟨k,hk,rfl⟩
  rw [firstWord_map] at hmem
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hmem
  rw [← he]
  exact ⟨linePath_a hn ha hap i, linePath_interior hn ha hap i⟩

theorem firstMove_liveSet : (firstMove hn ha hap).liveSet = firstLive (n := n) p (a-1) := by
  ext j
  have ht := j.total
  obtain ⟨hsa,hsb,hsc⟩ := firstMove_target_coordinates hn ha hap
  have he : j=(firstMove hn ha hap).vertex.val ↔ j.a=a ∧ j.b=n-p-1 := by
    constructor
    · intro h; subst j; exact ⟨hsa,hsb⟩
    · rintro ⟨hja,hjb⟩
      apply Vertex.ext <;> omega
  simp only [DeletionMove.liveSet, firstLive, baseLive, Set.mem_ofPred_eq, ne_eq, he]
  omega

end First

/-- All first-family deletions, in decreasing first coordinate. -/
theorem first_sequence {n p : ℕ} (hn : 2*p+1 ≤ n) (a : ℕ) (hap : a ≤ p) :
    Sequence (matrix n) (interiorSet n) (firstLive p a) (firstLive p 0) := by
  induction a with
  | zero => exact .nil _
  | succ a ih =>
    let d := firstMove hn (show 1 ≤ a+1 by omega) hap
    apply Sequence.cons d (firstMove_target_interior hn (by omega) hap)
    · intro k hk
      exact (firstMove_word_coordinates hn (by omega) hap k hk).2
    · have h := firstMove_liveSet hn (show 1 ≤ a+1 by omega) hap
      change Sequence (matrix n) (interiorSet n) (firstMove hn (by omega) hap).liveSet _
      rw [h]
      exact ih (by omega)

/-- During the exchanged family the entire first family is already absent. -/
def secondLive {n : ℕ} (p b : ℕ) : Set (Vertex n) :=
  {v | v ∈ firstLive p 0 ∧ (v.a=n-p-1 → v.b ≤ b)}

section Second
variable {n p a : ℕ} (hn : 2*p+1 ≤ n) (ha : 1 ≤ a) (hap : a ≤ p)
variable (halt : a < n-p-1)

/-- Reflection maps the second-family live set into the first-family live set. -/
def secondMap (j : secondLive (n := n) p a) : firstLive (n := n) p a :=
  ⟨exchange j.val, (baseLive_exchange j.val).mpr j.property.1.1, by
    simpa only [exchange_a, exchange_b] using j.property.2⟩

theorem secondMap_injective : Function.Injective (secondMap (n := n) (p := p) (a := a)) := by
  intro i j h
  apply Subtype.ext
  have he := congrArg (fun k : firstLive (n := n) p a => exchange k.val) h
  simpa only [secondMap, exchange_exchange] using he

/-- Every vertex of the required line survives the first family when `a < b₀`. -/
def secondLift (k : firstLive (n := n) p a) (hk : k.val.a=a) : secondLive (n := n) p a :=
  ⟨exchange k.val, ⟨(baseLive_exchange k.val).mpr k.property.1, by
    simp only [exchange_a, exchange_b]
    intro h
    omega⟩, by
      simp only [exchange_a, exchange_b]
      exact k.property.2⟩

@[simp] theorem secondMap_lift (k : firstLive (n := n) p a) (hk : k.val.a=a) :
    secondMap (secondLift halt k hk) = k := by
  apply Subtype.ext
  exact exchange_exchange k.val

include hn ha hap halt in
/-- The exchanged local deletion, restricted past the complete first family. -/
theorem second_move :
    ∃ d : DeletionMove (secondLive (n := n) p a) (restrictMatrix (matrix n) Subtype.val),
      d.vertex.val ∈ interiorSet n ∧
      (∀ k ∈ d.word, k.val.val ∈ interiorSet n) ∧
      d.liveSet=secondLive p (a-1) := by
  let d₀ := firstMove hn ha hap
  have hcoord := firstMove_target_coordinates hn ha hap
  let s := secondLift halt d₀.vertex hcoord.1
  have hs : secondMap s=d₀.vertex := secondMap_lift halt _ _
  have hw : ∀ k ∈ d₀.neg.word, ∃ l : secondLive (n := n) p a, secondMap l=k.val := by
    intro k hk
    have hka := (firstMove_word_coordinates hn ha hap k hk).1
    exact ⟨secondLift halt k.val hka, secondMap_lift halt _ _⟩
  have h := pullMove d₀.neg secondMap secondMap_injective s hs hw
  have hmatrix : restrictMatrix (-restrictMatrix (matrix n) Subtype.val) secondMap =
      restrictMatrix (matrix n) (Subtype.val : secondLive (n := n) p a → Vertex n) := by
    funext i j
    change -matrix n (exchange i.val) (exchange j.val) = matrix n i.val j.val
    rw [matrix_exchange, neg_neg]
  rw [hmatrix] at h
  obtain ⟨d, hd, hwmap⟩ := h
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [hd]
    have hi := firstMove_target_interior hn ha hap
    change 0 < d₀.vertex.val.b ∧ 0 < d₀.vertex.val.a ∧ 0 < d₀.vertex.val.c
    exact ⟨hi.2.1,hi.1,hi.2.2⟩
  · intro k hk
    have hmem : secondMap k.val ∈ d₀.neg.word.map Subtype.val := by
      rw [← hwmap]
      exact List.mem_map.mpr ⟨k.val, List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩
    obtain ⟨l, hl, he⟩ := List.mem_map.mp hmem
    have hi := (firstMove_word_coordinates hn ha hap l hl).2
    have ha' := congrArg (fun x : firstLive (n := n) p a => x.val.a) he
    have hb' := congrArg (fun x : firstLive (n := n) p a => x.val.b) he
    have hc' := congrArg (fun x : firstLive (n := n) p a => x.val.c) he
    change 0 < k.val.val.a ∧ 0 < k.val.val.b ∧ 0 < k.val.val.c
    change l.val.val.a=k.val.val.b at ha'
    change l.val.val.b=k.val.val.a at hb'
    change l.val.val.c=k.val.val.c at hc'
    dsimp [interiorSet] at hi
    omega
  · ext j
    have ht := j.total
    have hsa : d.vertex.val.a=n-p-1 := by
      rw [hd]
      exact hcoord.2.1
    have hsb : d.vertex.val.b=a := by
      rw [hd]
      exact hcoord.1
    have hsc : d.vertex.val.c=p+1-a := by
      rw [hd]
      exact hcoord.2.2
    have heq : j=d.vertex.val ↔ j.a=n-p-1 ∧ j.b=a := by
      constructor
      · intro h; subst j; exact ⟨hsa,hsb⟩
      · rintro ⟨hja,hjb⟩
        apply Vertex.ext <;> omega
    simp only [DeletionMove.liveSet, secondLive, firstLive, baseLive,
      Set.mem_ofPred_eq, ne_eq, heq]
    omega

end Second

/-- Exchanged-family deletions, excluding the shared odd endpoint. -/
theorem second_sequence {n p : ℕ} (hn : 2*p+1 ≤ n)
    (a : ℕ) (hap : a ≤ p) (halt : a < n-p-1) :
    Sequence (matrix n) (interiorSet n) (secondLive p a) (secondLive p 0) := by
  induction a with
  | zero => exact .nil _
  | succ a ih =>
    obtain ⟨d, hs, hw, hout⟩ := second_move hn (show 1 ≤ a+1 by omega) hap halt
    apply Sequence.cons d hs hw
    rw [hout]
    exact ih (by omega) (by omega)

/-- The upper bound decreases from `p` to `p-1` exactly when the two families overlap. -/
theorem second_start {n p : ℕ} (hn : 2*p+1 ≤ n) :
    secondLive (n := n) p (min p (n-p-2)) = firstLive p 0 := by
  ext j
  have ht := j.total
  simp only [secondLive, firstLive, baseLive, Set.mem_ofPred_eq]
  omega

/-- Final live set: the side depth is still `p`; only the interior shell changes. -/
theorem second_finish {n p : ℕ} (hn : 2*p+1 ≤ n) :
    secondLive (n := n) p 0 = baseLive p \ cornerSet (p+1) := by
  ext j
  have ht := j.total
  simp only [secondLive, firstLive, baseLive, cornerSet, Set.mem_ofPred_eq, Set.mem_sdiff]
  omega

/-- Universally quantified triangle-interior shell deletion for the concrete cycle matrix. -/
theorem shell_deletion {n p : ℕ} (hp : 1 ≤ p) (hn : 2*p+1 ≤ n) :
    Sequence (matrix n) (interiorSet n) (baseLive p) (baseLive p \ cornerSet (p+1)) := by
  have h₁ := first_sequence hn p (by omega)
  rw [firstLive_start hn] at h₁
  have h₂ := second_sequence hn (min p (n-p-2)) (by omega) (by omega)
  rw [second_start hn, second_finish hn] at h₂
  exact h₁.trans h₂

end FgStrip.TriangleShell
