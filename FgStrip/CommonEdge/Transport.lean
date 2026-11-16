import FgStrip.CommonEdge.Coincident

namespace FgStrip.CommonEdge
open TwoTriangle TriangleShell

/-- A supported sequence survives every extra deletion outside its support. -/
theorem sequence_restrict {X : Type*} [DecidableEq X] {A : Matrix X X ℤ}
    {I U T : Set X} (h : Sequence A I U T) (F : Set X)
    (hF : ∀ x ∈ I, x ∉ F) : Sequence A I (U \ F) (T \ F) := by
  classical
  induction h with
  | nil U => exact .nil _
  | @cons U T d hs hw tail ih =>
    let f : ↥(U \ F) → U := fun x => ⟨x.val,x.property.1⟩
    have hf : Function.Injective f := by
      intro x y he; apply Subtype.ext; exact congrArg (fun z : U => z.val) he
    let s : ↥(U \ F) := ⟨d.vertex.val,d.vertex.property,hF _ hs⟩
    have hW : ∀ k ∈ d.word, ∃ l : ↥(U \ F), f l=k.val := by
      intro k hk
      exact ⟨⟨k.val.val,k.val.property,hF _ (hw k hk)⟩,rfl⟩
    obtain ⟨e,he,hew⟩ := pullMove d f hf s rfl hW
    change DeletionMove (U \ F) (restrictMatrix A Subtype.val) at e
    apply Sequence.cons e
    · simpa only [he] using hs
    · intro k hk
      have hm : f k.val ∈ d.word.map Subtype.val := by
        rw [← hew]
        exact List.mem_map.mpr ⟨k.val,List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩
      obtain ⟨l,hl,hel⟩ := List.mem_map.mp hm
      have hv := congrArg Subtype.val hel
      simpa only [hv] using hw l hl
    · have hout : e.liveSet=d.liveSet \ F := by
        ext x
        simp only [DeletionMove.liveSet, Set.mem_sdiff, Set.mem_ofPred_eq, he]
        change ((x ∈ U ∧ x ∉ F) ∧ x ≠ d.vertex.val) ↔
          ((x ∈ U ∧ x ≠ d.vertex.val) ∧ x ∉ F)
        tauto
      rw [hout]
      exact ih

/-- Arrow reversal preserves the supported sequence, with source and sink exchanged. -/
theorem sequence_neg {X : Type*} [DecidableEq X] {A : Matrix X X ℤ}
    {I U T : Set X} (h : Sequence A I U T) : Sequence (-A) I U T := by
  induction h with
  | nil => exact .nil _
  | cons d hs hw tail ih => exact .cons d.neg hs hw ih

/-- Extra interface deletions are disjoint from the permitted support. -/
theorem interface_disjoint {n} (F : Set (Grid n))
    (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n) : ∀ u ∈ support n, u ∉ F := by
  intro u hu hf
  have := hF u hf
  change 0 < u.i ∧ u.i < n at hu
  omega

/-- Coincident-endpoint execution with arbitrary further interface deletions
and arbitrary complementary skew addition. -/
theorem coincident_restrict_add {n p} (hn : n=2*p+2)
    (F : Set (Grid n)) (hF : ∀ u ∈ F, u.i=0 ∨ u.i=n)
    (E : Matrix (Grid n) (Grid n) ℤ) (hE : SkewSymmetric E)
    (hz : ∀ u ∈ support n, ∀ v, E u v=0) :
    Execution (support n)
      (restrictMatrix (matrix n+E) (Subtype.val : ↥(live p \ F) → Grid n))
      (restrictMatrix (matrix n+E) (Subtype.val : ↥(finish p \ F) → Grid n)) :=
  ((sequence_restrict (coincident_sequence hn) F (interface_disjoint F hF)).add E hE hz).execution

end FgStrip.CommonEdge
