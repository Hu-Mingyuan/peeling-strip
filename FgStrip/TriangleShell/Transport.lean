import FgStrip.Deletion

namespace FgStrip.TriangleShell

/-- Pull a concrete deletion move back along an injection retaining its target and word.
This includes arbitrary additional deletions away from those vertices. -/
theorem pullMove {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {U : Set X} {T : Set Y} {B : Matrix U U ℤ} (d : DeletionMove U B)
    (f : T → U) (hf : Function.Injective f) (s : T) (hs : f s=d.vertex)
    (hW : ∀ k ∈ d.word, ∃ l : T, f l=k.val) :
    ∃ e : DeletionMove T (restrictMatrix B f), e.vertex=s ∧
      (e.word.map Subtype.val).map f = d.word.map Subtype.val := by
  classical
  let lift : {k // k ∈ d.word} → Remaining s := fun k =>
    ⟨Classical.choose (hW k.val k.property), by
      intro he
      have hchoose := Classical.choose_spec (hW k.val k.property)
      rw [he, hs] at hchoose
      exact k.val.property hchoose.symm⟩
  let W := d.word.attach.map lift
  have hmap : (W.map Subtype.val).map f = d.word.map Subtype.val := by
    simp only [W, List.map_map, Function.comp_def]
    calc
      _ = d.word.attach.map (fun k => k.val.val) := by
        apply List.map_congr_left
        intro k hk
        exact Classical.choose_spec (hW k.val k.property)
      _ = d.word.map Subtype.val := List.attach_map_val
  have hv : ValidDeletionWord (restrictMatrix B f) s W := by
    unfold ValidDeletionWord
    rw [← restrictMatrix_mutateWord B f hf (W.map Subtype.val), hmap]
    apply SourceOrSink.restrictMatrix f s
    rw [hs]
    exact d.source_or_sink
  exact ⟨⟨s,W,hv⟩, rfl, hmap⟩

/-- Arbitrary skew additions on the complementary block preserve a concrete move. -/
def addMove {X : Type*} [DecidableEq X] {U : Set X} {B : Matrix U U ℤ}
    (d : DeletionMove U B) (E : Matrix U U ℤ) (hE : SkewSymmetric E)
    (hs : ∀ j, E d.vertex j=0) (hW : ∀ k ∈ d.word, ∀ j, E k.val j=0) :
    DeletionMove U (B+E) :=
  ⟨d.vertex, d.word, (validDeletionWord_add_iff B E hE d.vertex d.word hW hs).mpr
    d.source_or_sink⟩

/-- A finite sequence on explicit live sets. Each step performs the actual
mutate/delete/reverse operation; `DeletionMove.output_original` proves that the
next input is precisely the restriction appearing in the following constructor. -/
inductive Sequence {X : Type*} [DecidableEq X] (A : Matrix X X ℤ) (I : Set X) :
    Set X → Set X → Prop
  | nil (U) : Sequence A I U U
  | cons {U T} (d : DeletionMove U (restrictMatrix A Subtype.val))
      (hs : d.vertex.val ∈ I)
      (hW : ∀ k ∈ d.word, k.val.val ∈ I)
      (tail : Sequence A I d.liveSet T) : Sequence A I U T

namespace Sequence
variable {X : Type*} [DecidableEq X] {A : Matrix X X ℤ} {I U T R : Set X}

theorem trans (h : Sequence A I U T) (g : Sequence A I T R) : Sequence A I U R := by
  induction h with
  | nil => exact g
  | cons d hs hw tail ih => exact .cons d hs hw (ih g)

theorem subset (h : Sequence A I U T) : T ⊆ U := by
  induction h with
  | nil => exact Set.Subset.rfl
  | cons d hs hw tail ih =>
    intro x hx
    exact (ih hx).1

theorem deleted_interior (h : Sequence A I U T) : U \ T ⊆ I := by
  induction h with
  | nil => simp
  | @cons U T d hs hw tail ih =>
    intro x hx
    by_cases he : x=d.vertex.val
    · simpa [he] using hs
    · exact ih ⟨⟨hx.1,he⟩,hx.2⟩

end Sequence
end FgStrip.TriangleShell
