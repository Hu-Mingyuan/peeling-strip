import FgStrip.TriangleShell.Ambient

namespace FgStrip.TriangleShell

/-- The actual deletion/undo output reindexed by the explicit next live set. -/
def stepOutput {X : Type*} [DecidableEq X] {U : Set X} {B : Matrix U U ℤ}
    (d : DeletionMove U B) : Matrix d.liveSet d.liveSet ℤ :=
  restrictMatrix d.output d.remainingEquiv.symm

theorem stepOutput_original {X : Type*} [DecidableEq X]
    (A : Matrix X X ℤ) {U : Set X} (d : DeletionMove U (restrictMatrix A Subtype.val)) :
    stepOutput d = restrictMatrix A Subtype.val := by
  funext i j
  exact d.output_original A (d.remainingEquiv.symm i) (d.remainingEquiv.symm j)

/-- Actual successive operations. Unlike `Sequence`, the input of each next step
is defined as the preceding step's mutate/delete/reverse output. -/
inductive Execution {X : Type*} [DecidableEq X] (I : Set X) :
    {U T : Set X} → Matrix U U ℤ → Matrix T T ℤ → Prop
  | nil {U : Set X} (B : Matrix U U ℤ) : Execution I (U := U) (T := U) B B
  | cons {U T : Set X} {B : Matrix U U ℤ} {C : Matrix T T ℤ}
      (d : DeletionMove U B) (hs : d.vertex.val ∈ I)
      (hW : ∀ k ∈ d.word, k.val.val ∈ I)
      (tail : Execution I (stepOutput d) C) : Execution I B C

/-- Every sequence of concrete moves runs to exactly the original restricted matrix. -/
theorem Sequence.execution {X : Type*} [DecidableEq X] {A : Matrix X X ℤ}
    {I U T : Set X} (h : Sequence A I U T) :
    Execution I (restrictMatrix A (Subtype.val : U → X))
      (restrictMatrix A (Subtype.val : T → X)) := by
  induction h with
  | nil => exact .nil _
  | cons d hs hw tail ih =>
    apply Execution.cons d hs hw
    rw [stepOutput_original]
    exact ih

/-- A supported sequence permits arbitrary skew additions away from its support. -/
theorem Sequence.add {X : Type*} [DecidableEq X] {A : Matrix X X ℤ}
    {I U T : Set X} (h : Sequence A I U T) (E : Matrix X X ℤ)
    (hE : SkewSymmetric E) (hz : ∀ k ∈ I, ∀ j, E k j=0) :
    Sequence (A+E) I U T := by
  induction h with
  | nil => exact .nil _
  | @cons U T d hs hw tail ih =>
    let e := addMove d (restrictMatrix E Subtype.val) (hE.restrictMatrix Subtype.val)
      (fun j => hz d.vertex.val hs j.val)
      (fun k hk j => hz k.val.val (hw k hk) j.val)
    apply Sequence.cons e hs hw
    exact ih

end FgStrip.TriangleShell
