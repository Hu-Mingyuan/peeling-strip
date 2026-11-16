import FgStrip.CommonEdge.Transport

namespace FgStrip.CommonEdge
open TriangleShell

/-- Retain all exterior vertices while changing the local live set. -/
def ambientLive {X F : Type*} (U : Set X) : Set (X ⊕ F) :=
  {z | match z with | .inl x => x ∈ U | .inr _ => True}

/-- The local support has no exterior vertices. -/
def ambientSupport {X F : Type*} (I : Set X) : Set (X ⊕ F) :=
  {z | match z with | .inl x => x ∈ I | .inr _ => False}

def ambientMap {X F : Type*} {U : Set X} (z : ambientLive (F := F) U) : U ⊕ F :=
  match z with
  | ⟨.inl x,hx⟩ => .inl ⟨x,hx⟩
  | ⟨.inr y,_⟩ => .inr y

def ambientLift {X F : Type*} {U : Set X} : U ⊕ F → ambientLive (F := F) U
  | .inl x => ⟨.inl x.val,x.property⟩
  | .inr y => ⟨.inr y,trivial⟩

@[simp] theorem ambientMap_lift {X F : Type*} {U : Set X} (z : U ⊕ F) :
    ambientMap (ambientLift z)=z := by cases z <;> rfl

@[simp] theorem ambientLift_map {X F : Type*} {U : Set X} (z : ambientLive (F := F) U) :
    ambientLift (ambientMap z)=z := by rcases z with ⟨x,hx⟩; cases x <;> rfl

theorem ambientMap_injective {X F : Type*} {U : Set X} :
    Function.Injective (ambientMap (X := X) (F := F) (U := U)) :=
  Function.LeftInverse.injective ambientLift_map

/-- A supported sequence extends over an arbitrary exterior vertex type. -/
theorem sequence_extend {X F : Type*} [DecidableEq X] [DecidableEq F]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T) :
    Sequence (extendMatrix (F := F) A) (ambientSupport I) (ambientLive U) (ambientLive T) := by
  classical
  induction h with
  | nil => exact .nil _
  | @cons U T d hs hw tail ih =>
    let s : ambientLive (F := F) U := ambientLift (.inl d.vertex)
    let L : List (Remaining s) := d.word.map fun k =>
      ⟨ambientLift (.inl k.val), by
        intro he
        have h := congrArg ambientMap he
        simp only [ambientMap_lift] at h
        exact k.property (Sum.inl.inj h)⟩
    have hm : (L.map Subtype.val).map ambientMap =
        (d.word.map Subtype.val).map Sum.inl := by
      simp only [L, List.map_map, Function.comp_def, ambientMap_lift]
    have hv := validDeletionWord_ambient_restrict d.source_or_sink
      (0 : Matrix (U ⊕ F) (U ⊕ F) ℤ) (by intro i j; simp)
      (by intro j; rfl) (by intro k hk j; rfl)
      ambientMap ambientMap_injective s (ambientMap_lift _) L hm
    have hmtrx : restrictMatrix (extendMatrix (restrictMatrix A Subtype.val)+
        (0 : Matrix (U ⊕ F) (U ⊕ F) ℤ)) ambientMap =
        restrictMatrix (extendMatrix A) (Subtype.val : ambientLive (F := F) U → X ⊕ F) := by
      funext ⟨i,hi⟩ ⟨j,hj⟩
      cases i <;> cases j <;> simp [restrictMatrix, extendMatrix, ambientMap]
    rw [hmtrx] at hv
    let d' : DeletionMove (ambientLive (F := F) U)
        (restrictMatrix (extendMatrix A) Subtype.val) := ⟨s,L,hv⟩
    apply Sequence.cons d'
    · exact hs
    · intro k hk
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hk
      exact hw l hl
    · have hout : d'.liveSet=ambientLive (F := F) d.liveSet := by
        ext z
        cases z <;> simp [DeletionMove.liveSet, d', s, ambientLift, ambientLive]
      rw [hout]
      exact ih

/-- Arbitrary skew attachments survive unchanged on the complementary block. -/
theorem sequence_ambient {X F : Type*} [DecidableEq X] [DecidableEq F]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T)
    (E : Matrix (X ⊕ F) (X ⊕ F) ℤ) (hE : SkewSymmetric E)
    (hz : ∀ x ∈ I, ∀ z, E (.inl x) z=0) :
    Sequence (extendMatrix A+E) (ambientSupport I) (ambientLive U) (ambientLive T) := by
  apply (sequence_extend (F := F) h).add E hE
  intro x hx z
  cases x with
  | inl x => exact hz x hx z
  | inr x => exact False.elim hx

end FgStrip.CommonEdge
