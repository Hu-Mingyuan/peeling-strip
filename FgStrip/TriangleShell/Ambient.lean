import FgStrip.TriangleShell.Sequence

namespace FgStrip.TriangleShell

/-- Extend a local matrix by zero to arbitrary exterior vertices. -/
def extendMatrix {V F : Type*} (B : Matrix V V ℤ) : Matrix (V ⊕ F) (V ⊕ F) ℤ
  | .inl i, .inl j => B i j
  | _, _ => 0

theorem mutate_extendMatrix {V F : Type*} [DecidableEq V] [DecidableEq F]
    (B : Matrix V V ℤ) (k : V) :
    mutate (extendMatrix (F := F) B) (.inl k) = extendMatrix (mutate B k) := by
  funext i j
  cases i <;> cases j <;>
    simp [mutate, extendMatrix, mutationTerm, posPart]

theorem mutateWord_extendMatrix {V F : Type*} [DecidableEq V] [DecidableEq F]
    (B : Matrix V V ℤ) (W : List V) :
    mutateWord (extendMatrix (F := F) B) (W.map Sum.inl) = extendMatrix (mutateWord B W) := by
  induction W generalizing B with
  | nil => rfl
  | cons k W ih =>
    simp only [List.map_cons, mutateWord_cons, mutate_extendMatrix, ih]

/-- Validity quantifies over the exterior vertices as well as every local side vertex. -/
theorem validDeletionWord_extend {V F : Type*} [DecidableEq V] [DecidableEq F]
    {B : Matrix V V ℤ} {s : V} {W : List (Remaining s)}
    (h : ValidDeletionWord B s W) :
    ValidDeletionWord (extendMatrix (F := F) B) (.inl s)
      (W.map (mapRemaining Sum.inl Sum.inl_injective s)) := by
  unfold ValidDeletionWord at *
  have hmap : (W.map (mapRemaining (Sum.inl : V → V ⊕ F) Sum.inl_injective s)).map Subtype.val =
      (W.map Subtype.val).map Sum.inl := by
    simp only [List.map_map]
    rfl
  rw [hmap, mutateWord_extendMatrix]
  rcases h with h | h
  · left
    intro j
    cases j with
    | inl j => exact h j
    | inr j => exact le_refl 0
  · right
    intro j
    cases j with
    | inl j => exact h j
    | inr j => exact le_refl 0

/-- Extension followed by a skew complementary-block addition preserves any
concrete word whose target and pivots have zero additive rows. -/
theorem validDeletionWord_ambient {V F : Type*} [DecidableEq V] [DecidableEq F]
    {B : Matrix V V ℤ} {s : V} {W : List (Remaining s)}
    (h : ValidDeletionWord B s W) (E : Matrix (V ⊕ F) (V ⊕ F) ℤ)
    (hE : SkewSymmetric E) (hs : ∀ j, E (.inl s) j=0)
    (hW : ∀ k ∈ W, ∀ j, E (.inl k.val) j=0) :
    ValidDeletionWord (extendMatrix B + E) (.inl s)
      (W.map (mapRemaining Sum.inl Sum.inl_injective s)) := by
  apply (validDeletionWord_add_iff _ E hE _ _ ?_ hs).mpr
  · exact validDeletionWord_extend h
  · intro k hk j
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
    exact hW l hl j

/-- The concrete first-family word remains valid with arbitrary side/exterior
attachments. No condition is imposed on the complementary block of `E`. -/
theorem firstWord_ambient {n p a : ℕ} (hn : 2*p+1 ≤ n) (ha : 1 ≤ a) (hap : a ≤ p)
    {F : Type*} [DecidableEq F]
    (E : Matrix (firstLive (n := n) p a ⊕ F) (firstLive p a ⊕ F) ℤ)
    (hE : SkewSymmetric E)
    (hzero : ∀ k : firstLive (n := n) p a, k.val ∈ interiorSet n →
      ∀ j, E (.inl k) j=0) :
    ValidDeletionWord (extendMatrix (restrictMatrix (Triangle.matrix n) Subtype.val) + E)
      (.inl (firstMove hn ha hap).vertex)
      ((firstMove hn ha hap).word.map
        (mapRemaining Sum.inl Sum.inl_injective (firstMove hn ha hap).vertex)) := by
  apply validDeletionWord_ambient (firstMove hn ha hap).source_or_sink E hE
  · exact hzero _ (firstMove_target_interior hn ha hap)
  · intro k hk
    exact hzero _ (firstMove_word_coordinates hn ha hap k hk).2

/-- Restrict the ambient move by any injection retaining its target and word.
This combines arbitrary additional deletions with arbitrary ambient attachments. -/
theorem validDeletionWord_ambient_restrict {V F T : Type*}
    [DecidableEq V] [DecidableEq F] [DecidableEq T]
    {B : Matrix V V ℤ} {s : V} {W : List (Remaining s)}
    (h : ValidDeletionWord B s W) (E : Matrix (V ⊕ F) (V ⊕ F) ℤ)
    (hE : SkewSymmetric E) (hs : ∀ j, E (.inl s) j=0)
    (hW : ∀ k ∈ W, ∀ j, E (.inl k.val) j=0)
    (f : T → V ⊕ F) (hf : Function.Injective f) (t : T) (ht : f t=Sum.inl s)
    (L : List (Remaining t))
    (hL : (L.map Subtype.val).map f = (W.map Subtype.val).map Sum.inl) :
    ValidDeletionWord (restrictMatrix (extendMatrix B+E) f) t L := by
  have hv := validDeletionWord_ambient h E hE hs hW
  unfold ValidDeletionWord at *
  have hmap : (W.map (mapRemaining (Sum.inl : V → V ⊕ F) Sum.inl_injective s)).map Subtype.val =
      (W.map Subtype.val).map Sum.inl := by
    simp only [List.map_map]
    rfl
  rw [hmap, ← hL, ← ht] at hv
  have hr := hv.restrictMatrix f t
  rw [restrictMatrix_mutateWord _ f hf] at hr
  exact hr

end FgStrip.TriangleShell
