import FgStrip.Mutation

/-!
# Deletion and undo

A deletion move is a word of present vertices different from the deletion vertex,
a source or sink condition on the entire live set, and the resulting operation.
The equality of its output with restriction is proved, not a field of the move.
-/

namespace FgStrip

universe u v

/-- A source is tested against every vertex of the matrix's index type. -/
def IsSource {V : Type u} (B : Matrix V V ℤ) (s : V) : Prop := ∀ v, 0 ≤ B s v

/-- A sink is tested against every vertex of the matrix's index type. -/
def IsSink {V : Type u} (B : Matrix V V ℤ) (s : V) : Prop := ∀ v, B s v ≤ 0

/-- Either sign is uniform over the entire row, including ambient vertices. -/
def SourceOrSink {V : Type u} (B : Matrix V V ℤ) (s : V) : Prop :=
  IsSource B s ∨ IsSink B s

theorem SourceOrSink.neg {V : Type u} {B : Matrix V V ℤ} {s : V}
    (h : SourceOrSink B s) : SourceOrSink (-B) s := by
  rcases h with h | h
  · exact Or.inr (fun v => neg_nonpos.mpr (h v))
  · exact Or.inl (fun v => neg_nonneg.mpr (h v))

theorem SourceOrSink.restrictMatrix {V : Type u} {W : Type v}
    {B : Matrix V V ℤ} (f : W → V) (s : W) (h : SourceOrSink B (f s)) :
    SourceOrSink (restrictMatrix B f) s := by
  rcases h with h | h
  · exact Or.inl (fun v => h (f v))
  · exact Or.inr (fun v => h (f v))

/-- All vertices except `s`; the type excludes `s` from every subsequent pivot. -/
abbrev Remaining {V : Type u} (s : V) := {v : V // v ≠ s}

/-- Mutate in the original set, delete `s`, then perform the reversed surviving word. -/
def deletionUndo {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (s : V) (W : List (Remaining s)) :
    Matrix (Remaining s) (Remaining s) ℤ :=
  mutateWord (restrictMatrix (mutateWord B (W.map Subtype.val)) Subtype.val) W.reverse

/-- The exact retained matrix is restored, independently of the sign condition. -/
theorem deletionUndo_eq_restrict {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (s : V) (W : List (Remaining s)) :
    deletionUndo B s W = restrictMatrix B Subtype.val := by
  unfold deletionUndo
  rw [restrictMatrix_mutateWord B Subtype.val Subtype.val_injective W]
  exact mutateWord_reverse _ W

/-- General form: delete any vertices outside the image of an injective map. -/
theorem restriction_undo {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (B : Matrix V V ℤ)
    (f : W → V) (hf : Function.Injective f) (L : List W) :
    mutateWord (restrictMatrix (mutateWord B (L.map f)) f) L.reverse =
      restrictMatrix B f := by
  rw [restrictMatrix_mutateWord B f hf L, mutateWord_reverse]

/-- The full source/sink test after a word surviving the deletion of `s`. -/
def ValidDeletionWord {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (s : V) (W : List (Remaining s)) : Prop :=
  SourceOrSink (mutateWord B (W.map Subtype.val)) s

theorem ValidDeletionWord.neg {V : Type u} [DecidableEq V]
    {B : Matrix V V ℤ} {s : V} {W : List (Remaining s)}
    (h : ValidDeletionWord B s W) : ValidDeletionWord (-B) s W := by
  unfold ValidDeletionWord at *
  rw [mutateWord_neg]
  exact h.neg

/-- A deletion row with no additive term is unchanged throughout a supported word. -/
theorem mutateWord_add_row {V : Type u} [DecidableEq V]
    (B E : Matrix V V ℤ) (hE : SkewSymmetric E) (W : List V)
    (hW : ∀ k ∈ W, ∀ j, E k j = 0) (s : V) (hs : ∀ j, E s j = 0) :
    ∀ j, mutateWord (B + E) W s j = mutateWord B W s j := by
  intro j
  rw [mutateWord_add_of_rows_zero B E hE W hW]
  simp [Matrix.add_apply, hs]

/-- Ambient validity requires the whole deletion row of `E` to vanish as well. -/
theorem validDeletionWord_add_iff {V : Type u} [DecidableEq V]
    (B E : Matrix V V ℤ) (hE : SkewSymmetric E) (s : V)
    (W : List (Remaining s))
    (hW : ∀ k ∈ W, ∀ j, E k.val j = 0) (hs : ∀ j, E s j = 0) :
    ValidDeletionWord (B + E) s W ↔ ValidDeletionWord B s W := by
  have hw : ∀ k ∈ W.map Subtype.val, ∀ j, E k j = 0 := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
    exact hW l hl
  have hr := mutateWord_add_row B E hE (W.map Subtype.val) hw s hs
  simp only [ValidDeletionWord, SourceOrSink, IsSource, IsSink, hr]

/-- Injective transport of a word avoiding its deletion vertex. -/
def mapRemaining {V : Type u} {W : Type v} (f : W → V)
    (hf : Function.Injective f) (s : W) : Remaining s → Remaining (f s) :=
  fun k => ⟨f k.val, fun h => k.property (hf h)⟩

/-- Further restriction preserves validity when it retains the word and deletion vertex. -/
theorem validDeletionWord_restrict {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (B : Matrix V V ℤ)
    (f : W → V) (hf : Function.Injective f) (s : W) (L : List (Remaining s))
    (h : ValidDeletionWord B (f s) (L.map (mapRemaining f hf s))) :
    ValidDeletionWord (restrictMatrix B f) s L := by
  have hm : (L.map (mapRemaining f hf s)).map Subtype.val =
      (L.map Subtype.val).map f := by
    simp only [List.map_map]
    rfl
  unfold ValidDeletionWord at *
  rw [hm] at h
  have hr := h.restrictMatrix f s
  rw [restrictMatrix_mutateWord B f hf (L.map Subtype.val)] at hr
  exact hr

/-- A move on the explicit live set `U`. Its sign test includes all of `U`.
The structure supplies a candidate word and its sign proof; it asserts no existence. -/
structure DeletionMove {V : Type u} [DecidableEq V]
    (U : Set V) (B : Matrix U U ℤ) where
  vertex : U
  word : List (Remaining vertex)
  source_or_sink : ValidDeletionWord B vertex word

namespace DeletionMove

variable {V : Type u} [DecidableEq V] {U : Set V} {B : Matrix U U ℤ}

/-- Each forward and reverse pivot is live and distinct from the deleted vertex. -/
theorem pivot_live (d : DeletionMove U B) (k : Remaining d.vertex) :
    k.val.val ∈ U ∧ k.val.val ≠ d.vertex.val := by
  refine ⟨k.val.property, ?_⟩
  intro h
  exact k.property (Subtype.ext h)

/-- The final live subset of the original ambient type. -/
def liveSet (d : DeletionMove U B) : Set V := {v | v ∈ U ∧ v ≠ d.vertex.val}

/-- Identification of surviving live vertices with the explicit final subset. -/
def remainingEquiv (d : DeletionMove U B) : Remaining d.vertex ≃ d.liveSet where
  toFun k := ⟨k.val.val, d.pivot_live k⟩
  invFun k := ⟨⟨k.val, k.property.1⟩, fun h => k.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual mutate/delete/reverse operation, not a preassigned restriction. -/
def output (d : DeletionMove U B) : Matrix (Remaining d.vertex) (Remaining d.vertex) ℤ :=
  deletionUndo B d.vertex d.word

theorem output_eq_restrict (d : DeletionMove U B) :
    d.output = restrictMatrix B Subtype.val :=
  deletionUndo_eq_restrict B d.vertex d.word

theorem output_skew (d : DeletionMove U B) (hB : SkewSymmetric B) :
    SkewSymmetric d.output := by
  rw [d.output_eq_restrict]
  exact hB.restrictMatrix Subtype.val

/-- An empty word defines a move whenever the present vertex is already a source or sink. -/
def ofSourceOrSink (s : U) (h : SourceOrSink B s) : DeletionMove U B :=
  ⟨s, [], h⟩

/-- Arrow reversal interchanges source and sink while retaining the same word. -/
def neg (d : DeletionMove U B) : DeletionMove U (-B) :=
  ⟨d.vertex, d.word, d.source_or_sink.neg⟩

/-- Every completed move on a restriction restores the original ambient entries. -/
theorem output_original (A : Matrix V V ℤ)
    (d : DeletionMove U (restrictMatrix A Subtype.val))
    (i j : Remaining d.vertex) : d.output i j = A i.val.val j.val.val := by
  rw [d.output_eq_restrict]
  rfl

end DeletionMove

end FgStrip
