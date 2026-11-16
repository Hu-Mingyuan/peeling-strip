import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Integer matrix mutation

The convention is target-theorem, Section 2, equation (3): positive entries
count arrows from the row vertex to the column vertex. Words act in listed order.
No finiteness assumption is needed for these entrywise identities.
-/

namespace FgStrip

universe u v w

/-- Entrywise skew symmetry of an integer matrix. -/
def SkewSymmetric {V : Type u} (B : Matrix V V ℤ) : Prop :=
  ∀ i j, B i j = -B j i

/-- The positive part used in the manuscript's mutation formula. -/
def posPart (a : ℤ) : ℤ := max a 0

/-- The correction to an entry away from the pivot. -/
def mutationTerm (a b : ℤ) : ℤ :=
  posPart a * posPart b - posPart (-a) * posPart (-b)

lemma mutationTerm_neg (a b : ℤ) :
    mutationTerm (-a) (-b) = -mutationTerm a b := by
  simp only [mutationTerm, neg_neg]
  ring

lemma mutationTerm_swap (a b : ℤ) : mutationTerm b a = mutationTerm a b := by
  simp only [mutationTerm]
  ring

/-- Fomin--Zelevinsky mutation with the exact positive-part convention. -/
def mutate {V : Type u} [DecidableEq V] (B : Matrix V V ℤ) (k : V) : Matrix V V ℤ :=
  fun i j => if i = k ∨ j = k then -B i j
    else B i j + mutationTerm (B i k) (B k j)

@[simp] theorem mutate_row {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (k j : V) : mutate B k k j = -B k j := by
  simp [mutate]

@[simp] theorem mutate_col {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (k i : V) : mutate B k i k = -B i k := by
  simp [mutate]

theorem mutate_of_ne {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (k i j : V) (hi : i ≠ k) (hj : j ≠ k) :
    mutate B k i j = B i j + posPart (B i k) * posPart (B k j) -
      posPart (-B i k) * posPart (-B k j) := by
  simp [mutate, hi, hj, mutationTerm]
  ring

theorem SkewSymmetric.mutate {V : Type u} [DecidableEq V]
    {B : Matrix V V ℤ} (hB : SkewSymmetric B) (k : V) :
    SkewSymmetric (mutate B k) := by
  intro i j
  by_cases hi : i = k
  · subst i
    simp only [mutate_row, mutate_col, neg_neg]
    exact (hB j k).symm
  by_cases hj : j = k
  · subst j
    simp only [mutate_row, mutate_col, neg_neg]
    exact (hB k i).symm
  simp only [FgStrip.mutate, hi, hj, false_or, ite_false]
  rw [hB j i, hB j k, hB k i, mutationTerm_neg, mutationTerm_swap]
  ring

@[simp] theorem mutate_involutive {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (k : V) : mutate (mutate B k) k = B := by
  funext i j
  by_cases hi : i = k
  · subst i
    simp
  by_cases hj : j = k
  · subst j
    simp
  simp only [mutate, hi, hj, false_or, ite_false, or_true, ite_true,
    true_or, mutationTerm_neg]
  ring

/-- Reversing all arrows commutes with mutation. -/
theorem mutate_neg {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (k : V) : mutate (-B) k = -mutate B k := by
  funext i j
  simp only [mutate, Matrix.neg_apply]
  split_ifs
  · rfl
  · rw [mutationTerm_neg]
    ring

/-- Restriction or reindexing along a map, using the standard matrix submatrix. -/
def restrictMatrix {V : Type u} {W : Type v}
    (B : Matrix V V ℤ) (f : W → V) : Matrix W W ℤ := B.submatrix f f

@[simp] theorem restrictMatrix_apply {V : Type u} {W : Type v}
    (B : Matrix V V ℤ) (f : W → V) (i j : W) :
    restrictMatrix B f i j = B (f i) (f j) := rfl

theorem SkewSymmetric.restrictMatrix {V : Type u} {W : Type v}
    {B : Matrix V V ℤ} (hB : SkewSymmetric B) (f : W → V) :
    SkewSymmetric (restrictMatrix B f) := fun i j => hB (f i) (f j)

@[simp] theorem restrictMatrix_comp {V : Type u} {W : Type v} {X : Type w}
    (B : Matrix V V ℤ) (f : W → V) (g : X → W) :
    restrictMatrix (restrictMatrix B f) g = restrictMatrix B (f ∘ g) := rfl

/-- Every retained pivot commutes with injective restriction. -/
theorem restrictMatrix_mutate {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (B : Matrix V V ℤ)
    (f : W → V) (hf : Function.Injective f) (k : W) :
    restrictMatrix (mutate B (f k)) f = mutate (restrictMatrix B f) k := by
  funext i j
  simp only [restrictMatrix_apply, mutate, hf.eq_iff]

/-- A word acts from left to right, in the listed order. -/
def mutateWord {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) : List V → Matrix V V ℤ
  | [] => B
  | k :: W => mutateWord (mutate B k) W

@[simp] theorem mutateWord_nil {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) : mutateWord B [] = B := rfl

@[simp] theorem mutateWord_cons {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (k : V) (W : List V) :
    mutateWord B (k :: W) = mutateWord (mutate B k) W := rfl

theorem mutateWord_append {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (W₁ W₂ : List V) :
    mutateWord B (W₁ ++ W₂) = mutateWord (mutateWord B W₁) W₂ := by
  induction W₁ generalizing B with
  | nil => rfl
  | cons k W ih => exact ih (mutate B k)

/-- Reversing a word undoes it, with no skew-symmetry hypothesis needed. -/
@[simp] theorem mutateWord_reverse {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (W : List V) :
    mutateWord (mutateWord B W) W.reverse = B := by
  induction W generalizing B with
  | nil => rfl
  | cons k W ih =>
    simp only [mutateWord_cons, List.reverse_cons, mutateWord_append,
      ih, mutateWord_nil, mutate_involutive]

theorem SkewSymmetric.mutateWord {V : Type u} [DecidableEq V]
    {B : Matrix V V ℤ} (hB : SkewSymmetric B) (W : List V) :
    SkewSymmetric (mutateWord B W) := by
  induction W generalizing B with
  | nil => exact hB
  | cons k W ih => exact ih (hB.mutate k)

theorem mutateWord_neg {V : Type u} [DecidableEq V]
    (B : Matrix V V ℤ) (W : List V) : mutateWord (-B) W = -mutateWord B W := by
  induction W generalizing B with
  | nil => rfl
  | cons k W ih => simp only [mutateWord_cons, mutate_neg, ih]

theorem restrictMatrix_mutateWord {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (B : Matrix V V ℤ)
    (f : W → V) (hf : Function.Injective f) (L : List W) :
    restrictMatrix (mutateWord B (L.map f)) f =
      mutateWord (restrictMatrix B f) L := by
  induction L generalizing B with
  | nil => rfl
  | cons k L ih =>
    simp only [List.map_cons, mutateWord_cons, ih, restrictMatrix_mutate B f hf]

/-- Reindexing by an equivalence is a special case of injective restriction. -/
theorem reindex_mutateWord {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (B : Matrix V V ℤ) (e : W ≃ V) (L : List W) :
    restrictMatrix (mutateWord B (L.map e)) e =
      mutateWord (restrictMatrix B e) L :=
  restrictMatrix_mutateWord B e e.injective L

/-- A zero row in a skew matrix is also a zero column. -/
theorem SkewSymmetric.col_zero {V : Type u} {E : Matrix V V ℤ}
    (hE : SkewSymmetric E) {k : V} (hk : ∀ j, E k j = 0) : ∀ i, E i k = 0 := by
  intro i
  rw [hE i k, hk i, neg_zero]

/-- The complementary block of `E` is arbitrary. Only the pivot row vanishes. -/
theorem mutate_add_of_row_zero {V : Type u} [DecidableEq V]
    (B E : Matrix V V ℤ) (hE : SkewSymmetric E) (k : V)
    (hk : ∀ j, E k j = 0) : mutate (B + E) k = mutate B k + E := by
  have hc := hE.col_zero hk
  funext i j
  by_cases hi : i = k
  · subst i
    simp [Matrix.add_apply, hk]
  by_cases hj : j = k
  · subst j
    simp [Matrix.add_apply, hc]
  simp only [mutate, hi, hj, false_or, ite_false, Matrix.add_apply, hk, hc, add_zero]
  ring

/-- An arbitrary word supported on zero rows leaves the additive matrix unchanged. -/
theorem mutateWord_add_of_rows_zero {V : Type u} [DecidableEq V]
    (B E : Matrix V V ℤ) (hE : SkewSymmetric E) (W : List V)
    (hW : ∀ k ∈ W, ∀ j, E k j = 0) :
    mutateWord (B + E) W = mutateWord B W + E := by
  induction W generalizing B with
  | nil => rfl
  | cons k W ih =>
    simp only [mutateWord_cons]
    rw [mutate_add_of_row_zero B E hE k (hW k (List.mem_cons_self ..))]
    exact ih (mutate B k) (fun l hl => hW l (List.mem_cons_of_mem k hl))

/-- Set-supported form of additive invariance. -/
theorem mutateWord_add_of_support {V : Type u} [DecidableEq V]
    (B E : Matrix V V ℤ) (hE : SkewSymmetric E) (I : Set V)
    (hI : ∀ k ∈ I, ∀ j, E k j = 0) (W : List V) (hW : ∀ k ∈ W, k ∈ I) :
    mutateWord (B + E) W = mutateWord B W + E :=
  mutateWord_add_of_rows_zero B E hE W (fun k hk => hI k (hW k hk))

end FgStrip
