import FgStrip.Rounds
import FgStrip.AmbientTriangulation

namespace FgStrip
open TriangleShell AmbientTriangulation

namespace Proposition74

/-- The prescribed deleted set after the last round. -/
def deleted {n N} (hN : 0 < N) : Set (Strip.Vertex n N) :=
  (Rounds.roundLive hN (n/2))ᶜ

theorem imageLive_compl {X Y : Type*} (i : X ↪ Y) (T : Set X) :
    Rounds.imageLive i T=(i '' Tᶜ)ᶜ := by
  classical
  ext y
  by_cases hr : y ∈ Set.range i
  · obtain ⟨x,rfl⟩ := hr
    rw [Rounds.imageLive_apply]
    simp [i.injective.eq_iff]
  · constructor
    · intro _ hh
      obtain ⟨x,_,he⟩ := hh
      exact hr ⟨x,he⟩
    · intro _
      exact Or.inr hr

/-- The unconditional strip result, before changing the ambient vertex type. -/
theorem strip {n N : ℕ} (hn : 2 ≤ n) (hN : max (n/2) 2 ≤ N) :
    Strip.middle (n := n) (show 0 < N by omega) ⊆ deleted (show 0 < N by omega) ∧
    deleted (n := n) (show 0 < N by omega) ⊆ Strip.internal (show 0 < N by omega) ∧
    Sequence (Strip.matrix n N) (Strip.internal (show 0 < N by omega)) Set.univ
      (deleted (n := n) (show 0 < N by omega))ᶜ := by
  have h := Rounds.rounds hn (show 0 < N by omega) (n/2) (by omega) (by omega)
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact Rounds.middle_not_mem_roundLive (by omega) (by omega) v hv
  · intro v hv
    exact h.deleted_interior ⟨Set.mem_univ v,hv⟩
  · simpa only [deleted,compl_compl] using h

/-- Proposition 7.4 for every permitted rank and strip length, every finite
ambient vertex type and injection, and the full permitted complementary skew
block. Both the supported sequence and its actual execution are supplied. -/
theorem ambient {n N : ℕ} (hn : 2 ≤ n) (hN : max (n/2) 2 ≤ N)
    {V : Type*} [Finite V] [DecidableEq V] (i : Strip.Vertex n N ↪ V)
    (E : Matrix V V ℤ) (hE : SkewSymmetric E)
    (hz : ∀ x ∈ Strip.internal (show 0 < N by omega), ∀ v, E (i x) v=0) :
    ∃ Z : Set V,
      i '' Strip.middle (show 0 < N by omega) ⊆ Z ∧
      Z ⊆ i '' Strip.internal (show 0 < N by omega) ∧
      Sequence (zeroExtension i (Strip.matrix n N)+E)
        (i '' Strip.internal (show 0 < N by omega)) Set.univ Zᶜ ∧
      Execution (i '' Strip.internal (show 0 < N by omega))
        (restrictMatrix (zeroExtension i (Strip.matrix n N)+E) (Subtype.val : Set.univ → V))
        (restrictMatrix (zeroExtension i (Strip.matrix n N)+E) (Subtype.val : ↥(Zᶜ) → V)) := by
  classical
  obtain ⟨hm,hi,hs⟩ := strip hn hN
  have ht := Rounds.sequence_injection hs i E hE hz
  rw [Rounds.imageLive_univ,imageLive_compl,compl_compl] at ht
  refine ⟨i '' deleted (show 0 < N by omega),?_,?_,ht,ht.execution⟩
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨x,hm hx,rfl⟩
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨x,hi hx,rfl⟩

/-- The explicit triangle-incidence application. The actual ambient triangle sum
supplies all matrix hypotheses through `Data.ambient_hypothesis`. -/
theorem triangulation {n N : ℕ} (hn : 2 ≤ n) (hN : max (n/2) 2 ≤ N)
    {X O : Type*} [Fintype O] (d : AmbientTriangulation.Data N X O)
    (hb : d.BoundaryCompatible n) (hi : d.FaceIncidence n) :
    ∃ Z : Set (d.Vertex n),
      d.embedding hb '' Strip.middle (show 0 < N by omega) ⊆ Z ∧
      Z ⊆ d.embedding hb '' Strip.internal (show 0 < N by omega) ∧
      Sequence (d.matrix n) (d.embedding hb '' Strip.internal (show 0 < N by omega)) Set.univ Zᶜ ∧
      Execution (d.embedding hb '' Strip.internal (show 0 < N by omega))
        (restrictMatrix (d.matrix n) (Subtype.val : Set.univ → d.Vertex n))
        (restrictMatrix (d.matrix n) (Subtype.val : ↥(Zᶜ) → d.Vertex n)) := by
  obtain ⟨hm,hsk,hz⟩ := d.ambient_hypothesis hb hi (show 0 < N by omega)
  have h := ambient hn hN (d.embedding hb) (d.exterior n) hsk hz
  rwa [← hm] at h

end Proposition74
end FgStrip
