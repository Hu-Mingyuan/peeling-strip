import FgStrip.TwoTriangle.Contribution

namespace FgStrip.TwoTriangle
open Triangle
namespace Pair
variable {n N : ℕ}

theorem tx_surjective (s : Pair N) : Function.Surjective (s.tx (n := n)) := by
  intro p
  cases s
  · exact ⟨p,rfl⟩
  · exact ⟨swap p, swap_swap p⟩
theorem ty_surjective (s : Pair N) : Function.Surjective (s.ty (n := n)) := by
  intro p
  cases s
  · exact ⟨rot (rot p), rot_rot_rot p⟩
  · refine ⟨rot (rot (swap p)), ?_⟩
    simp [ty, rot_rot_rot, swap_swap]

theorem contribution_zero_of_not_range (s : Pair N) (u v : Strip.Vertex n N)
    (hu : u ∉ Set.range s.embed) : s.contribution u v = 0 := by
  classical
  have hx : ∀ p : Triangle.Vertex n, u.1 ≠ Strip.glue s.faceX p := by
    intro p hp
    obtain ⟨q,hq⟩ := s.tx_surjective p
    apply hu
    apply (s.mem_range_embed_iff u).mpr
    exact Or.inl ⟨q, by change Strip.glue s.faceX (s.tx q)=u.1; rw [hq]; exact hp.symm⟩
  have hy : ∀ p : Triangle.Vertex n, u.1 ≠ Strip.glue s.faceY p := by
    intro p hp
    obtain ⟨q,hq⟩ := s.ty_surjective p
    apply hu
    apply (s.mem_range_embed_iff u).mpr
    exact Or.inr ⟨q, by change Strip.glue s.faceY (s.ty q)=u.1; rw [hq]; exact hp.symm⟩
  change mapMatrix (Strip.glue s.faceX) u.1 v.1 + mapMatrix (Strip.glue s.faceY) u.1 v.1 = 0
  simp [mapMatrix_eq_sum, cycleEntry, cycleCount, hx, hy]

/-- On the pair interiors and common edge, the selected contribution supplies
all strip entries, including columns outside the pair. -/
theorem strip_row_eq_contribution (s : Pair N) (u : Grid n)
    (hi : 0 < u.i) (hin : u.i < n) (v : Strip.Vertex n N) :
    Strip.matrix n N (s.embed u) v = s.contribution (s.embed u) v := by
  rw [s.strip_decomposition]
  change s.contribution (s.embed u) v + s.remainder (s.embed u) v = _
  rw [s.remainder_row_zero u hi hin v, add_zero]
end Pair
end FgStrip.TwoTriangle
