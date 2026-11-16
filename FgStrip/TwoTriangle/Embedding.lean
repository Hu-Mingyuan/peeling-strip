import FgStrip.TwoTriangle.Cycles

namespace FgStrip.TwoTriangle
open Triangle

/-- All adjacent pairs: common edges `2*i+1` and `2*i+2`, respectively. -/
inductive Pair (N : ℕ)
  | odd (i : Fin N)
  | even (i : Fin N) (next : i.val+1 < N)
namespace Pair
variable {n N : ℕ}
def faceX : Pair N → Strip.Face N
  | .odd i => (i, false)
  | .even i _ => (i, true)
def faceY : Pair N → Strip.Face N
  | .odd i => (i, true)
  | .even i h => (⟨i.val+1,h⟩, false)
def tx : Pair N → Triangle.Vertex n → Triangle.Vertex n
  | .odd _ => id
  | .even _ _ => swap
def ty : Pair N → Triangle.Vertex n → Triangle.Vertex n
  | .odd _ => rot
  | .even _ _ => swap ∘ rot
def gx (s : Pair N) (p : Triangle.Vertex n) : Strip.Glued n N := Strip.glue s.faceX (s.tx p)
def gy (s : Pair N) (p : Triangle.Vertex n) : Strip.Glued n N := Strip.glue s.faceY (s.ty p)

theorem faces_ne (s : Pair N) : s.faceX ≠ s.faceY := by
  cases s <;> simp [faceX, faceY]
theorem tx_injective (s : Pair N) : Function.Injective (s.tx (n := n)) := by
  cases s
  · exact Function.injective_id
  · intro p q h; simpa only [tx, ty, Function.comp_apply, swap_swap] using congrArg swap h
theorem ty_injective (s : Pair N) : Function.Injective (s.ty (n := n)) := by
  have hr : Function.Injective (@rot n) := by
    intro p q h; simpa only [Function.comp_apply, rot_rot_rot] using congrArg (rot ∘ rot) h
  cases s
  · exact hr
  · intro p q h; apply hr; simpa only [tx, ty, Function.comp_apply, swap_swap] using congrArg swap h

theorem gx_injective (s : Pair N) : Function.Injective (s.gx (n := n)) :=
  (Strip.glue_injective s.faceX).comp s.tx_injective
theorem gy_injective (s : Pair N) : Function.Injective (s.gy (n := n)) :=
  (Strip.glue_injective s.faceY).comp s.ty_injective

theorem gx_eq_gy_iff (s : Pair N) (p q : Triangle.Vertex n) :
    s.gx p = s.gy q ↔ x p = y q := by
  rw [x_eq_y_iff]
  have hp := p.total; have hq := q.total
  cases s with
  | odd i =>
    change Strip.glue (i,false) p = Strip.glue (i,true) (rot q) ↔ _
    rw [Strip.glue_opposite_iff]
    simp only [rot, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
      true_and]
    omega
  | even i h =>
    change Strip.glue (i,true) (swap p) = Strip.glue (⟨i.val+1,h⟩,false) (swap (rot q)) ↔ _
    rw [eq_comm, Strip.glue_opposite_iff]
    simp only [swap, rot, Triangle.Vertex.mk_a, Triangle.Vertex.mk_b, Triangle.Vertex.mk_c,
      Fin.ext_iff, true_and]
    omega

theorem gx_mixed (s : Pair N) (p : Triangle.Vertex n) :
    Strip.Mixed (Strip.weight (s.gx p)) ↔ 0 < p.c := by
  cases s <;> simp [gx, Strip.mixed_localWeight_iff, tx, swap]
theorem gy_mixed (s : Pair N) (p : Triangle.Vertex n) :
    Strip.Mixed (Strip.weight (s.gy p)) ↔ 0 < p.a := by
  cases s <;> simp [gy, Strip.mixed_localWeight_iff, ty, rot, swap]

def embed (s : Pair N) (u : Grid n) : Strip.Vertex n N :=
  ⟨if h : u.j ≤ u.i then s.gx (u.lower h) else s.gy (u.upper (by omega)), by
    split
    · exact (s.gx_mixed _).mpr u.j_pos
    · exact (s.gy_mixed _).mpr (by dsimp [Grid.upper]; have := u.j_lt; omega)⟩

theorem gx_eq_embed_iff (s : Pair N) (p : Triangle.Vertex n) (u : Grid n) :
    s.gx p = (s.embed u).1 ↔ x p = u.1 := by
  simp only [embed]
  split <;> rename_i h
  · rw [s.gx_injective.eq_iff, ← u.x_lower h, x_injective.eq_iff]
  · rw [s.gx_eq_gy_iff, u.y_upper]

theorem gy_eq_embed_iff (s : Pair N) (p : Triangle.Vertex n) (u : Grid n) :
    s.gy p = (s.embed u).1 ↔ y p = u.1 := by
  simp only [embed]
  split <;> rename_i h
  · rw [eq_comm, s.gx_eq_gy_iff, u.x_lower, eq_comm]
  · rw [s.gy_injective.eq_iff, ← u.y_upper (show u.i ≤ u.j by omega), y_injective.eq_iff]

theorem embed_injective (s : Pair N) : Function.Injective (s.embed (n := n)) := by
  intro u v h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  rcases u.covered with ⟨p, _, hp⟩ | ⟨p, _, hp⟩
  · have he := (s.gx_eq_embed_iff p u).mpr hp
    exact hp.symm.trans ((s.gx_eq_embed_iff p v).mp (he.trans hh))
  · have he := (s.gy_eq_embed_iff p u).mpr hp
    exact hp.symm.trans ((s.gy_eq_embed_iff p v).mp (he.trans hh))

def embedding (s : Pair N) : Grid n ↪ Strip.Vertex n N := ⟨s.embed, s.embed_injective⟩

/-- The image consists exactly of the retained vertices of these two faces. -/
theorem mem_range_embed_iff (s : Pair N) (v : Strip.Vertex n N) :
    v ∈ Set.range s.embed ↔
      (∃ p, s.gx p = v.1) ∨ (∃ p, s.gy p = v.1) := by
  constructor
  · rintro ⟨u, rfl⟩
    rcases u.covered with ⟨p, _, hp⟩ | ⟨p, _, hp⟩
    · exact Or.inl ⟨p, (s.gx_eq_embed_iff p u).mpr hp⟩
    · exact Or.inr ⟨p, (s.gy_eq_embed_iff p u).mpr hp⟩
  · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
    · have hm : Strip.Mixed (Strip.weight (s.gx p)) := hp.symm ▸ v.2
      let u : Grid n := ⟨x p, (x_retained_iff p).mpr ((s.gx_mixed p).mp hm)⟩
      refine ⟨u, Subtype.ext ?_⟩
      exact ((s.gx_eq_embed_iff p u).mpr rfl).symm.trans hp
    · have hm : Strip.Mixed (Strip.weight (s.gy p)) := hp.symm ▸ v.2
      let u : Grid n := ⟨y p, (y_retained_iff p).mpr ((s.gy_mixed p).mp hm)⟩
      refine ⟨u, Subtype.ext ?_⟩
      exact ((s.gy_eq_embed_iff p u).mpr rfl).symm.trans hp
end Pair
end FgStrip.TwoTriangle
