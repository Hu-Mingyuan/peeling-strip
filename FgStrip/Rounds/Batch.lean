import FgStrip.Rounds.ProfileUpdates

namespace FgStrip.Rounds
open TriangleShell TwoTriangle

/-- Raise exactly a finite set of depth entries. -/
def raised {X : Type*} [DecidableEq X] (d : X → ℕ) (S : Finset X) (p : ℕ) : X → ℕ :=
  fun x => if x ∈ S then p+1 else d x

@[simp] theorem raised_empty {X : Type*} [DecidableEq X] (d : X → ℕ) (p : ℕ) :
    raised d ∅ p=d := by funext x; simp [raised]

theorem raised_insert {X : Type*} [DecidableEq X] (d : X → ℕ) (S : Finset X)
    (p : ℕ) (x : X) :
    Function.update (raised d S p) x (p+1)=raised d (insert x S) p := by
  funext y
  by_cases hy : y=x
  · subst y; simp [raised]
  · simp [Function.update_of_ne hy,raised,hy]

/-- Independent triangle shells compose on their exact successive profiles. -/
theorem batch_faces {n N p} (hN : 0 < N) (hp : 1 ≤ p) (hn : 2*p+1 ≤ n)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (S : Finset (Strip.Face N))
    (hS : ∀ f ∈ S, d (faceEdgeA f)=p ∧ d (faceEdgeB f)=p ∧ c f=p) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (profileLive hN d c)
      (profileLive hN d (raised c S p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (Sequence.nil (A := Strip.matrix n N) (I := Strip.internal hN)
      (profileLive hN d c))
  | @insert f S hf ih =>
    have hfirst := ih (fun g hg => hS g (Finset.mem_insert_of_mem hg))
    have hdata := hS f (Finset.mem_insert_self _ _)
    have hcur : raised c S p f=p := by simp [raised,hf,hdata.2.2]
    have hstep := face_profile_step hN hp hn d (raised c S p) f hdata.1 hdata.2.1 hcur
    rw [raised_insert] at hstep
    exact hfirst.trans hstep

/-- Edge layers compose even when previously processed neighbours have greater
depth, since the concrete pair theorem permits arbitrary interface deletions. -/
theorem batch_edges {n N p} (hN : 0 < N) (hp : p<n/2)
    (d : Strip.EdgeIndex N → ℕ) (c : Strip.Face N → ℕ) (S : Finset (Strip.EdgeIndex N))
    (hS : ∀ j ∈ S, ∃ s : Pair N, s.commonEdge=j ∧ d j=p ∧
      p ≤ d s.firstEdge ∧ p ≤ d s.lastEdge ∧ c s.faceX=p+1 ∧ c s.faceY=p+1) :
    Sequence (Strip.matrix n N) (Strip.internal hN) (profileLive hN d c)
      (profileLive hN (raised d S p) c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (Sequence.nil (A := Strip.matrix n N) (I := Strip.internal hN)
      (profileLive hN d c))
  | @insert j S hj ih =>
    have hfirst := ih (fun k hk => hS k (Finset.mem_insert_of_mem hk))
    obtain ⟨s,hs,hd,hl,hr,hx,hy⟩ := hS j (Finset.mem_insert_self _ _)
    have hcur : raised d S p s.commonEdge=p := by simp [raised,hs,hj,hd]
    have hleft : p ≤ raised d S p s.firstEdge := by dsimp [raised]; split_ifs <;> omega
    have hright : p ≤ raised d S p s.lastEdge := by dsimp [raised]; split_ifs <;> omega
    have hstep := edge_profile_step hN hp (raised d S p) c s hcur hleft hright hx hy
    rw [hs,raised_insert] at hstep
    exact hfirst.trans hstep

end FgStrip.Rounds
