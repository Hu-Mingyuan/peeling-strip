import FgStrip.CommonEdge
import FgStrip.AmbientTriangulation.Matrix

namespace FgStrip.Rounds
open TriangleShell CommonEdge AmbientTriangulation

/-- Enlarging the allowed support does not change any move. -/
theorem sequence_support_mono {X : Type*} [DecidableEq X]
    {A : Matrix X X ℤ} {I J U T : Set X}
    (h : Sequence A I U T) (hIJ : I ⊆ J) : Sequence A J U T := by
  induction h with
  | nil => exact .nil _
  | cons d hs hw tail ih => exact .cons d (hIJ hs) (fun k hk => hIJ (hw k hk)) ih

/-- Relabel every live set, deletion vertex, and pivot by the same equivalence. -/
theorem sequence_equiv {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T) (f : Y ≃ X) :
    Sequence (restrictMatrix A f) (f ⁻¹' I) (f ⁻¹' U) (f ⁻¹' T) := by
  classical
  induction h with
  | nil => exact .nil _
  | @cons U T d hs hw tail ih =>
    let g : (f ⁻¹' U) → U := fun x => ⟨f x.val,x.property⟩
    have hg : Function.Injective g := by
      intro x y he
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val he)
    let s : (f ⁻¹' U) := ⟨f.symm d.vertex.val, by simpa using d.vertex.property⟩
    have hgs : g s=d.vertex := by apply Subtype.ext; exact f.apply_symm_apply _
    have hW : ∀ k ∈ d.word, ∃ l : (f ⁻¹' U), g l=k.val := by
      intro k hk
      refine ⟨⟨f.symm k.val.val, by simpa using k.val.property⟩, ?_⟩
      apply Subtype.ext
      exact f.apply_symm_apply _
    obtain ⟨e,he,hew⟩ := pullMove d g hg s hgs hW
    change DeletionMove (f ⁻¹' U) (restrictMatrix (restrictMatrix A f) Subtype.val) at e
    apply Sequence.cons e
    · change f e.vertex.val ∈ I
      rw [he]
      simpa [s] using hs
    · intro k hk
      have hm : g k.val ∈ d.word.map Subtype.val := by
        rw [← hew]
        exact List.mem_map.mpr ⟨k.val,List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩
      obtain ⟨l,hl,hel⟩ := List.mem_map.mp hm
      have hv := congrArg Subtype.val hel
      change l.val.val = f k.val.val at hv
      change f k.val.val ∈ I
      rw [← hv]
      exact hw l hl
    · have hout : e.liveSet=f ⁻¹' d.liveSet := by
        ext x
        simp only [DeletionMove.liveSet, Set.mem_setOf_eq, Set.mem_preimage, he]
        change (f x ∈ U ∧ x ≠ f.symm d.vertex.val) ↔
          (f x ∈ U ∧ f x ≠ d.vertex.val)
        simp only [ne_eq, f.eq_symm_apply]
      rw [hout]
      exact ih

/-- Extra deletions need avoid only the initially live supported vertices. -/
theorem sequence_restrict_live {X : Type*} [DecidableEq X] {A : Matrix X X ℤ}
    {I U T : Set X} (h : Sequence A I U T) (F : Set X)
    (hF : ∀ x ∈ I, x ∈ U → x ∉ F) : Sequence A I (U \ F) (T \ F) := by
  classical
  induction h with
  | nil => exact .nil _
  | @cons U T d hs hw tail ih =>
    let f : ↥(U \ F) → U := fun x => ⟨x.val,x.property.1⟩
    have hf : Function.Injective f := by
      intro x y he; apply Subtype.ext; exact congrArg (fun z : U => z.val) he
    let s : ↥(U \ F) := ⟨d.vertex.val,d.vertex.property,hF _ hs d.vertex.property⟩
    have hW : ∀ k ∈ d.word, ∃ l : ↥(U \ F), f l=k.val := by
      intro k hk
      exact ⟨⟨k.val.val,k.val.property,hF _ (hw k hk) k.val.property⟩,rfl⟩
    obtain ⟨e,he,hew⟩ := pullMove d f hf s rfl hW
    change DeletionMove (U \ F) (restrictMatrix A Subtype.val) at e
    apply Sequence.cons e
    · simpa only [he] using hs
    · intro k hk
      have hm : f k.val ∈ d.word.map Subtype.val := by
        rw [← hew]
        exact List.mem_map.mpr ⟨k.val,List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩
      obtain ⟨l,hl,hel⟩ := List.mem_map.mp hm
      have hv := congrArg Subtype.val hel
      simpa only [hv] using hw l hl
    · have hout : e.liveSet=d.liveSet \ F := by
        ext x
        simp only [DeletionMove.liveSet, Set.mem_sdiff, Set.mem_ofPred_eq, he]
        change ((x ∈ U ∧ x ∉ F) ∧ x ≠ d.vertex.val) ↔
          ((x ∈ U ∧ x ≠ d.vertex.val) ∧ x ∉ F)
        tauto
      rw [hout]
      exact ih (fun x hx hxu => hF x hx hxu.1)

/-- Pull a sequence through an injection whose image contains the initial live
set. This removes unused labels from a local coordinate representation. -/
theorem sequence_pull {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T)
    (f : Y ↪ X) (hU : U ⊆ Set.range f) :
    Sequence (restrictMatrix A f) (f ⁻¹' I) (f ⁻¹' U) (f ⁻¹' T) := by
  classical
  induction h with
  | nil => exact .nil _
  | @cons U T d hs hw tail ih =>
    let g : (f ⁻¹' U) → U := fun x => ⟨f x.val,x.property⟩
    have hg : Function.Injective g := by
      intro x y he
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val he)
    obtain ⟨v,hv⟩ := hU d.vertex.property
    let s : (f ⁻¹' U) := ⟨v, by change f v ∈ U; rw [hv]; exact d.vertex.property⟩
    have hgs : g s=d.vertex := Subtype.ext hv
    have hW : ∀ k ∈ d.word, ∃ l : (f ⁻¹' U), g l=k.val := by
      intro k hk
      obtain ⟨w,hw⟩ := hU k.val.property
      refine ⟨⟨w, by change f w ∈ U; rw [hw]; exact k.val.property⟩,Subtype.ext hw⟩
    obtain ⟨e,he,hew⟩ := pullMove d g hg s hgs hW
    change DeletionMove (f ⁻¹' U) (restrictMatrix (restrictMatrix A f) Subtype.val) at e
    apply Sequence.cons e
    · change f e.vertex.val ∈ I
      rw [he]
      change f v ∈ I
      rwa [hv]
    · intro k hk
      have hm : g k.val ∈ d.word.map Subtype.val := by
        rw [← hew]
        exact List.mem_map.mpr ⟨k.val,List.mem_map.mpr ⟨k,hk,rfl⟩,rfl⟩
      obtain ⟨l,hl,hel⟩ := List.mem_map.mp hm
      have hval := congrArg Subtype.val hel
      change l.val.val = f k.val.val at hval
      change f k.val.val ∈ I
      rw [← hval]
      exact hw l hl
    · have hout : e.liveSet=f ⁻¹' d.liveSet := by
        ext x
        simp only [DeletionMove.liveSet, Set.mem_setOf_eq, Set.mem_preimage, he]
        change (f x ∈ U ∧ x ≠ v) ↔ (f x ∈ U ∧ f x ≠ d.vertex.val)
        rw [← hv]
        simp only [ne_eq, f.injective.eq_iff]
      rw [hout]
      exact ih (fun x hx => hU hx.1)

/-- An injection identifies its codomain with the image and its complement. -/
noncomputable def injectionEquiv {X Y : Type*} (i : X ↪ Y) :
    (X ⊕ {y // y ∉ Set.range i}) ≃ Y :=
  Equiv.ofBijective (Sum.elim i Subtype.val) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (i.injective hab)
        | inr b => exact (b.property ⟨a,hab⟩).elim
      | inr a =>
        cases b with
        | inl b => exact (a.property ⟨b,hab.symm⟩).elim
        | inr b => exact congrArg Sum.inr (Subtype.ext hab)
    · intro y
      by_cases hy : y ∈ Set.range i
      · obtain ⟨x,rfl⟩ := hy; exact ⟨.inl x,rfl⟩
      · exact ⟨.inr ⟨y,hy⟩,rfl⟩)

@[simp] theorem injectionEquiv_inl {X Y : Type*} (i : X ↪ Y) (x : X) :
    injectionEquiv i (.inl x)=i x := rfl

@[simp] theorem injectionEquiv_inr {X Y : Type*} (i : X ↪ Y)
    (y : {y // y ∉ Set.range i}) : injectionEquiv i (.inr y)=y.val := rfl

/-- A local live set together with every exterior vertex. -/
def imageLive {X Y : Type*} (i : X ↪ Y) (U : Set X) : Set Y :=
  (i '' U) ∪ (Set.range i)ᶜ

@[simp] theorem imageLive_apply {X Y : Type*} (i : X ↪ Y) (U : Set X) (x : X) :
    i x ∈ imageLive i U ↔ x ∈ U := by
  simp only [imageLive, Set.mem_union, Set.mem_image, Set.mem_compl_iff,
    Set.mem_range, i.injective.eq_iff]
  simp

@[simp] theorem imageLive_univ {X Y : Type*} (i : X ↪ Y) :
    imageLive i Set.univ=Set.univ := by
  ext y
  simp [imageLive]

theorem zeroExtension_equiv {X Y : Type*} (i : X ↪ Y) (A : Matrix X X ℤ) :
    restrictMatrix (zeroExtension i A) (injectionEquiv i) = extendMatrix A := by
  funext x y
  cases x with
  | inl x =>
    cases y with
    | inl y => exact zeroExtension_apply i A x y
    | inr y => exact zeroExtension_col_zero i A (i x) y.val y.property
  | inr x =>
    exact zeroExtension_row_zero i A x.val (injectionEquiv i y) x.property

/-- Transport a concrete local sequence through an arbitrary injection, retaining
all exterior vertices and every entry of the permitted complementary block. -/
theorem sequence_injection {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T)
    (i : X ↪ Y) (E : Matrix Y Y ℤ) (hE : SkewSymmetric E)
    (hz : ∀ x ∈ I, ∀ y, E (i x) y=0) :
    Sequence (zeroExtension i A+E) (i '' I) (imageLive i U) (imageLive i T) := by
  classical
  let e := injectionEquiv i
  have he := sequence_ambient (F := {y // y ∉ Set.range i}) h
    (restrictMatrix E e) (hE.restrictMatrix e) (by
      intro x hx y
      exact hz x hx (e y))
  have hm : extendMatrix A + restrictMatrix E e =
      restrictMatrix (zeroExtension i A+E) e := by
    rw [← zeroExtension_equiv i A]
    rfl
  rw [hm] at he
  have hh := sequence_equiv he e.symm
  have hmat : restrictMatrix (restrictMatrix (zeroExtension i A+E) e) e.symm =
      zeroExtension i A+E := by
    funext x y
    simp [restrictMatrix]
  have hsupport : e.symm ⁻¹' ambientSupport I = i '' I := by
    ext y
    obtain ⟨z,rfl⟩ := e.surjective y
    simp only [Set.mem_preimage, Equiv.symm_apply_apply]
    cases z with
    | inl x =>
      change x ∈ I ↔ i x ∈ i '' I
      simp [i.injective.eq_iff]
    | inr y =>
      change False ↔ y.val ∈ i '' I
      exact ⟨False.elim, fun ⟨x,_,he⟩ => y.property ⟨x,he⟩⟩
  have hlive (S : Set X) : e.symm ⁻¹' ambientLive S = imageLive i S := by
    ext y
    obtain ⟨z,rfl⟩ := e.surjective y
    simp only [Set.mem_preimage, Equiv.symm_apply_apply]
    cases z with
    | inl x => exact (imageLive_apply i S x).symm
    | inr y =>
      change True ↔ y.val ∈ imageLive i S
      exact ⟨fun _ => Or.inr y.property, fun _ => trivial⟩
  rw [hmat, hsupport, hlive U, hlive T] at hh
  exact hh

/-- Transport into the exact current ambient live set. The preimage hypothesis
specifies geometry only; the deletion sequence is the concrete input `h`. -/
theorem sequence_on_live {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T)
    (i : X ↪ Y) (E : Matrix Y Y ℤ) (hE : SkewSymmetric E)
    (hz : ∀ x ∈ I, ∀ y, E (i x) y=0)
    (V : Set Y) (hV : i ⁻¹' V = U) :
    Sequence (zeroExtension i A+E) (i '' I) V (V \ i '' (U \ T)) := by
  classical
  have hpre (x : X) : i x ∈ V ↔ x ∈ U := by
    change x ∈ i ⁻¹' V ↔ x ∈ U
    rw [hV]
  have hsub : V ⊆ imageLive i U := by
    intro y hy
    by_cases hr : y ∈ Set.range i
    · obtain ⟨x,rfl⟩ := hr
      exact (imageLive_apply i U x).mpr ((hpre x).mp hy)
    · exact Or.inr hr
  have hr := sequence_restrict_live (sequence_injection h i E hE hz) Vᶜ (by
    rintro y ⟨x,hx,rfl⟩ hy
    exact fun hn => hn ((hpre x).mpr ((imageLive_apply i U x).mp hy)))
  have hin : imageLive i U \ Vᶜ=V := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_compl_iff, not_not]
    exact ⟨fun hy => hy.2, fun hy => ⟨hsub hy,hy⟩⟩
  have hout : imageLive i T \ Vᶜ=V \ i '' (U \ T) := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_compl_iff, not_not]
    constructor
    · rintro ⟨hy,hv⟩
      refine ⟨hv,?_⟩
      rintro ⟨x,hx,rfl⟩
      exact hx.2 ((imageLive_apply i T x).mp hy)
    · rintro ⟨hv,hn⟩
      refine ⟨?_,hv⟩
      by_cases hh : y ∈ Set.range i
      · obtain ⟨x,rfl⟩ := hh
        apply (imageLive_apply i T x).mpr
        by_contra ht
        exact hn ⟨x,⟨(hpre x).mp hv,ht⟩,rfl⟩
      · exact Or.inr hh
  rw [hin,hout] at hr
  exact hr

/-- Zero extension preserves skew symmetry for every embedding. -/
theorem zeroExtension_skew {X Y : Type*} (i : X ↪ Y) {A : Matrix X X ℤ}
    (hA : SkewSymmetric A) : SkewSymmetric (zeroExtension i A) := by
  intro u v
  obtain ⟨x,rfl⟩ := (injectionEquiv i).surjective u
  obtain ⟨y,rfl⟩ := (injectionEquiv i).surjective v
  have hm := congrFun (congrFun (zeroExtension_equiv i A) x) y
  have hn := congrFun (congrFun (zeroExtension_equiv i A) y) x
  change zeroExtension i A _ _ = extendMatrix A x y at hm
  change zeroExtension i A _ _ = extendMatrix A y x at hn
  rw [hm,hn]
  cases x <;> cases y <;> simp only [extendMatrix, neg_zero]
  exact hA _ _

/-- Local supported rows suffice; the complementary skew block is derived from
`B`, so no global entry outside those rows is constrained. -/
theorem sequence_of_rows {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X X ℤ} {I U T : Set X} (h : Sequence A I U T)
    (hA : SkewSymmetric A) (i : X ↪ Y) (B : Matrix Y Y ℤ)
    (hB : SkewSymmetric B)
    (hrow : ∀ x ∈ I, ∀ y, B (i x) y=zeroExtension i A (i x) y)
    (V : Set Y) (hV : i ⁻¹' V=U) :
    Sequence B (i '' I) V (V \ i '' (U \ T)) := by
  have hE : SkewSymmetric (B-zeroExtension i A) := by
    intro x y
    change B x y-zeroExtension i A x y = -(B y x-zeroExtension i A y x)
    rw [hB x y,zeroExtension_skew i hA x y]
    omega
  have hz : ∀ x ∈ I, ∀ y, (B-zeroExtension i A) (i x) y=0 := by
    intro x hx y
    change B (i x) y-zeroExtension i A (i x) y=0
    rw [hrow x hx y,sub_self]
  have hh := sequence_on_live h i (B-zeroExtension i A) hE hz V hV
  have he : zeroExtension i A+(B-zeroExtension i A)=B := by
    funext x y
    change zeroExtension i A x y+(B x y-zeroExtension i A x y)=B x y
    omega
  rwa [he] at hh

end FgStrip.Rounds
