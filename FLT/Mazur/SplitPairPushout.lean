/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SplitPairLocalDescent

/-!
# The scheme pushout of two augmented affine branches

Matching-pair spectra have the full arbitrary-target universal property.
The branch rings may already be localized; the marked field is unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SplitPairEqualizer
set_option backward.isDefEq.respectTransparency false
universe u
variable {K C D : Type u} [Field K] [CommRing C] [CommRing D]
  (f : C →+* K) (g : D →+* K) (l : K →+* C) (r : K →+* D)
  (hl : f.comp l = RingHom.id K) (hr : g.comp r = RingHom.id K)

/-- The first branch into the actual matching-pair spectrum. -/
def firstBranch : Spec (.of C) ⟶ Spec (.of (E f g)) :=
  Spec.map (CommRingCat.ofHom ((RingHom.fst _ _).comp (E f g).subtype))
/-- The second branch into the actual matching-pair spectrum. -/
def secondBranch : Spec (.of D) ⟶ Spec (.of (E f g)) :=
  Spec.map (CommRingCat.ofHom ((RingHom.snd _ _).comp (E f g).subtype))

include hl hr in
/-- Unique descent from the product normalization to arbitrary schemes. -/
theorem product_desc {Y : Scheme.{u}} (h : Spec (.of (C × D)) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (leftEval f (D := D))) ≫ h =
      Spec.map (CommRingCat.ofHom (rightEval g (C := C))) ≫ h) :
    ∃! d : Spec (.of (E f g)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (E f g).subtype) ≫ d = h :=
  RingEqualizerDescent.exists_desc (leftEval f (D := D)) (rightEval g (C := C)) h
    (inclusion_finite f g l r hl hr) (evaluation_surjective f g l r hl hr)
    (exists_local_desc f g l r hl hr h w)

include hl hr in
/-- Two maps agreeing at the specified origin descend uniquely. -/
theorem branches_desc {Y : Scheme.{u}} (a : Spec (.of C) ⟶ Y) (b : Spec (.of D) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃! d : Spec (.of (E f g)) ⟶ Y,
      firstBranch f g ≫ d = a ∧ secondBranch f g ≫ d = b := by
  let h := inv (coprodSpec C D) ≫ coprod.desc a b
  have h₁ : Spec.map (CommRingCat.ofHom (RingHom.fst C D)) ≫ h = a := by
    rw [← coprodSpec_inl, Category.assoc]
    simp [h]
  have h₂ : Spec.map (CommRingCat.ofHom (RingHom.snd C D)) ≫ h = b := by
    rw [← coprodSpec_inr, Category.assoc]
    simp [h]
  have hw : Spec.map (CommRingCat.ofHom (leftEval f (D := D))) ≫ h =
      Spec.map (CommRingCat.ofHom (rightEval g (C := C))) ≫ h := by
    rw [leftEval, rightEval, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
      Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, h₁, h₂]
    exact w
  let ν := Spec.map (CommRingCat.ofHom (E f g).subtype)
  have hb₁ : Spec.map (CommRingCat.ofHom (RingHom.fst C D)) ≫ ν = firstBranch f g := by
    rw [firstBranch, ← Spec.map_comp]; rfl
  have hb₂ : Spec.map (CommRingCat.ofHom (RingHom.snd C D)) ≫ ν = secondBranch f g := by
    rw [secondBranch, ← Spec.map_comp]; rfl
  obtain ⟨d, hd, hu⟩ := product_desc f g l r hl hr h hw
  have hd' : ν ≫ d = h := hd
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · rw [← hb₁, Category.assoc, hd', h₁]
  · rw [← hb₂, Category.assoc, hd', h₂]
  · rintro e ⟨he₁, he₂⟩
    apply hu e
    change ν ≫ e = h
    apply (cancel_epi (coprodSpec C D)).mp
    apply coprod.hom_ext
    · rw [coprodSpec_inl_assoc, coprodSpec_inl_assoc, ← Category.assoc, hb₁, he₁, h₁]
    · rw [coprodSpec_inr_assoc, coprodSpec_inr_assoc, ← Category.assoc, hb₂, he₂, h₂]

include hl hr in
/-- The matching-pair spectrum is a pushout in schemes, without affine target restrictions. -/
theorem isPushout : IsPushout (Spec.map (CommRingCat.ofHom f))
    (Spec.map (CommRingCat.ofHom g)) (firstBranch f g) (secondBranch f g) := by
  have w : Spec.map (CommRingCat.ofHom f) ≫ firstBranch f g =
      Spec.map (CommRingCat.ofHom g) ≫ secondBranch f g := by
    rw [firstBranch, secondBranch, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun z ↦ z.property)
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => (branches_desc f g l r hl hr s.inl s.inr s.condition).choose) ?_ ?_ ?_⟩⟩
  · intro s
    exact (branches_desc f g l r hl hr s.inl s.inr s.condition).choose_spec.1.1
  · intro s
    exact (branches_desc f g l r hl hr s.inl s.inr s.condition).choose_spec.1.2
  · intro s m hm hn
    exact (branches_desc f g l r hl hr s.inl s.inr s.condition).choose_spec.2 m ⟨hm, hn⟩

end FLT.Mazur.SplitPairEqualizer
