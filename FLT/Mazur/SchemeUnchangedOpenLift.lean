/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Lift an actual chart through a full unchanged open

An isomorphism on the entire target open produces an actual lift of any
open chart with that image, and the lift is its complete pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeUnchangedOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme} (f : X ⟶ Y) (i : T ⟶ Y) [IsOpenImmersion i]
  (h : IsIso (f ∣_ i.opensRange))

include h in
/-- The projection onto an unchanged open chart is an isomorphism. -/
theorem chartProjection_isIso : IsIso (pullback.snd f i) :=
  ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange f i)).mp h

/-- Lift the actual open chart by the inverse of its complete pullback projection. -/
def lift : T ⟶ X := by
  let _ := chartProjection_isIso f i h
  exact inv (pullback.snd f i) ≫ pullback.fst f i

instance lift_isOpenImmersion : IsOpenImmersion (lift f i h) := by
  let _ := chartProjection_isIso f i h
  unfold lift
  infer_instance

/-- The lifted chart contracts to its exact original morphism. -/
@[reassoc] theorem lift_comp : lift f i h ≫ f = i := by
  let _ := chartProjection_isIso f i h
  rw [lift, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- The lifted chart is the entire contraction pullback of its original open immersion. -/
theorem lift_isPullback : IsPullback (𝟙 T) (lift f i h) i f := by
  let _ := chartProjection_isIso f i h
  apply (IsPullback.of_hasPullback f i).flip.of_iso
    (asIso (pullback.snd f i)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simp [lift]
  · simp
  · simp

/-- A map with the same original chart contraction must be the full unchanged lift. -/
theorem lift_unique (g : T ⟶ X) (hg : g ≫ f = i) : g = lift f i h := by
  let H := lift_isPullback f i h
  have hw : (𝟙 T) ≫ i = g ≫ f := by simpa using hg.symm
  have hf := H.lift_fst (𝟙 T) g hw
  have hs := H.lift_snd (𝟙 T) g hw
  have hl : H.lift (𝟙 T) g hw = 𝟙 T := by simpa using hf
  simpa only [hl, Category.id_comp] using hs.symm

/-- There are no other points above the unchanged chart. -/
theorem lift_preimage : f ⁻¹' Set.range i = Set.range (lift f i h) := by
  have H := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (lift_isPullback f i h) ⊤
  simpa using (congrArg SetLike.coe H).symm

end FLT.Mazur.SchemeUnchangedOpen
