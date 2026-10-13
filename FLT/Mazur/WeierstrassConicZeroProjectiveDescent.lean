/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroDescent
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# The zero conic receives maps from its two complete branch components

The original affine parameters and both incidence markings are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a) (hc : c = 0)
local notation "Z" => conicZeroAffineIso c hc
local notation "p₁" => (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c
local notation "p₂" => (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c
variable {Y : Scheme.{u}} (f₁ f₂ : ProjectiveLine.scheme K ⟶ Y)

/-- Descend the full affine charts of two independently supplied projective components. -/
@[irreducible] def conicZeroProjectiveDesc : Spec (.of (ConicCoordinate a c)) ⟶ Y :=
  conicZeroDesc a c ha hc ((Z).inv ≫ ProjectiveLine.left K ≫ f₁)
    ((Z).inv ≫ ProjectiveLine.left K ≫ f₂)

/-- The complete first branch has its original affine parameter. -/
@[reassoc] theorem conicZeroProjectiveDesc_first :
    (Z).hom ≫ p₁ ≫ conicZeroProjectiveDesc a c ha hc f₁ f₂ =
      ProjectiveLine.left K ≫ f₁ := by
  rw [conicZeroProjectiveDesc, conicZeroDesc_first, Iso.hom_inv_id_assoc]

/-- The complete opposite branch has its independently specified affine parameter. -/
@[reassoc] theorem conicZeroProjectiveDesc_second :
    (Z).hom ≫ p₂ ≫ conicZeroProjectiveDesc a c ha hc f₁ f₂ =
      ProjectiveLine.left K ≫ f₂ := by
  rw [conicZeroProjectiveDesc, conicZeroDesc_second, Iso.hom_inv_id_assoc]

/-- The first incidence marking is zero on the first original component. -/
@[reassoc] theorem conicZeroProjectiveDesc_first_origin :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫
      conicZeroProjectiveDesc a c ha hc f₁ f₂ = ProjectiveLine.zero K ≫ f₁ := by
  rw [conicZeroProjectiveDesc, ← conicFirstParameterIso_origin_assoc,
    ← Category.assoc _ _ (conicZeroDesc ..), conicZeroDesc_first,
    ← conicZeroAffineIso_origin c hc, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The opposite incidence marking is zero on the opposite original component. -/
@[reassoc] theorem conicZeroProjectiveDesc_second_origin :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫
      conicZeroProjectiveDesc a c ha hc f₁ f₂ = ProjectiveLine.zero K ≫ f₂ := by
  rw [conicZeroProjectiveDesc, ← conicSecondParameterIso_origin_assoc,
    ← Category.assoc _ _ (conicZeroDesc ..), conicZeroDesc_second,
    ← conicZeroAffineIso_origin c hc, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- Both full original affine branches characterize the conic map. -/
theorem conicZeroProjectiveDesc_unique (m : Spec (.of (ConicCoordinate a c)) ⟶ Y)
    (h₁ : (Z).hom ≫ p₁ ≫ m = ProjectiveLine.left K ≫ f₁)
    (h₂ : (Z).hom ≫ p₂ ≫ m = ProjectiveLine.left K ≫ f₂) :
    m = conicZeroProjectiveDesc a c ha hc f₁ f₂ := by
  apply conicParameter_hom_ext a c ha
  · apply (cancel_epi (Z).hom).mp
    simpa only [Category.assoc] using
      h₁.trans (conicZeroProjectiveDesc_first a c ha hc f₁ f₂).symm
  · apply (cancel_epi (Z).hom).mp
    simpa only [Category.assoc] using
      h₂.trans (conicZeroProjectiveDesc_second a c ha hc f₁ f₂).symm

end FLT.Mazur.WeierstrassModificationX
