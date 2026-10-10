/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicParameterOverlap
public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The full scheme overlap of the two conic parameter charts

The explicit doubly localized algebra is the actual pullback of the two
original conic neighborhoods. Transport along the rational parameter
isomorphisms gives the full parameter overlap, not just a pointwise match.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R)
local notation "C₀" => ConicCoordinate a c
local notation "O₁" => ConicFirstOpen a c
local notation "O₂" => ConicSecondOpen a c
local notation "B" => ConicParameterOverlap a c

/-- The overlap projection to the first full tangent neighborhood. -/
def conicOverlapFirstMap : Spec (.of B) ⟶ Spec (.of O₁) :=
  Spec.map (CommRingCat.ofHom (algebraMap O₁ B))

/-- The overlap projection to the second full tangent neighborhood. -/
def conicOverlapSecondMap : Spec (.of B) ⟶ Spec (.of O₂) :=
  Spec.map (CommRingCat.ofHom (conicSecondToOverlap a c).toRingHom)

/-- The doubly localized algebra is the full scheme intersection of the tangent opens. -/
theorem conicOverlap_isPullback : IsPullback (conicOverlapFirstMap a c)
    (conicOverlapSecondMap a c) (conicFirstOpenImmersion a c)
      (conicSecondOpenImmersion a c) := by
  apply isPullback_SpecMap_of_isPushout
  apply CommRingCat.isPushout_of_isLocalization (algebraMap C₀ O₁)
    (conicSecondToOverlap a c).toRingHom _ (Submonoid.powers (conicV a c))
  apply RingHom.ext
  intro q
  exact conicSecondToOverlap_base a c q

instance conicOverlapFirstMap_isOpenImmersion : IsOpenImmersion (conicOverlapFirstMap a c) :=
  IsOpenImmersion.of_isLocalization (algebraMap C₀ O₁ (conicV a c))

instance conicOverlapSecondMap_isOpenImmersion : IsOpenImmersion (conicOverlapSecondMap a c) :=
  MorphismProperty.of_isPullback (conicOverlap_isPullback a c)
    (show IsOpenImmersion (conicFirstOpenImmersion a c) from inferInstance)

/-- The overlap map to the first rational parameter scheme. -/
def conicOverlapFirstParameterMap (ha : IsUnit a) :=
  conicOverlapFirstMap a c ≫ (conicFirstParameterIso a c ha).hom

/-- The overlap map to the second rational parameter scheme. -/
def conicOverlapSecondParameterMap (ha : IsUnit a) :=
  conicOverlapSecondMap a c ≫ (conicSecondParameterIso a c ha).hom

/-- The explicit overlap also represents the intersection of the actual parameter charts. -/
theorem conicParameterOverlap_isPullback (ha : IsUnit a) :
    IsPullback (conicOverlapFirstParameterMap a c ha) (conicOverlapSecondParameterMap a c ha)
      ((conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c)
      ((conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c) := by
  apply (conicOverlap_isPullback a c).of_iso (Iso.refl _)
    (conicFirstParameterIso a c ha) (conicSecondParameterIso a c ha) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, conicOverlapFirstParameterMap]
  · simp only [Iso.refl_hom, Category.id_comp, conicOverlapSecondParameterMap]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

/-- An isomorphism with the full categorical parameter overlap, retaining both projections. -/
def conicParameterOverlapIso (ha : IsUnit a) : Spec (.of B) ≅
    pullback ((conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c)
      ((conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c) :=
  (conicParameterOverlap_isPullback a c ha).isoPullback

end FLT.Mazur.WeierstrassModificationX
