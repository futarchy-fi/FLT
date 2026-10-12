/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicParameterCoefficient
public import FLT.Mazur.WeierstrassConicPunctureCoefficient
public import FLT.Mazur.WeierstrassModificationXConicSecondCoordinates
public import FLT.Mazur.WeierstrassModificationXConicGeometry

/-!
# Both complete conic parameter charts commute with coefficients

These identities include the parameter origin, with no vanishing-constant
hypothesis. Both original signed incidence and slope functions are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
  (a c : S) (b d : T) (ha : f a = b) (hc : f c = d)
  (ua : IsUnit a) (ub : IsUnit b)
local notation "C" => conicCoefficientMap f a c b d ha hc
local notation "P" => conicParameterCoefficientMap f c d hc
local notation "F₁" => (conicFirstParameterEquiv a c ua).symm.toRingHom.comp
  (algebraMap (ConicCoordinate a c) (ConicFirstOpen a c))
local notation "G₁" => (conicFirstParameterEquiv b d ub).symm.toRingHom.comp
  (algebraMap (ConicCoordinate b d) (ConicFirstOpen b d))
local notation "F₂" => (conicSecondParameterEquiv a c ua).symm.toRingHom.comp
  (algebraMap (ConicCoordinate a c) (ConicSecondOpen a c))
local notation "G₂" => (conicSecondParameterEquiv b d ub).symm.toRingHom.comp
  (algebraMap (ConicCoordinate b d) (ConicSecondOpen b d))

/-- The full first inverse parameter specializes on every conic function. -/
theorem conicFirstParameter_coefficient_algebra : (G₁).comp C = (P).comp F₁ := by
  apply conic_ringHom_ext
  · intro s
    change (conicFirstParameterEquiv b d ub).symm
      (algebraMap _ _ (C (algebraMap S _ s))) =
        P ((conicFirstParameterEquiv a c ua).symm
          (algebraMap _ _ (algebraMap S _ s)))
    rw [conicCoefficientMap_scalar, ← IsScalarTower.algebraMap_apply T,
      ← IsScalarTower.algebraMap_apply S, AlgEquiv.commutes, AlgEquiv.commutes,
      conicParameterCoefficientMap_scalar]
  · change conicFirstToParameter b d ub (algebraMap _ _ (C (conicT a c))) =
      P (conicFirstToParameter a c ua (algebraMap _ _ (conicT a c)))
    rw [conicCoefficientMap_t, conicFirstToParameter_base, conicFirstToParameter_base,
      conicToParameter_t, conicToParameter_t, conicParameterCoefficientMap_inverseT, ha]
  · change conicFirstToParameter b d ub (algebraMap _ _ (C (conicV a c))) =
      P (conicFirstToParameter a c ua (algebraMap _ _ (conicV a c)))
    rw [conicCoefficientMap_v, conicFirstToParameter_base, conicFirstToParameter_base,
      conicToParameter_v, conicToParameter_v, conicParameterCoefficientMap_inverseV, ha]

/-- The full opposite inverse parameter retains its negative scale and slope shift. -/
theorem conicSecondParameter_coefficient_algebra : (G₂).comp C = (P).comp F₂ := by
  apply conic_ringHom_ext
  · intro s
    change (conicSecondParameterEquiv b d ub).symm
      (algebraMap _ _ (C (algebraMap S _ s))) =
        P ((conicSecondParameterEquiv a c ua).symm
          (algebraMap _ _ (algebraMap S _ s)))
    rw [conicCoefficientMap_scalar, ← IsScalarTower.algebraMap_apply T,
      ← IsScalarTower.algebraMap_apply S, AlgEquiv.commutes, AlgEquiv.commutes,
      conicParameterCoefficientMap_scalar]
  · change (conicSecondParameterEquiv b d ub).symm
      (algebraMap _ _ (C (conicT a c))) =
        P ((conicSecondParameterEquiv a c ua).symm (algebraMap _ _ (conicT a c)))
    rw [conicCoefficientMap_t, conicSecondParameterEquiv_symm_t,
      conicSecondParameterEquiv_symm_t, conicParameterCoefficientMap_inverseT, map_neg, ha]
  · change (conicSecondParameterEquiv b d ub).symm
      (algebraMap _ _ (C (conicV a c))) =
        P ((conicSecondParameterEquiv a c ua).symm (algebraMap _ _ (conicV a c)))
    rw [conicCoefficientMap_v, conicSecondParameterEquiv_symm_v,
      conicSecondParameterEquiv_symm_v, map_sub, conicParameterCoefficientMap_inverseV,
      conicParameterCoefficientMap_scalar, map_neg, ha]

/-- The entire first parameter chart commutes with the full conic specialization. -/
@[reassoc] theorem conicFirstParameter_coefficient :
    (conicFirstParameterIso b d ub).inv ≫ conicFirstOpenImmersion b d ≫
        Spec.map (CommRingCat.ofHom C) =
      Spec.map (CommRingCat.ofHom P) ≫
        (conicFirstParameterIso a c ua).inv ≫ conicFirstOpenImmersion a c := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact conicFirstParameter_coefficient_algebra f a c b d ha hc ua ub

/-- The entire second parameter chart preserves its signed specialization as well. -/
@[reassoc] theorem conicSecondParameter_coefficient :
    (conicSecondParameterIso b d ub).inv ≫ conicSecondOpenImmersion b d ≫
        Spec.map (CommRingCat.ofHom C) =
      Spec.map (CommRingCat.ofHom P) ≫
        (conicSecondParameterIso a c ua).inv ≫ conicSecondOpenImmersion a c := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact conicSecondParameter_coefficient_algebra f a c b d ha hc ua ub

end FLT.Mazur.WeierstrassModificationX
