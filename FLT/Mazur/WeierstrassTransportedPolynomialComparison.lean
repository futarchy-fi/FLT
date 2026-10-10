/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffinePolynomialIntersections
public import FLT.Mazur.WeierstrassTransportedAdditionRing

/-!
# Polynomial comparison on transported affine addition domains

Undoing the invertible input normalization transports the affine comparison
factor. Localizing at any original polynomial output coordinate then gives
the actual intersection and an output-overlap factorization of its two laws.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)
  (i : AdditionChartIndex)

/-- Homogeneous comparison factor after undoing the change of input coordinates. -/
def transportedPolynomialFactor : TransportedAdditionRing W j k i :=
  ↑(transportedAdditionScale_isUnit W j k i).unit⁻¹ *
    transportedAdditionAffine W j k i (additionPolynomialFactor W i)

/-- The original polynomial law scales to the actual transported affine law. -/
theorem transportedPolynomial_scaled (a : Fin 3) :
    transportedAdditionInput W j k i (chartProductAdditionCoordinates W j k a) =
      transportedPolynomialFactor W j k i *
        ((transportedAdditionAffine W j k i).comp (additionChartAlgOutput W i))
          (coord W (additionChartOutput i) a) := by
  have hs := transportedAdditionPolynomial_scaled W j k i a
  have ha := congrArg (transportedAdditionAffine W j k i) (additionPolynomial_scaled W i a)
  rw [map_mul] at ha
  have hi : ↑(transportedAdditionScale_isUnit W j k i).unit⁻¹ *
      transportedAdditionScale W j k i = 1 :=
    Units.inv_mul_eq_one.mpr (transportedAdditionScale_isUnit W j k i).unit_spec
  dsimp only [transportedPolynomialFactor, AlgHom.comp_apply]
  linear_combination -↑(transportedAdditionScale_isUnit W j k i).unit⁻¹ * hs +
    ↑(transportedAdditionScale_isUnit W j k i).unit⁻¹ * ha -
    transportedAdditionInput W j k i (chartProductAdditionCoordinates W j k a) * hi

variable (t : Fin 3)

/-- Intersection of a transported affine addition domain and an original polynomial domain. -/
abbrev TransportedPolynomialIntersection := Localization.Away
  (transportedAdditionInput W j k i (chartProductAdditionCoordinates W j k t))

/-- Restriction from the transported affine domain to the polynomial intersection. -/
def transportedPolynomialRestriction : TransportedAdditionRing W j k i →ₐ[R]
    TransportedPolynomialIntersection W j k i t := IsScalarTower.toAlgHom R _ _

/-- The selected original polynomial output coordinate is invertible on the intersection. -/
theorem transportedPolynomialOutput_isUnit : IsUnit
    ((transportedPolynomialRestriction W j k i t).comp (transportedAdditionInput W j k i)
      (chartProductAdditionCoordinates W j k t)) :=
  IsLocalization.Away.algebraMap_isUnit
    (transportedAdditionInput W j k i (chartProductAdditionCoordinates W j k t))

/-- Restriction from the original polynomial domain to the actual intersection. -/
def transportedPolynomialOutput : AdditionOutputOpen W j k t →ₐ[R]
    TransportedPolynomialIntersection W j k i t :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j k t)
    (transportedPolynomialOutput_isUnit W j k i t)

/-- Both restrictions have the original unnormalized input pair. -/
theorem transportedPolynomialIntersection_inputs :
    (transportedPolynomialOutput W j k i t).comp (additionOutputRestriction W j k t) =
      (transportedPolynomialRestriction W j k i t).comp (transportedAdditionInput W j k i) := by
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.Away.lift_comp (chartProductAdditionCoordinates W j k t)
    (S := AdditionOutputOpen W j k t)
    (g := ((transportedPolynomialRestriction W j k i t).comp
      (transportedAdditionInput W j k i)).toRingHom)
    (transportedPolynomialOutput_isUnit W j k i t)

/-- The homogeneous comparison descends to the actual intersection. -/
theorem transportedPolynomialIntersection_scaled (a : Fin 3) :
    transportedPolynomialOutput W j k i t
        (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k a)) =
      transportedPolynomialRestriction W j k i t (transportedPolynomialFactor W j k i) *
        ((transportedPolynomialRestriction W j k i t).comp
          ((transportedAdditionAffine W j k i).comp (additionChartAlgOutput W i)))
            (coord W (additionChartOutput i) a) := by
  have hs := congrArg (transportedPolynomialRestriction W j k i t)
    (transportedPolynomial_scaled W j k i a)
  rw [map_mul] at hs
  exact (DFunLike.congr_fun (transportedPolynomialIntersection_inputs W j k i t) _).trans hs

/-- Both addition laws factor through their actual output-chart overlap. -/
def transportedPolynomialOutputLift : Overlap W t (additionChartOutput i) →ₐ[R]
    TransportedPolynomialIntersection W j k i t :=
  polynomialComparisonLift W j k t (additionChartOutput i) (transportedPolynomialOutput W j k i t)
    ((transportedPolynomialRestriction W j k i t).comp
      ((transportedAdditionAffine W j k i).comp (additionChartAlgOutput W i)))
    (transportedPolynomialRestriction W j k i t (transportedPolynomialFactor W j k i))
    (transportedPolynomialIntersection_scaled W j k i t)

/-- The polynomial projection recovers the law on the original input charts. -/
theorem transportedPolynomialOutputLift_restriction :
    (transportedPolynomialOutputLift W j k i t).comp
        (overlapRestriction W t (additionChartOutput i)) =
      (transportedPolynomialOutput W j k i t).comp (projectiveAdditionChart W j k t) :=
  polynomialComparisonLift_restriction ..

/-- The other projection recovers the transported affine law. -/
theorem transportedPolynomialOutputLift_transition :
    (transportedPolynomialOutputLift W j k i t).comp
        (transitionBase W t (additionChartOutput i)) =
      (transportedPolynomialRestriction W j k i t).comp
        ((transportedAdditionAffine W j k i).comp (additionChartAlgOutput W i)) :=
  polynomialComparisonLift_transition ..

open AlgebraicGeometry CategoryTheory

/-- This is the actual scheme intersection over the original input-chart product. -/
theorem transportedPolynomialIntersection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (transportedPolynomialRestriction W j k i t).toRingHom))
      (Spec.map (CommRingCat.ofHom (transportedPolynomialOutput W j k i t).toRingHom))
      (Spec.map (CommRingCat.ofHom (transportedAdditionInput W j k i).toRingHom))
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom)) := by
  have : IsLocalization
      ((Submonoid.powers (chartProductAdditionCoordinates W j k t)).map
        (transportedAdditionInput W j k i).toRingHom)
      (TransportedPolynomialIntersection W j k i t) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization
    (transportedAdditionInput W j k i).toRingHom
    (transportedPolynomialOutput W j k i t).toRingHom
    (congrArg AlgHom.toRingHom (transportedPolynomialIntersection_inputs W j k i t))
    (Submonoid.powers (chartProductAdditionCoordinates W j k t))

end FLT.Mazur.WeierstrassIntegralChart
