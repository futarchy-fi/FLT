/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffinePolynomialScaling
public import FLT.Mazur.WeierstrassPolynomialOutputIntersections

/-!
# Polynomial comparison on all four affine addition intersections

Localize each actual affine addition domain at a polynomial output coordinate.
The integral scaling formulas construct a map from the appropriate output
overlap, and both local addition laws are recovered by its restrictions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : AdditionChartIndex)

/-- The algebra homomorphism underlying every member of the affine addition cover. -/
def additionChartAlgOutput : Coordinate W (additionChartOutput i) →ₐ[R] additionChartRing W i :=
  match i with
  | .secant => secantAddition W
  | .tangent => tangentAddition W
  | .verticalSecant => verticalSecantAddition W
  | .verticalTangent => verticalTangentAddition W

/-- The explicit factor comparing polynomial addition to each normalized affine law. -/
def additionPolynomialFactor : additionChartRing W i :=
  match i with
  | .secant => additionChartAlgRestriction W .secant (secantDenominator W) ^ 3
  | .tangent => additionChartAlgRestriction W .tangent (secantDenominator W) ^ 3
  | .verticalSecant => reciprocalPolynomialFactor W false
  | .verticalTangent => reciprocalPolynomialFactor W true

/-- The scaling identity for every affine chart, including both reciprocal charts. -/
theorem additionPolynomial_scaled (a : Fin 3) :
    additionChartAlgRestriction W i (chartProductAdditionCoordinates W 2 2 a) =
      additionPolynomialFactor W i *
        additionChartAlgOutput W i (coord W (additionChartOutput i) a) := by
  cases i
  · exact ordinaryPolynomial_scaled W false a
  · exact ordinaryPolynomial_scaled W true a
  · exact reciprocalPolynomial_scaled W false a
  · exact reciprocalPolynomial_scaled W true a

variable (t : Fin 3)

/-- The concrete intersection of an affine addition domain and a polynomial output domain. -/
abbrev AffinePolynomialIntersection := Localization.Away
  (additionChartAlgRestriction W i (chartProductAdditionCoordinates W 2 2 t))

/-- Restriction from the affine addition domain to its polynomial intersection. -/
def affinePolynomialRestriction : additionChartRing W i →ₐ[R]
    AffinePolynomialIntersection W i t := IsScalarTower.toAlgHom R _ _

/-- The selected polynomial output coordinate is a unit on this intersection. -/
theorem affinePolynomialOutput_isUnit : IsUnit
    ((affinePolynomialRestriction W i t).comp (additionChartAlgRestriction W i)
      (chartProductAdditionCoordinates W 2 2 t)) :=
  IsLocalization.Away.algebraMap_isUnit
    (additionChartAlgRestriction W i (chartProductAdditionCoordinates W 2 2 t))

/-- Restriction from the polynomial addition domain to the same intersection. -/
def affinePolynomialOutput : AdditionOutputOpen W 2 2 t →ₐ[R]
    AffinePolynomialIntersection W i t :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W 2 2 t)
    (affinePolynomialOutput_isUnit W i t)

/-- The two restrictions have the same pair of inputs. -/
theorem affinePolynomialIntersection_inputs :
    (affinePolynomialOutput W i t).comp (additionOutputRestriction W 2 2 t) =
      (affinePolynomialRestriction W i t).comp (additionChartAlgRestriction W i) := by
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.Away.lift_comp (chartProductAdditionCoordinates W 2 2 t)
    (S := AdditionOutputOpen W 2 2 t)
    (g := ((affinePolynomialRestriction W i t).comp (additionChartAlgRestriction W i)).toRingHom)
    (affinePolynomialOutput_isUnit W i t)

/-- The concrete intersection retains the homogeneous comparison identity. -/
theorem affinePolynomialIntersection_scaled (a : Fin 3) :
    affinePolynomialOutput W i t
        (additionOutputRestriction W 2 2 t (chartProductAdditionCoordinates W 2 2 a)) =
      affinePolynomialRestriction W i t (additionPolynomialFactor W i) *
        ((affinePolynomialRestriction W i t).comp (additionChartAlgOutput W i))
          (coord W (additionChartOutput i) a) := by
  have hs := congrArg (affinePolynomialRestriction W i t) (additionPolynomial_scaled W i a)
  rw [map_mul] at hs
  exact (DFunLike.congr_fun (affinePolynomialIntersection_inputs W i t) _).trans hs

/-- The actual output-overlap factorization for every affine/polynomial intersection. -/
def affinePolynomialOutputLift :
    Overlap W t (additionChartOutput i) →ₐ[R] AffinePolynomialIntersection W i t :=
  polynomialComparisonLift W 2 2 t (additionChartOutput i) (affinePolynomialOutput W i t)
    ((affinePolynomialRestriction W i t).comp (additionChartAlgOutput W i))
    (affinePolynomialRestriction W i t (additionPolynomialFactor W i))
    (affinePolynomialIntersection_scaled W i t)

/-- The comparison recovers the polynomial law in its selected output chart. -/
theorem affinePolynomialOutputLift_restriction :
    (affinePolynomialOutputLift W i t).comp (overlapRestriction W t (additionChartOutput i)) =
      (affinePolynomialOutput W i t).comp (projectiveAdditionChart W 2 2 t) :=
  polynomialComparisonLift_restriction ..

/-- Changing output charts recovers the affine addition law. -/
theorem affinePolynomialOutputLift_transition :
    (affinePolynomialOutputLift W i t).comp (transitionBase W t (additionChartOutput i)) =
      (affinePolynomialRestriction W i t).comp (additionChartAlgOutput W i) :=
  polynomialComparisonLift_transition ..

open AlgebraicGeometry CategoryTheory

/-- The algebra output map recovers the original scheme output map. -/
theorem additionChartAlgOutput_spec :
    Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom) =
      additionChartSpec W i := by
  cases i <;> rfl

/-- The constructed ring is the scheme intersection of the two original domains. -/
theorem affinePolynomialIntersection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (affinePolynomialRestriction W i t).toRingHom))
      (Spec.map (CommRingCat.ofHom (affinePolynomialOutput W i t).toRingHom))
      (additionChartInclusion W i)
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W 2 2 t).toRingHom)) := by
  let _ : Algebra (AffineProduct W) (AdditionOutputOpen W 2 2 t) :=
    inferInstanceAs (Algebra (ChartProduct W 2 2) (AdditionOutputOpen W 2 2 t))
  let _ : IsLocalization.Away
      (show AffineProduct W from chartProductAdditionCoordinates W 2 2 t)
      (AdditionOutputOpen W 2 2 t) :=
    inferInstanceAs (IsLocalization.Away (chartProductAdditionCoordinates W 2 2 t)
      (AdditionOutputOpen W 2 2 t))
  have : IsLocalization
      ((Submonoid.powers (chartProductAdditionCoordinates W 2 2 t)).map
        (additionChartAlgRestriction W i).toRingHom)
      (AffinePolynomialIntersection W i t) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  simp only [← additionChartAlgRestriction_toRingHom]
  exact CommRingCat.isPushout_of_isLocalization
    (additionChartAlgRestriction W i).toRingHom
    (affinePolynomialOutput W i t).toRingHom
    (congrArg AlgHom.toRingHom (affinePolynomialIntersection_inputs W i t))
    (Submonoid.powers (chartProductAdditionCoordinates W 2 2 t))

end FLT.Mazur.WeierstrassIntegralChart
