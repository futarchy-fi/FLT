/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCyclicParameterDensity
public import FLT.Mazur.WeierstrassSmoothHorizontalFactorOrder
public import FLT.Mazur.WeierstrassSmoothHorizontalCyclicParameter
public import FLT.Mazur.ProjectiveLineUniversalLaurentEvaluation
public import FLT.Mazur.LaurentCoefficientInjectivity
public import FLT.Mazur.LaurentTensor

/-!
# Density of the independent smooth and conic residue pair

Tensor interchange identifies the actual conic-first source with Laurent
polynomials over the smooth localization. In that order the universal pair
map is simply the injective cyclic change of coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
open WeierstrassDividedDepth
local notation "𝕂" => ResidueField R
local notation "L" => 𝕂[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "C" => SmoothHorizontalResidueRing D
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D

/-- Put the actual residue product in smooth-coefficient Laurent form. -/
def smoothHorizontalLaurentOrder : C ≃ₐ[𝕂] P[T;T⁻¹] :=
  (smoothHorizontalResidueInterchange D).trans (LaurentTensor.equivalence 𝕂 P)

/-- Every smooth parameter becomes a Laurent coefficient after the original interchange. -/
theorem smoothHorizontalLaurentOrder_parameter (t : P) :
    smoothHorizontalLaurentOrder D (smoothHorizontalResidueParameter D t) =
      LaurentPolynomial.C t := by
  change LaurentTensor.equivalence 𝕂 P
    (smoothHorizontalResidueInterchange D (smoothHorizontalResidueParameter D t)) = _
  rw [smoothHorizontalResidueInterchange_parameter]
  exact LaurentTensor.equivalence_left 𝕂 P t

/-- Every conic function becomes the Laurent coordinate function after interchange. -/
theorem smoothHorizontalLaurentOrder_conic (t : L) :
    smoothHorizontalLaurentOrder D (smoothHorizontalResidueConic D t) =
      PolygonScalingNaturality.coeffMap (algebraMap 𝕂 P) t := by
  change LaurentTensor.equivalence 𝕂 P
    (smoothHorizontalResidueInterchange D (smoothHorizontalResidueConic D t)) = _
  rw [smoothHorizontalResidueInterchange_conic]
  exact LaurentTensor.equivalence_right 𝕂 P t

/-- The actual universal pair map is the cyclic coefficient inclusion in smooth-first order. -/
theorem smoothHorizontalLaurentPair_ordered :
    (smoothHorizontalLaurentOrder D).toRingEquiv.toRingHom.comp
        (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z).toRingHom =
      PolygonScalingNaturality.coeffMap (smoothYParameterCyclicAlgebra D).toRingHom := by
  have hz : LaurentUnitPoints.evalUnit z = smoothHorizontalResidueConic D := by
    have h : LaurentUnitPoints.pointUnit (smoothHorizontalResidueConic D) = z := by
      apply Units.ext
      exact (smoothHorizontalConicUnit_val D).symm
    rw [← h, LaurentUnitPoints.evalUnit_pointUnit]
  apply PolygonScalingNaturality.ringHom_ext
  · intro t
    change smoothHorizontalLaurentOrder D (LaurentPolynomial.eval₂
      (LaurentUnitPoints.evalUnit τ⁻¹).toRingHom z (LaurentPolynomial.C t)) = _
    rw [LaurentPolynomial.eval₂_C, PolygonScalingNaturality.coeffMap_C]
    change smoothHorizontalLaurentOrder D (smoothHorizontalLaurentEvaluation D τ⁻¹ t) = _
    rw [smoothHorizontalCyclicParameter_evaluation]
    exact smoothHorizontalLaurentOrder_parameter D (smoothYParameterCyclicAlgebra D t)
  · change smoothHorizontalLaurentOrder D (LaurentPolynomial.eval₂
      (LaurentUnitPoints.evalUnit τ⁻¹).toRingHom z (LaurentPolynomial.T 1)) = _
    rw [LaurentPolynomial.eval₂_T, ← LaurentUnitPoints.evalUnit_T (R := 𝕂) z, hz,
      smoothHorizontalLaurentOrder_conic]
    simp only [PolygonScalingNaturality.coeffMap_T_one]
  · change smoothHorizontalLaurentOrder D (LaurentPolynomial.eval₂
      (LaurentUnitPoints.evalUnit τ⁻¹).toRingHom z (LaurentPolynomial.T (-1))) = _
    rw [LaurentPolynomial.eval₂_T, ← LaurentUnitPoints.evalUnit_T (R := 𝕂) z, hz,
      smoothHorizontalLaurentOrder_conic]
    simp only [PolygonScalingNaturality.coeffMap_T_neg_one]

/-- The actual independent residue pair loses no function of the two cyclic coordinates. -/
theorem smoothHorizontalLaurentPair_injective :
    Function.Injective (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z) := by
  have h := PolygonScalingNaturality.coeffMap_injective
    (smoothYParameterCyclicAlgebra D).toRingHom (smoothYParameterCyclicAlgebra_injective D)
  rw [← smoothHorizontalLaurentPair_ordered] at h
  intro x y he
  apply h
  exact congrArg (smoothHorizontalLaurentOrder D) he

/-- The original smooth-times-conic source is dense in the universal cyclic pair. -/
instance smoothHorizontalLaurentPair_dominant :
    IsDominant (Spec.map (CommRingCat.ofHom
      (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z).toRingHom)) := by
  let _ := SurjectiveDominantEpi.spec_schematic
    (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z).toRingHom
    (smoothHorizontalLaurentPair_injective D)
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
