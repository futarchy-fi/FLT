/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalReciprocalEvaluation

/-!
# Evaluating the original smooth product at independent algebra-valued units

The actual smooth affine chart requires the tangent unit minus one to be
invertible. Its localization and the full conic tensor factor are evaluated explicitly.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  {A : Type u} [CommRing A] [Algebra (ResidueField R) A]
  (τ : Aˣ) (hτ : IsUnit ((τ : A) - 1))
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "P" => SmoothYParameterRing D

include hτ in
/-- The real smooth chart denominator is invertible at the specified tangent unit. -/
theorem smoothYUnitEvaluation_denominator :
    IsUnit (LaurentUnitPoints.evalUnit τ (splitNodalLaurentZ a)) := by
  simp only [splitNodalLaurentZ, splitNodalLaurentX, map_mul, map_pow,
    map_sub, map_one, AlgHom.commutes, LaurentUnitPoints.evalUnit_T,
    zpow_one, zpow_neg_one]
  exact (((a⁻¹).isUnit.map (algebraMap K A)).mul hτ).pow 3 |>.mul (τ⁻¹).isUnit

/-- Evaluation on the actual localized smooth parameter ring. -/
def smoothYUnitEvaluation : P →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (splitNodalLaurentZ a)
    (smoothYUnitEvaluation_denominator D τ hτ)

/-- The localization evaluation retains every original Laurent function. -/
theorem smoothYUnitEvaluation_base (x : L) :
    smoothYUnitEvaluation D τ hτ (algebraMap L P x) = LaurentUnitPoints.evalUnit τ x :=
  IsLocalization.Away.lift_eq _ (smoothYUnitEvaluation_denominator D τ hτ) x

variable (z : Aˣ)

/-- Evaluate both independent factors of the original smooth residue product. -/
def smoothHorizontalUnitEvaluation : SmoothHorizontalResidueRing D →ₐ[K] A :=
  Algebra.TensorProduct.lift (LaurentUnitPoints.evalUnit z) (smoothYUnitEvaluation D τ hτ)
    (fun _ _ => Commute.all _ _)

/-- Evaluation on the entire original conic factor. -/
theorem smoothHorizontalUnitEvaluation_conic (x : L) :
    smoothHorizontalUnitEvaluation D τ hτ z (smoothHorizontalResidueConic D x) =
      LaurentUnitPoints.evalUnit z x := by
  change LaurentUnitPoints.evalUnit z x * smoothYUnitEvaluation D τ hτ 1 = _
  rw [map_one, mul_one]

/-- Evaluation on the entire original localized smooth factor. -/
theorem smoothHorizontalUnitEvaluation_parameter (x : P) :
    smoothHorizontalUnitEvaluation D τ hτ z (smoothHorizontalResidueParameter D x) =
      smoothYUnitEvaluation D τ hτ x := by
  change LaurentUnitPoints.evalUnit z 1 * smoothYUnitEvaluation D τ hτ x = _
  rw [map_one, one_mul]

/-- The original conic unit evaluates to the independently specified conic parameter. -/
theorem smoothHorizontalUnitEvaluation_conicUnit :
    Units.map (smoothHorizontalUnitEvaluation D τ hτ z).toMonoidHom
      (smoothHorizontalConicUnit D) = z := by
  apply Units.ext
  change smoothHorizontalUnitEvaluation D τ hτ z (smoothHorizontalConicUnit D : _) = _
  rw [smoothHorizontalConicUnit_val, smoothHorizontalUnitEvaluation_conic,
    LaurentUnitPoints.evalUnit_T, zpow_one]

/-- The actual smooth tangent unit evaluates to its specified independent parameter. -/
theorem smoothHorizontalUnitEvaluation_tangentUnit :
    Units.map (smoothHorizontalUnitEvaluation D τ hτ z).toMonoidHom
      (smoothHorizontalTangentUnit D) = τ := by
  apply Units.ext
  change smoothHorizontalUnitEvaluation D τ hτ z (smoothHorizontalTangentUnit D : _) = _
  rw [smoothHorizontalTangentUnit_val, smoothHorizontalUnitEvaluation_parameter,
    smoothYUnitEvaluation_base, LaurentUnitPoints.evalUnit_T, zpow_one]

/-- Signed reciprocal coordinates evaluate on the whole original product. -/
theorem smoothHorizontalUnitEvaluation_reciprocalUnit (b : Kˣ) :
    Units.map (smoothHorizontalUnitEvaluation D τ hτ z).toMonoidHom
      (smoothHorizontalReciprocalUnit D b) = Units.map (algebraMap K A) b * z⁻¹ := by
  rw [smoothHorizontalReciprocalUnit, map_mul, map_inv,
    smoothHorizontalUnitEvaluation_conicUnit]
  congr 1
  apply Units.ext
  exact (smoothHorizontalUnitEvaluation D τ hτ z).commutes b

end FLT.Mazur.WeierstrassIntegralChart
