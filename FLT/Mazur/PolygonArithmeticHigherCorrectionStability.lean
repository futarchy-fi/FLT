/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherCorrectionField
public import FLT.Mazur.PolygonSmoothingStationaryPunctures
public import FLT.Mazur.LaurentBoundaryCorrectionScalar

/-!
# Higher corrections vanish on every earlier arithmetic quotient

The scalar drift and the whole chart increment vanish at orders m <= r.
This proves identity of both complete puncture substitutions without a support
hypothesis or a truncation of the opposite branch's inverse.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing LaurentPolynomial LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- The coefficient of a correction of order r+1 vanishes on every earlier quotient. -/
theorem parameter_higher_eq_zero (m r : ℕ) (hm : m ≤ r) :
    parameter R π m ^ (r + 1) = 0 :=
  pow_eq_zero_of_le (Nat.add_le_add_right hm 1) (parameter_pow R π m)

/-- The entire higher scalar drift vanishes, including its linear coefficient. -/
theorem higherCorrection_scalar_eq_zero (m r : ℕ) (hm : m ≤ r) (q : R[T;T⁻¹]) :
    parameter R π m * algebraMap R (Quotient R π m)
      ((higherCorrectionField R π r q).coeff 1) = 0 := by
  rw [higherCorrectionField_coeff, map_mul, map_pow, ← mul_assoc]
  change (parameter R π m * parameter R π m ^ r) * _ = 0
  rw [← pow_succ', parameter_higher_eq_zero R π m r hm, zero_mul]

/-- The entire lifted chart increment vanishes, with all Laurent coefficients retained. -/
theorem higherCorrection_chart_eq_zero (m r : ℕ) (hm : m ≤ r)
    (t : Quotient R π m) (q : R[T;T⁻¹]) :
    algebraMap (Quotient R π m) (ChartRing t) (parameter R π m) *
      boundaryLift t (correctionField R π m (higherCorrectionField R π r q)) = 0 := by
  rw [correctionField_higher, ← smul_eq_C_mul, boundaryLift_smul,
    Algebra.smul_def (parameter R π m ^ r) (boundaryLift t (correctionField R π m q)),
    ← mul_assoc, ← map_mul, ← pow_succ',
    parameter_higher_eq_zero R π m r hm, map_zero, zero_mul]

/-- Higher corrections preserve the actual smoothing on every earlier quotient. -/
theorem correctionSmoothing_higher_stable (m r : ℕ) (hm : m ≤ r)
    (t : Quotient R π m) (q : R[T;T⁻¹]) :
    correctionSmoothing R π m t (higherCorrectionField R π r q) = t := by
  rw [correctionSmoothing_higher, parameter_higher_eq_zero R π m r hm,
    zero_mul, add_zero, one_mul]

/-- Both full higher puncture substitutions are identity on every earlier quotient. -/
theorem correctionPunctureFactor_higher_stable (m r : ℕ) (hm : m ≤ r)
    (t : Quotient R π m) (q : R[T;T⁻¹]) (b : Bool) :
    correctionPunctureFactor R π m t (higherCorrectionField R π r q) b = AlgEquiv.refl :=
  nilpotentShearPunctureEquiv_eq_refl _ _ _ _ _
    (higherCorrection_scalar_eq_zero R π m r hm q)
    (higherCorrection_chart_eq_zero R π m r hm t q) b

/-- The full inverse substitutions also stabilize, including the reflected branch. -/
theorem correctionPunctureFactor_higher_symm_stable (m r : ℕ) (hm : m ≤ r)
    (t : Quotient R π m) (q : R[T;T⁻¹]) (b : Bool) :
    (correctionPunctureFactor R π m t (higherCorrectionField R π r q) b).symm =
      AlgEquiv.refl := by
  rw [correctionPunctureFactor_higher_stable R π m r hm]
  rfl

end FLT.Mazur.PolygonArithmeticStages
