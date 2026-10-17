/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentBoundaryCorrectionNaturality
public import FLT.Mazur.PolygonArithmeticStageCoefficients

/-!
# Compatible arithmetic lifts of finite Laurent correction fields

Lift a finite Laurent field once to the original coefficient ring. Its
specializations at all arithmetic orders then form a compatible family,
including both parts of the split and their reciprocal fields.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
open LaurentBoundaryCorrectionSplit LaurentBoundaryVectorField
variable (R : Type*) [CommRing R] (π : R)

/-- Specialize a complete integral Laurent field to a finite arithmetic order. -/
def correctionField (m : ℕ) (q : R[T;T⁻¹]) : (Quotient R π m)[T;T⁻¹] :=
  coeffMap (algebraMap R (Quotient R π m)) q

/-- Every coefficient of the integral field is retained under specialization. -/
theorem correctionField_coeff (m : ℕ) (q : R[T;T⁻¹]) (k : ℤ) :
    (correctionField R π m q).coeff k = algebraMap R (Quotient R π m) (q.coeff k) :=
  coeffMap_coeff _ _ _

/-- The full finite field commutes with each successive arithmetic quotient. -/
theorem correctionField_restriction (m : ℕ) (q : R[T;T⁻¹]) :
    coeffMap (restriction R π m).toRingHom (correctionField R π (m + 1) q) =
      correctionField R π m q := by
  ext k
  rw [coeffMap_coeff, correctionField_coeff, correctionField_coeff]
  exact (restriction R π m).commutes (q.coeff k)

/-- Every finite arithmetic field has a finite Laurent lift over the original ring. -/
theorem correctionField_surjective (m : ℕ) : Function.Surjective (correctionField R π m) :=
  coeffMap_surjective _ (Ideal.Quotient.mk_surjective)

/-- Choose a single integral lift, before any higher arithmetic order is selected. -/
def integralCorrectionLift (m : ℕ) (q : (Quotient R π m)[T;T⁻¹]) : R[T;T⁻¹] :=
  (correctionField_surjective R π m q).choose

/-- The integral lift recovers the entire prescribed finite field at its original order. -/
theorem integralCorrectionLift_spec (m : ℕ) (q : (Quotient R π m)[T;T⁻¹]) :
    correctionField R π m (integralCorrectionLift R π m q) = q :=
  (correctionField_surjective R π m q).choose_spec

/-- The positive fields at all orders come from one integral positive field. -/
theorem correctionField_positive (m : ℕ) (q : R[T;T⁻¹]) :
    correctionField R π m (positivePart q) = positivePart (correctionField R π m q) :=
  (positivePart_coeffMap _ _).symm

/-- The reciprocal complementary fields also form a compatible arithmetic family. -/
theorem correctionField_reciprocal (m : ℕ) (q : R[T;T⁻¹]) :
    correctionField R π m (reciprocalField (nonpositivePart q)) =
      reciprocalField (nonpositivePart (correctionField R π m q)) := by
  unfold correctionField
  rw [nonpositivePart_coeffMap, reciprocalField_coeffMap]

/-- Specialization preserves the complete positive support of a boundary field. -/
theorem correctionField_boundary (m : ℕ) (q : R[T;T⁻¹])
    (hq : ∀ k : ℤ, k ≤ 0 → q.coeff k = 0) (k : ℤ) (hk : k ≤ 0) :
    (correctionField R π m q).coeff k = 0 := by
  rw [correctionField_coeff, hq k hk, map_zero]

end FLT.Mazur.PolygonArithmeticStages
