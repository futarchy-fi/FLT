/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalFirstResidualFactors
public import FLT.Mazur.PolygonArithmeticLaurentCorrectionLift

/-!
# Integral lifts of the actual first residual fields

Choose full finite Laurent lifts over the original ring for both residual
coordinates. Their specializations and both boundary pieces are compatible
at every arithmetic order. These are lifts of the first correction, not a
claim that it eliminates the higher-order residual by itself.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages LaurentPolynomial PolygonScalingNaturality
open LaurentBoundaryCorrectionSplit LaurentBoundaryVectorField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "q" => arithmeticFirstResidualField hπ data H j hj u hu

/-- Choose a single integral finite Laurent lift for each actual first residual field. -/
def arithmeticResidualIntegralField (b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π 1 (q b)

local notation "Q" => arithmeticResidualIntegralField hπ data H j hj u hu

/-- The whole actual residual field is recovered at first order, with both Laurent tails. -/
theorem arithmeticResidualIntegralField_first (b : Bool) : correctionField R π 1 (Q b) = q b :=
  integralCorrectionLift_spec R π 1 (q b)

/-- The integral field realizes the original residual coordinate at first order. -/
theorem arithmeticResidualIntegralField_coordinate (b : Bool) :
    arithmeticTerminalResidualEquiv data H 1 j hj u hu b (T 1) =
      T 1 + C (parameter R π 1) * correctionField R π 1 (Q b) := by
  rw [arithmeticResidualIntegralField_first]
  exact arithmeticFirstResidualField_coordinate hπ data H j hj u hu b

/-- The retained correction has one fixed integral reciprocal boundary field. -/
def arithmeticRetainedIntegralField (b : Bool) : R[T;T⁻¹] :=
  reciprocalField (nonpositivePart (Q b))

/-- First specialization gives exactly the original full retained boundary correction. -/
theorem arithmeticRetainedIntegralField_first (b : Bool) :
    correctionField R π 1 (arithmeticRetainedIntegralField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (q b)) := by
  rw [arithmeticRetainedIntegralField, correctionField_reciprocal,
    arithmeticResidualIntegralField_first]

/-- This reciprocal field has no linear term, so the retained smoothing need not drift. -/
theorem arithmeticRetainedIntegralField_linear (b : Bool) :
    (arithmeticRetainedIntegralField hπ data H j hj u hu b).coeff 1 = 0 := by
  rw [arithmeticRetainedIntegralField, reciprocalField_coeff, nonpositivePart_coeff]
  norm_num

/-- The retained fields vanish at their boundary origin before any quotient is taken. -/
theorem arithmeticRetainedIntegralField_boundary (b : Bool) (k : ℤ) (hk : k ≤ 0) :
    (arithmeticRetainedIntegralField hπ data H j hj u hu b).coeff k = 0 :=
  reciprocal_nonpositive_coeff (Q b) k hk

/-- Every successive quotient retains the same complete lifted correction. -/
theorem arithmeticRetainedIntegralField_restriction (m : ℕ) (b : Bool) :
    coeffMap (restriction R π m).toRingHom
        (correctionField R π (m + 1) (arithmeticRetainedIntegralField hπ data H j hj u hu b)) =
      correctionField R π m (arithmeticRetainedIntegralField hπ data H j hj u hu b) :=
  correctionField_restriction R π m _

end FLT.Mazur.WeierstrassDividedDepth
