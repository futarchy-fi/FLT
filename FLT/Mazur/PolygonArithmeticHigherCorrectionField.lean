/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCorrectionPunctures
public import FLT.Mazur.PolygonArithmeticCorrectionPunctureRestriction

/-!
# Integral correction fields at arbitrary positive parameter order

Multiplying a single integral Laurent field by pi^r supplies a correction of
order r+1. Existing full node and puncture constructions then preserve its
entire support, exact smoothing drift, inverse, and coefficient squares.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonSmoothing PolygonScalingNaturality
open LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- A fixed integral field for a correction of order r+1. -/
def higherCorrectionField (r : ℕ) (q : R[T;T⁻¹]) : R[T;T⁻¹] := C (π ^ r) * q

/-- Scaling keeps every original Laurent coefficient and both tails. -/
theorem higherCorrectionField_coeff (r : ℕ) (q : R[T;T⁻¹]) (d : ℤ) :
    (higherCorrectionField R π r q).coeff d = π ^ r * q.coeff d := by
  rw [higherCorrectionField, ← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
    smul_eq_mul]

/-- The scaled field specializes to the exact higher parameter power times the original field. -/
theorem correctionField_higher (m r : ℕ) (q : R[T;T⁻¹]) :
    correctionField R π m (higherCorrectionField R π r q) =
      C (parameter R π m ^ r) * correctionField R π m q := by
  simp only [correctionField, higherCorrectionField, map_mul, coeffMap_C, map_pow]
  rfl

/-- Higher corrections preserve vanishing at the boundary origin. -/
theorem higherCorrectionField_boundary (r : ℕ) (q : R[T;T⁻¹])
    (hq : ∀ d : ℤ, d ≤ 0 → q.coeff d = 0) (d : ℤ) (hd : d ≤ 0) :
    (higherCorrectionField R π r q).coeff d = 0 := by
  rw [higherCorrectionField_coeff, hq d hd, mul_zero]

/-- The exact smoothing drift begins in the intended order, with its linear coefficient kept. -/
theorem correctionSmoothing_higher (m r : ℕ) (t : Quotient R π m) (q : R[T;T⁻¹]) :
    correctionSmoothing R π m t (higherCorrectionField R π r q) =
      (1 + parameter R π m ^ (r + 1) * algebraMap R _ (q.coeff 1)) * t := by
  rw [correctionSmoothing, higherCorrectionField_coeff, map_mul, map_pow]
  change (1 + parameter R π m * (parameter R π m ^ r * _)) * t = _
  rw [pow_succ' (parameter R π m), mul_assoc]

/-- The whole outgoing puncture of the actual higher node correction has its exact increment. -/
theorem correctionPunctureFactor_higher_coordinate (m r : ℕ) (t : Quotient R π m)
    (q : R[T;T⁻¹]) (hq : ∀ d : ℤ, d ≤ 0 → q.coeff d = 0) :
    correctionPunctureFactor R π m t (higherCorrectionField R π r q) true (T 1) =
      T 1 + C (parameter R π m ^ (r + 1)) * correctionField R π m q := by
  let v := higherCorrectionField R π r q
  have hv : ∀ d : ℤ, d ≤ 0 → (correctionField R π m v).coeff d = 0 :=
    correctionField_boundary R π m v (higherCorrectionField_boundary R π r q hq)
  change LaurentUnitPoints.evalUnit (nilpotentShearLeftUnit t (parameter R π m)
    _ (boundaryLift t (correctionField R π m v))) (T 1) = _
  rw [LaurentUnitPoints.evalUnit_T, zpow_one, nilpotentShearLeftUnit_val,
    mul_add, mul_one, mul_left_comm, boundaryLift_value t _ hv]
  change T 1 + C (parameter R π m) *
    correctionField R π m (higherCorrectionField R π r q) = _
  rw [correctionField_higher, ← mul_assoc, ← map_mul, ← pow_succ']

end FLT.Mazur.PolygonArithmeticStages
