/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchCoefficients
public import FLT.Mazur.LaurentSquareZeroMarking

/-!
# Constant coefficients across square-zero chart branches

The two branches have the same constant coefficient. The nilpotent marking
factors change that coefficient only by the degree sign, because their
correction term contains the square of the original parameter.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0)

/-- Both original Laurent branches have the same constant coefficient. -/
theorem branch_coefficient_zero (z : ChartRing t) :
    (precedingLaurentMap R t z).coeff 0 = (leftLaurentMap t z).coeff 0 := by
  simpa only [Nat.cast_zero, pow_zero, one_mul] using branch_coefficient_nonneg t z 0

include ht

/-- The incoming marking correction has zero constant coefficient at first order. -/
theorem first_incoming_marking_constant (d : ℕ) (z : ChartRing t) :
    ((C t * T (-1) - 1) ^ d * precedingLaurentMap R t z).coeff 0 =
      (-1 : R) ^ d * (leftLaurentMap t z).coeff 0 := by
  rw [LaurentSquareZeroMarking.marking_pow_mul_coefficient t ht]
  have hz : t * (precedingLaurentMap R t z).coeff 1 = 0 := by
    rw [show (1 : ℤ) = (1 : ℕ) by rfl, branch_coefficient_nonneg, pow_one,
      ← mul_assoc, ← pow_two, ht, zero_mul]
  rw [show (0 - -1 : ℤ) = 1 by rfl, mul_assoc (d : R), hz, mul_zero, sub_zero,
    branch_coefficient_zero]

/-- The outgoing marking correction also has zero constant coefficient. -/
theorem first_outgoing_marking_constant (d : ℕ) (z : ChartRing t) :
    ((C t * T 1 - 1) ^ d * leftLaurentMap t z).coeff 0 =
      (-1 : R) ^ d * (leftLaurentMap t z).coeff 0 := by
  rw [LaurentSquareZeroMarking.marking_pow_mul_coefficient t ht]
  have hz : t * (leftLaurentMap t z).coeff (-1) = 0 := by
    rw [show (-1 : ℤ) = -(1 : ℕ) by rfl, branch_coefficient_nonpos, pow_one,
      ← mul_assoc, ← pow_two, ht, zero_mul]
  rw [show (0 - 1 : ℤ) = -1 by rfl, mul_assoc (d : R), hz, mul_zero, sub_zero]

end FLT.Mazur.PolygonSmoothing
