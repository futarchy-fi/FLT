/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFiniteLaurentLifts

/-!
# Incoming lifts of the marked quadratic and cubic transitions

The signed reciprocal transition retains the exact lower coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t a b c : R)
local notation "ρ" => algebraMap R (ChartRing t)
local notation "y" => rightCoordinate t

/-- A Laurent monomial shifts its exponent without changing its coefficient. -/
theorem laurent_monomial_shift (r : R) (k l : ℤ) :
    T k * (C r * T l) = C r * T (k + l) := by
  rw [mul_left_comm, ← T_add]

/-- The reciprocal quadratic retains both incoming terms. -/
theorem incomingPolynomialLift_reciprocal_quadratic :
    incomingPolynomialLift t ((-T (-1)) ^ 2 *
      (C a + C b * T 1 + C a * T 2)) = (ρ) a * (y) ^ 2 + (ρ) b * (y) := by
  have he : (-T (-1) : R[T;T⁻¹]) ^ 2 * (C a + C b * T 1 + C a * T 2) =
      C a * T (-2) + C b * T (-1) + C a := by
    simp only [neg_sq, T_pow, Nat.cast_ofNat, Int.reduceMul, mul_add, laurent_monomial_shift,
      Int.reduceAdd, T_zero, mul_one]
    rw [mul_comm]
  rw [he, incomingPolynomialLift_add, incomingPolynomialLift_add,
    incomingPolynomialLift_monomial, incomingPolynomialLift_monomial,
    incomingPolynomialLift_constant]
  simp only [Int.reduceLT, ite_true, Int.reduceNeg, Int.reduceToNat, pow_one, add_zero]

/-- The reciprocal cubic includes the signs of all three incoming coefficients. -/
theorem incomingPolynomialLift_reciprocal_cubic :
    incomingPolynomialLift t ((-T (-1)) ^ 3 *
      (-C a + C b * T 1 + C c * T 2 + C a * T 3)) =
      (ρ) a * (y) ^ 3 - (ρ) b * (y) ^ 2 - (ρ) c * (y) := by
  have he : (-T (-1) : R[T;T⁻¹]) ^ 3 *
      (-C a + C b * T 1 + C c * T 2 + C a * T 3) =
      C a * T (-3) + -(C b * T (-2)) + -(C c * T (-1)) + -C a := by
    simp only [Odd.neg_pow (by decide : Odd 3), T_pow, Nat.cast_ofNat,
      neg_mul, mul_add, mul_neg, laurent_monomial_shift, Int.reduceAdd, T_zero, mul_one]
    ring
  rw [he, incomingPolynomialLift_add, incomingPolynomialLift_add,
    incomingPolynomialLift_add, incomingPolynomialLift_neg,
    incomingPolynomialLift_neg, incomingPolynomialLift_neg,
    incomingPolynomialLift_monomial, incomingPolynomialLift_monomial,
    incomingPolynomialLift_monomial, incomingPolynomialLift_constant]
  simp only [Int.reduceLT, ite_true, Int.reduceNeg, Int.reduceToNat,
    pow_one, neg_zero, add_zero, sub_eq_add_neg]

end FLT.Mazur.PolygonSmoothing
