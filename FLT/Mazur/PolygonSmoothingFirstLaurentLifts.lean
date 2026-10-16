/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingLaurentReconstruction

/-!
# Explicit polynomial lifts in the unchanged first-order node ring

These formulas evaluate the complementary Laurent lifts. The incoming lift
retains its actual negative coefficient, including a possible nilpotent term.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- The outgoing lift respects addition of the original Laurent polynomials. -/
theorem outgoingPolynomialLift_add (p q : R[T;T⁻¹]) :
    outgoingPolynomialLift t (p + q) =
      outgoingPolynomialLift t p + outgoingPolynomialLift t q := by
  exact (Finsupp.linearCombination R _).map_add _ _

/-- A nonnegative Laurent monomial lifts to the same original coordinate monomial. -/
theorem outgoingPolynomialLift_monomial (r : R) (k : ℕ) :
    outgoingPolynomialLift t (C r * T k) =
      algebraMap R (ChartRing t) r * leftCoordinate t ^ k := by
  rw [outgoingPolynomialLift, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single,
    Nat.cast_nonneg, ite_true, Int.toNat_natCast]
  exact Algebra.smul_def r (leftCoordinate t ^ k)

/-- A Laurent constant lifts to its unchanged scalar in the node ring. -/
theorem outgoingPolynomialLift_constant (r : R) :
    outgoingPolynomialLift t (C r) = algebraMap R (ChartRing t) r := by
  simpa only [Nat.cast_zero, T_zero, mul_one, pow_zero] using
    outgoingPolynomialLift_monomial t r 0

/-- If the negative tail stops at minus one, its lift is the actual linear incoming term. -/
theorem incomingPolynomialLift_linear (p : R[T;T⁻¹])
    (hp : ∀ k : ℤ, k < -1 → p.coeff k = 0) :
    incomingPolynomialLift t p = algebraMap R (ChartRing t) (p.coeff (-1)) *
      rightCoordinate t := by
  rw [incomingPolynomialLift, Finsupp.linearCombination_apply,
    Finsupp.sum_eq_single (-1)]
  · simp only [Int.reduceNeg, Int.reduceLT, ite_true, Int.toNat_one, pow_one]
    exact Algebra.smul_def (p.coeff (-1)) (rightCoordinate t)
  · intro k _ hk
    by_cases hn : k < 0
    · rw [hp k (by omega), zero_smul]
    · rw [ite_eq_right hn, smul_zero]
  · intro _
    exact zero_smul R _

/-- Every negative outgoing coefficient is killed by a square-zero parameter. -/
theorem parameter_leftLaurentMap_negative (ht : t ^ 2 = 0)
    (z : ChartRing t) (k : ℤ) (hk : k < 0) :
    t * (leftLaurentMap t z).coeff k = 0 := by
  by_cases he : k = -1
  · rw [he, show (-1 : ℤ) = -(1 : ℕ) by rfl, branch_coefficient_nonpos, pow_one,
      ← mul_assoc, ← pow_two, ht, zero_mul]
  · rw [leftLaurentMap_coefficient_below t 1 ht z k (by omega), mul_zero]

end FLT.Mazur.PolygonSmoothing
