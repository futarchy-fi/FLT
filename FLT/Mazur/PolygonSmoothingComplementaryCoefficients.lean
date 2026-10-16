/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingFiniteLaurentLifts

/-!
# Coefficients of the two complementary node lifts

The outgoing polynomial retains the entire nonnegative Laurent part. The
incoming polynomial retains the entire negative part on the inverse branch.
Their opposite tails vanish before any arithmetic reduction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- The outgoing lift of any integer monomial uses precisely its nonnegative exponent. -/
theorem outgoingPolynomialLift_integer (r : R) (k : ℤ) :
    outgoingPolynomialLift t (C r * T k) =
      if 0 ≤ k then algebraMap R (ChartRing t) r * leftCoordinate t ^ k.toNat else 0 := by
  rw [outgoingPolynomialLift, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
  split_ifs
  · exact Algebra.smul_def r (leftCoordinate t ^ k.toNat)
  · exact smul_zero _

/-- Every outgoing coefficient is retained, with zero negative tail. -/
theorem outgoingPolynomialLift_left_coeff (p : R[T;T⁻¹]) (k : ℤ) :
    (leftLaurentMap t (outgoingPolynomialLift t p)).coeff k =
      if 0 ≤ k then p.coeff k else 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [outgoingPolynomialLift_add, map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | C_mul_T n r =>
    rw [outgoingPolynomialLift_integer]
    by_cases hn : 0 ≤ n
    · rw [ite_eq_left hn]
      simp only [map_mul, AlgHom.commutes, map_pow, leftLaurentMap_left, T_pow,
        ← C_eq_algebraMap, Int.toNat_of_nonneg hn, ← single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp_all
      all_goals omega
    · rw [ite_eq_right hn, map_zero]
      simp only [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp_all

/-- The outgoing polynomial has no negative coefficient on the incoming branch either. -/
theorem outgoingPolynomialLift_preceding_negative (p : R[T;T⁻¹]) (k : ℤ) (hk : k < 0) :
    (precedingLaurentMap R t (outgoingPolynomialLift t p)).coeff k = 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [outgoingPolynomialLift_add, map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp, hq, add_zero]
  | C_mul_T n r =>
    rw [outgoingPolynomialLift_integer]
    split_ifs with hn
    · simp only [map_mul, AlgHom.commutes, map_pow, precedingLaurentMap_left, mul_pow,
        T_pow, mul_one, Int.toNat_of_nonneg hn, ← C_eq_algebraMap]
      rw [← map_pow, ← mul_assoc, ← map_mul, ← single_eq_C_mul_T]
      exact Finsupp.single_eq_of_ne (show k ≠ n by omega)
    · simp

/-- The incoming polynomial retains exactly the negative Laurent coefficients. -/
theorem incomingPolynomialLift_preceding_coeff (p : R[T;T⁻¹]) (k : ℤ) :
    (precedingLaurentMap R t (incomingPolynomialLift t p)).coeff k =
      if k < 0 then p.coeff k else 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [incomingPolynomialLift_add, map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | C_mul_T n r =>
    rw [incomingPolynomialLift_monomial]
    by_cases hn : n < 0
    · rw [ite_eq_left hn]
      simp only [map_mul, AlgHom.commutes, map_pow, precedingLaurentMap_right, T_pow,
        neg_mul, Int.toNat_of_nonneg (show 0 ≤ -n by omega),
        ← C_eq_algebraMap, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply]
      split_ifs <;> simp_all
      all_goals omega
    · rw [ite_eq_right hn, map_zero]
      simp only [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp_all

/-- The incoming polynomial contributes no nonnegative outgoing coefficient. -/
theorem incomingPolynomialLift_left_nonnegative (p : R[T;T⁻¹]) (k : ℤ) (hk : 0 ≤ k) :
    (leftLaurentMap t (incomingPolynomialLift t p)).coeff k = 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [incomingPolynomialLift_add, map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp, hq, add_zero]
  | C_mul_T n r =>
    rw [incomingPolynomialLift_monomial]
    split_ifs with hn
    · simp only [map_mul, AlgHom.commutes, map_pow, leftLaurentMap_right, mul_pow,
        T_pow, mul_neg_one, Int.toNat_of_nonneg (show 0 ≤ -n by omega), neg_neg,
        ← C_eq_algebraMap]
      rw [← map_pow, ← mul_assoc, ← map_mul, ← single_eq_C_mul_T]
      exact Finsupp.single_eq_of_ne (show k ≠ n by omega)
    · simp

end FLT.Mazur.PolygonSmoothing
