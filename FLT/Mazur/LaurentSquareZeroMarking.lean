/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Tactic.LinearCombination

/-!
# Exact first-order marking factors on Laurent edges

Square-zero parameters give finite formulas for the entire marking power
and every coefficient of its product with an arbitrary retained numerator.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroMarking
open LaurentPolynomial
variable {R : Type*} [CommRing R]

/-- A square-zero perturbation has an exact power formula in every degree. -/
theorem sub_one_pow (u : R) (hu : u ^ 2 = 0) (d : ℕ) :
    (u - 1) ^ d = (-1 : R) ^ d * (1 - d * u) := by
  induction d with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, sub_zero, mul_one]
  | succ d hd =>
    rw [pow_succ, hd, pow_succ, Nat.cast_succ]
    linear_combination -((-1 : R) ^ d * (d : R)) * hu

/-- The nilpotent monomial remains square-zero on the full Laurent edge. -/
theorem monomial_sq (t : R) (ht : t ^ 2 = 0) (a : ℤ) :
    (C t * T a) ^ 2 = (0 : R[T;T⁻¹]) := by
  rw [mul_pow, ← map_pow, ht, map_zero, zero_mul]

/-- Multiplication by a first-order marking power retains one precise shifted correction. -/
theorem marking_pow_mul (t : R) (ht : t ^ 2 = 0) (a : ℤ) (d : ℕ)
    (p : R[T;T⁻¹]) :
    (C t * T a - 1) ^ d * p =
      C ((-1 : R) ^ d) * (p - C ((d : R) * t) * T a * p) := by
  rw [sub_one_pow _ (monomial_sq t ht a)]
  simp only [map_pow, map_neg, map_one, map_mul, map_natCast]
  ring

/-- The exact coefficient recurrence has no discarded lower terms or parameter cancellation. -/
theorem marking_pow_mul_coefficient (t : R) (ht : t ^ 2 = 0)
    (a : ℤ) (d : ℕ) (p : R[T;T⁻¹]) (k : ℤ) :
    ((C t * T a - 1) ^ d * p).coeff k =
      (-1 : R) ^ d * (p.coeff k - (d : R) * t * p.coeff (k - a)) := by
  rw [marking_pow_mul t ht]
  conv_lhs => rw [← mul_one (C ((-1 : R) ^ d)), ← T_zero, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, ← single_eq_C_mul_T]
  simp only [neg_zero, add_zero, sub_eq_add_neg, add_comm]

/-- Multiplication by the parameter kills precisely the first-order correction. -/
theorem parameter_marking_pow_mul (t : R) (ht : t ^ 2 = 0)
    (a : ℤ) (d : ℕ) (p : R[T;T⁻¹]) :
    C t * ((C t * T a - 1) ^ d * p) = C (t * (-1 : R) ^ d) * p := by
  rw [marking_pow_mul t ht, map_mul]
  have hz : C t * C t = (0 : R[T;T⁻¹]) := by rw [← map_mul, ← pow_two, ht, map_zero]
  simp only [map_mul, map_natCast]
  linear_combination -(C ((-1 : R) ^ d) * (d : R[T;T⁻¹]) * T a * p) * hz

end FLT.Mazur.LaurentSquareZeroMarking
