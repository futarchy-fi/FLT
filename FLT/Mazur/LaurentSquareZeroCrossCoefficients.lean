/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroMarking

/-!
# Solving both first-order marking factors on a Laurent edge

The coefficient formula keeps the correction from each side of the original
cross equation. It applies in every characteristic without dividing by the
smoothing parameter or by the tensor degree.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroMarking
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R) (ht : t ^ 2 = 0)
variable (a b : ℤ) (d : ℕ) (p q : R[T;T⁻¹])
variable (he : (C t * T a - 1) ^ d * p = (C t * T b - 1) ^ d * q)
include ht he

/-- The original cross equation equates every parameter-multiplied coefficient. -/
theorem cross_parameter_coefficient (k : ℤ) : t * p.coeff k = t * q.coeff k := by
  have hh := congrArg (fun z ↦ C t * z) he
  rw [parameter_marking_pow_mul t ht, parameter_marking_pow_mul t ht] at hh
  have hc := congrArg (fun z : R[T;T⁻¹] ↦ z.coeff k) hh
  simp only [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add] at hc
  apply (((isUnit_one : IsUnit (1 : R)).neg).pow d).isRegular.left
  dsimp only
  simpa only [mul_comm t ((-1 : R) ^ d), mul_assoc] using hc

/-- Both marking factors contribute to the exact, solved coefficient equation. -/
theorem cross_coefficient (k : ℤ) :
    p.coeff k = q.coeff k + (d : R) * t * (q.coeff (k - a) - q.coeff (k - b)) := by
  have hc := congrArg (fun z : R[T;T⁻¹] ↦ z.coeff k) he
  rw [marking_pow_mul_coefficient t ht, marking_pow_mul_coefficient t ht] at hc
  have hc' := (((isUnit_one : IsUnit (1 : R)).neg).pow d).isRegular.left hc
  have hp := cross_parameter_coefficient t ht a b d p q he (k - a)
  linear_combination hc' + (d : R) * hp

end FLT.Mazur.LaurentSquareZeroMarking
