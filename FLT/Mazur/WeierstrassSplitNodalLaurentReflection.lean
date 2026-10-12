/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalLaurent

/-!
# Laurent coordinates under interchange of the two tangent roots

Changing the tangent unit from a to -a and inverting the parameter gives the
same homogeneous cubic point after the actual shear and a Laurent unit rescaling.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R : Type*} [CommRing R] (a : Rˣ)
local notation "L" => R[T;T⁻¹]
local notation "t" => (LaurentPolynomial.T 1 : L)
local notation "q" => (LaurentPolynomial.T (-1) : L)

/-- Interchanging the ordered roots changes the horizontal infinity function by t inverse. -/
theorem splitNodalLaurent_reflect_x :
    LaurentPolynomial.invert (splitNodalLaurentX (-a)) = q * splitNodalLaurentX a := by
  simp only [splitNodalLaurentX, map_mul, map_sub, map_one, LaurentPolynomial.invert_T,
    show algebraMap R L = LaurentPolynomial.C from rfl, LaurentPolynomial.invert_C,
    inv_neg, Units.val_neg, map_neg]
  have ht : q * t = 1 := by rw [← LaurentPolynomial.T_add]; rfl
  linear_combination -(LaurentPolynomial.C (↑a⁻¹ : R)) * ht

/-- The full vertical infinity function has the same homogeneous rescaling. -/
theorem splitNodalLaurent_reflect_z :
    LaurentPolynomial.invert (splitNodalLaurentZ (-a)) = q * splitNodalLaurentZ a := by
  rw [splitNodalLaurentZ, map_mul, map_pow, splitNodalLaurent_reflect_x,
    LaurentPolynomial.invert_T]
  change (q * splitNodalLaurentX a) ^ 3 * t = q * (splitNodalLaurentX a ^ 3 * q)
  have ht : q * t = 1 := by rw [← LaurentPolynomial.T_add]; rfl
  linear_combination q ^ 2 * splitNodalLaurentX a ^ 3 * ht

/-- The actual opposite-root shear has the invertible vertical homogeneous coordinate. -/
theorem splitNodalLaurent_reflect_y :
    1 - algebraMap R L (a : R) *
      LaurentPolynomial.invert (splitNodalLaurentX (-a)) = q := by
  rw [splitNodalLaurent_reflect_x]
  have ht : q * t = 1 := by rw [← LaurentPolynomial.T_add]; rfl
  linear_combination -q * splitNodalLaurent_tangent a - ht

end FLT.Mazur.WeierstrassIntegralChart
