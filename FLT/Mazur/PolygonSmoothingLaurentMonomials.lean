/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingOverlapGraph
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Full Laurent coefficients of original smoothing-chart monomials

The relation xy=t contributes the actual power of t to every monomial.
This records the entire arithmetic coefficient before any stage reduction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- An original two-variable monomial retains its full parameter power on the left edge. -/
theorem leftLaurentMap_monomial (v : Fin 2 →₀ ℕ) (r : R) :
    leftLaurentMap t (Ideal.Quotient.mk (relationIdeal t) (MvPolynomial.monomial v r)) =
      C (r * t ^ v 1) * T ((v 0 : ℤ) - v 1) := by
  change MvPolynomial.aeval ![T 1, C t * T (-1)] (MvPolynomial.monomial v r) = _
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_pow, T_pow, mul_one, mul_neg_one, ← map_pow]
    rw [← C_eq_algebraMap r, mul_left_comm (T (v 0 : ℤ)),
      ← mul_assoc, ← map_mul, ← T_add]
    rfl
  · intro k
    exact pow_zero _

/-- Every Laurent coefficient of an original monomial is explicitly determined. -/
theorem leftLaurentMap_monomial_coefficient (v : Fin 2 →₀ ℕ) (r : R) (k : ℤ) :
    (leftLaurentMap t
      (Ideal.Quotient.mk (relationIdeal t) (MvPolynomial.monomial v r))).coeff k =
      if (v 0 : ℤ) - v 1 = k then r * t ^ v 1 else 0 := by
  rw [leftLaurentMap_monomial, ← single_eq_C_mul_T]
  exact Finsupp.single_apply

/-- Nilpotence bounds the negative Laurent tail of every actual chart element. -/
theorem leftLaurentMap_coefficient_below (m : ℕ) (ht : t ^ (m + 1) = 0)
    (z : ChartRing t) (k : ℤ) (hk : k < -(m : ℤ)) :
    (leftLaurentMap t z).coeff k = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on' with
  | monomial v r =>
    rw [leftLaurentMap_monomial_coefficient]
    split_ifs with he
    · have hb : m + 1 ≤ v 1 := by omega
      rw [pow_eq_zero_of_le hb ht, mul_zero]
    · rfl
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_zero]

/-- The original inverse transition bounds the positive incoming Laurent tail. -/
theorem precedingLaurentMap_coefficient_above (m : ℕ) (ht : t ^ (m + 1) = 0)
    (z : ChartRing t) (k : ℤ) (hk : (m : ℤ) < k) :
    (precedingLaurentMap R t z).coeff k = 0 := by
  change (LaurentPolynomial.invert (leftLaurentMap t (branchSwapMap t z))).coeff k = 0
  rw [LaurentPolynomial.invert_apply]
  exact leftLaurentMap_coefficient_below t m ht _ (-k) (by omega)

end FLT.Mazur.PolygonSmoothing
