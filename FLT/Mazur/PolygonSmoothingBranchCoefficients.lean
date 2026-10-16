/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingLaurentMonomials

/-!
# Coefficient compatibility between both branches of the same node

The incoming and outgoing Laurent coefficients retain the exact powers of
the smoothing parameter. These identities hold before any reduction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- The incoming restriction sends the first coordinate to tT. -/
theorem precedingLaurentMap_left :
    precedingLaurentMap R t (leftCoordinate t) = C t * T 1 := by
  simp [precedingLaurentMap]

/-- A quotient monomial is the corresponding product of original coordinates. -/
theorem chart_monomial (v : Fin 2 →₀ ℕ) (r : R) :
    Ideal.Quotient.mk (relationIdeal t) (MvPolynomial.monomial v r) =
      algebraMap R (ChartRing t) r * leftCoordinate t ^ v 0 * rightCoordinate t ^ v 1 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two, map_mul, map_pow, ← mul_assoc]
    rfl
  · intro k
    exact pow_zero _

/-- The incoming monomial keeps the power of t contributed by the first coordinate. -/
theorem precedingLaurentMap_monomial (v : Fin 2 →₀ ℕ) (r : R) :
    precedingLaurentMap R t
        (Ideal.Quotient.mk (relationIdeal t) (MvPolynomial.monomial v r)) =
      C (r * t ^ v 0) * T ((v 0 : ℤ) - v 1) := by
  rw [chart_monomial, map_mul, map_mul, AlgHom.commutes, map_pow, map_pow,
    precedingLaurentMap_left, precedingLaurentMap_right]
  simp only [mul_pow, T_pow, mul_one, mul_neg_one, ← map_pow, ← C_eq_algebraMap]
  rw [← mul_assoc, ← map_mul, mul_assoc, ← T_add]
  rfl

/-- Every incoming monomial coefficient uses the same exponent as the outgoing one. -/
theorem precedingLaurentMap_monomial_coefficient (v : Fin 2 →₀ ℕ) (r : R) (k : ℤ) :
    (precedingLaurentMap R t
      (Ideal.Quotient.mk (relationIdeal t) (MvPolynomial.monomial v r))).coeff k =
      if (v 0 : ℤ) - v 1 = k then r * t ^ v 0 else 0 := by
  rw [precedingLaurentMap_monomial, ← single_eq_C_mul_T]
  exact Finsupp.single_apply

/-- Nonnegative incoming coefficients are parameter powers times the outgoing coefficients. -/
theorem branch_coefficient_nonneg (z : ChartRing t) (k : ℕ) :
    (precedingLaurentMap R t z).coeff k = t ^ k * (leftLaurentMap t z).coeff k := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on' with
  | monomial v r =>
    rw [precedingLaurentMap_monomial_coefficient, leftLaurentMap_monomial_coefficient]
    split_ifs with he
    · have hv : v 0 = k + v 1 := by omega
      rw [hv, pow_add]
      ring
    · exact (mul_zero _).symm
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

/-- Nonpositive outgoing coefficients are parameter powers times the incoming coefficients. -/
theorem branch_coefficient_nonpos (z : ChartRing t) (k : ℕ) :
    (leftLaurentMap t z).coeff (-(k : ℤ)) =
      t ^ k * (precedingLaurentMap R t z).coeff (-(k : ℤ)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on' with
  | monomial v r =>
    rw [precedingLaurentMap_monomial_coefficient, leftLaurentMap_monomial_coefficient]
    split_ifs with he
    · have hv : v 1 = k + v 0 := by omega
      rw [hv, pow_add]
      ring
    · exact (mul_zero _).symm
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

end FLT.Mazur.PolygonSmoothing
