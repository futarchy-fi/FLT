/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentNodePrincipalParts
public import FLT.Mazur.PolygonFirstNodePolynomialDescent

/-!
# Clearing finite boundary poles by a positive coordinate power

Every Laurent polynomial becomes a polynomial vanishing at the origin after
a sufficiently positive shift. The same holds for powers of any scaled
coordinate, over arbitrary coefficient rings and in every characteristic.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.LaurentBoundaryTailShift
open LaurentPolynomial LaurentPositivePart LaurentNodePrincipalParts
variable {R : Type} [CommRing R]

/-- Scalar coefficients cannot create a boundary pole when the entire tail vanishes. -/
theorem tail_C_mul_zero (r : R) (p : R[T;T⁻¹]) (hp : boundaryTail p = 0) :
    boundaryTail (C r * p) = 0 := by
  rw [← smul_eq_C_mul]
  change tailLinear (r • p) = 0
  rw [map_smul]
  change r • boundaryTail p = 0
  rw [hp, smul_zero]

/-- Some strictly positive coordinate shift clears all poles and the constant term. -/
theorem exists_positive_shift (p : R[T;T⁻¹]) :
    ∃ m : ℕ, 0 < m ∧ boundaryTail (T (m : ℤ) * p) = 0 := by
  obtain ⟨m, q, hq⟩ := exists_T_pow p
  refine ⟨m + 1, by omega, ?_⟩
  have he : (q * Polynomial.X).toLaurent = T ((m + 1 : ℕ) : ℤ) * p := by
    rw [map_mul, Polynomial.toLaurent_X, hq, mul_assoc, ← T_add]
    simp only [Nat.cast_add, Nat.cast_one, mul_comm]
  rw [← he]
  apply PolygonInfinitesimalStages.boundaryTail_polynomial_zero R
  simp only [Polynomial.coeff_mul_X_zero]

/-- Powers of a scaled coordinate clear every Laurent boundary obstruction. -/
theorem exists_scaled_power (a : R) (p : R[T;T⁻¹]) :
    ∃ m : ℕ, 0 < m ∧ boundaryTail ((C a * T 1) ^ m * p) = 0 := by
  obtain ⟨m, hm, hp⟩ := exists_positive_shift p
  refine ⟨m, hm, ?_⟩
  have he : (C a * T 1) ^ m * p = C (a ^ m) * (T (m : ℤ) * p) := by
    rw [mul_pow, ← map_pow, T_pow, mul_one, mul_assoc]
  rw [he]
  exact tail_C_mul_zero _ _ hp

/-- Natural multiples also retain the cleared boundary condition. -/
theorem tail_nsmul_zero (m : ℕ) (p : R[T;T⁻¹]) (hp : boundaryTail p = 0) :
    boundaryTail (m • p) = 0 := by
  change tailLinear (m • p) = 0
  rw [map_nsmul]
  change m • boundaryTail p = 0
  rw [hp, nsmul_zero]

end FLT.Mazur.LaurentBoundaryTailShift
