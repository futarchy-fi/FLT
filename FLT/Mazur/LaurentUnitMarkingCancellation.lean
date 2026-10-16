/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Cancellation at the unit Laurent marking over arbitrary rings

The equation T-1 is regular even with nilpotent coefficients. Its reciprocal
equation differs by the explicit unit -T⁻¹, giving exact numerator transitions.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.LaurentUnitMarking
open LaurentPolynomial
variable (R : Type*) [CommRing R]

/-- The original unit marking equation is regular over every coefficient ring. -/
theorem equation_regular : IsRegular (T 1 - 1 : R[T;T⁻¹]) := by
  have hM : ∀ p ∈ Submonoid.powers (Polynomial.X : R[X]), IsRegular p := by
    rintro p ⟨k, rfl⟩
    exact Polynomial.monic_X.isRegular.pow k
  have hp : IsRegular (Polynomial.X - 1 : R[X]) :=
    (Polynomial.monic_X_sub_C (1 : R)).isRegular
  have he := (IsLocalization.isRegular_mk' (S := R[T;T⁻¹]) hM
    (r := Polynomial.X - 1) (m := 1)).mpr hp
  simpa only [IsLocalization.mk'_one, algebraMap_eq_toLaurent,
    map_sub, Polynomial.toLaurent_X, map_one] using he

/-- The incoming equation is the outgoing equation times its actual reciprocal unit. -/
theorem inverse_equation : (T (-1) - 1 : R[T;T⁻¹]) = (T 1 - 1) * (-T (-1)) := by
  rw [mul_neg, sub_mul, ← T_add]
  simp only [Int.reduceAdd, T_zero, one_mul, neg_sub]

/-- Cancelling the regular marking power retains the entire original numerator. -/
theorem numerator_transition (d : ℕ) (p q : R[T;T⁻¹])
    (he : (T 1 - 1) ^ d * q = (T (-1) - 1) ^ d * p) :
    q = (-T (-1)) ^ d * p := by
  apply ((equation_regular R).pow d).left
  dsimp only
  rw [← mul_assoc, ← mul_pow, ← inverse_equation]
  exact he

/-- Every coefficient, including the lower terms, follows the exact signed Laurent shift. -/
theorem numerator_transition_coefficient (d : ℕ) (p q : R[T;T⁻¹])
    (he : (T 1 - 1) ^ d * q = (T (-1) - 1) ^ d * p) (k : ℤ) :
    q.coeff k = (-1 : R) ^ d * p.coeff (k + d) := by
  rw [numerator_transition R d p q he, neg_pow, T_pow, mul_neg_one]
  have hc : (-1 : R[T;T⁻¹]) ^ d = C ((-1 : R) ^ d) := by
    simp only [map_pow, map_neg, map_one]
  rw [hc, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_neg, add_comm]

end FLT.Mazur.LaurentUnitMarking
