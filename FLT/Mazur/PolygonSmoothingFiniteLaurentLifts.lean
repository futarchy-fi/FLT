/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFirstLaurentLifts

/-!
# Finite complementary Laurent lifts

The outgoing linear formula discards only negative exponents. Incoming
monomials lift with their exact sign and retain every strictly negative term.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- Vanishing nonnegative coefficients give a zero outgoing lift. -/
theorem outgoingPolynomialLift_eq_zero (p : R[T;T⁻¹])
    (hp : ∀ k : ℤ, 0 ≤ k → p.coeff k = 0) : outgoingPolynomialLift t p = 0 := by
  rw [outgoingPolynomialLift, Finsupp.linearCombination_apply]
  apply Finset.sum_eq_zero
  intro k _
  dsimp only
  by_cases hk : 0 ≤ k
  · rw [hp k hk, zero_smul]
  · rw [ite_eq_right hk, smul_zero]

/-- The outgoing lift is linear whenever the positive tail stops at one. -/
theorem outgoingPolynomialLift_linear (p : R[T;T⁻¹])
    (hp : ∀ k : ℤ, 1 < k → p.coeff k = 0) :
    outgoingPolynomialLift t p = algebraMap R (ChartRing t) (p.coeff 0) +
      algebraMap R (ChartRing t) (p.coeff 1) * leftCoordinate t := by
  have hz := outgoingPolynomialLift_eq_zero t
    (p - (C (p.coeff 0) + C (p.coeff 1) * T 1)) (by
      intro k hk
      rw [← single_eq_C_mul_T, ← single_eq_C]
      simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_single, Finsupp.sub_apply, Finsupp.add_apply,
        Finsupp.single_apply]
      by_cases h0 : k = 0
      · subst k
        simp
      · by_cases h1 : k = 1
        · subst k
          simp
        · simp [Ne.symm h0, Ne.symm h1, hp k (by omega)])
  change (Finsupp.linearCombination R _) _ = 0 at hz
  rw [AddMonoidAlgebra.coeff_sub, map_sub, sub_eq_zero] at hz
  change outgoingPolynomialLift t p = outgoingPolynomialLift t
    (C (p.coeff 0) + C (p.coeff 1) * T 1) at hz
  rw [hz, outgoingPolynomialLift_add, outgoingPolynomialLift_constant]
  have he := outgoingPolynomialLift_monomial t (p.coeff 1) 1
  simpa only [Nat.cast_one, pow_one] using congrArg
    (fun z ↦ algebraMap R (ChartRing t) (p.coeff 0) + z) he

/-- The incoming lift is additive. -/
theorem incomingPolynomialLift_add (p q : R[T;T⁻¹]) :
    incomingPolynomialLift t (p + q) =
      incomingPolynomialLift t p + incomingPolynomialLift t q :=
  (Finsupp.linearCombination R _).map_add _ _

/-- The incoming lift preserves the sign of the original numerator. -/
theorem incomingPolynomialLift_neg (p : R[T;T⁻¹]) :
    incomingPolynomialLift t (-p) = -incomingPolynomialLift t p :=
  (Finsupp.linearCombination R _).map_neg _

/-- A Laurent monomial contributes exactly when its exponent is strictly negative. -/
theorem incomingPolynomialLift_monomial (r : R) (k : ℤ) :
    incomingPolynomialLift t (C r * T k) =
      if k < 0 then algebraMap R (ChartRing t) r * rightCoordinate t ^ (-k).toNat
      else 0 := by
  rw [incomingPolynomialLift, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
  split_ifs
  · exact Algebra.smul_def r (rightCoordinate t ^ (-k).toNat)
  · exact smul_zero _

/-- Constants have no strictly negative incoming part. -/
theorem incomingPolynomialLift_constant (r : R) :
    incomingPolynomialLift t (C r) = 0 := by
  simpa only [T_zero, mul_one, lt_self_iff_false, ite_false] using
    incomingPolynomialLift_monomial t r 0

end FLT.Mazur.PolygonSmoothing
