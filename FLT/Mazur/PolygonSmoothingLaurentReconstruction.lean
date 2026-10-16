/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchCoefficients
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Reconstructing the entire node from its two Laurent branches

Nonnegative outgoing coefficients and strictly negative incoming coefficients
give an exact polynomial expression in the original node coordinates. No
coefficient is divided by the parameter, including at nilpotent stages.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)

/-- Lift the nonnegative Laurent terms in the original outgoing coordinate. -/
def outgoingPolynomialLift (p : R[T;T⁻¹]) : ChartRing t :=
  Finsupp.linearCombination R
    (fun k : ℤ ↦ if 0 ≤ k then leftCoordinate t ^ k.toNat else 0) p.coeff

/-- Lift the strictly negative terms in the original incoming coordinate. -/
def incomingPolynomialLift (p : R[T;T⁻¹]) : ChartRing t :=
  Finsupp.linearCombination R
    (fun k : ℤ ↦ if k < 0 then rightCoordinate t ^ (-k).toNat else 0) p.coeff

/-- Mixed original monomials reduce using precisely the power of the smoothing parameter. -/
theorem coordinate_mixedPower (a b : ℕ) :
    leftCoordinate t ^ a * rightCoordinate t ^ b =
      if b ≤ a then algebraMap R (ChartRing t) (t ^ b) * leftCoordinate t ^ (a - b)
      else algebraMap R (ChartRing t) (t ^ a) * rightCoordinate t ^ (b - a) := by
  split_ifs with hab
  · conv_lhs => rw [← Nat.sub_add_cancel hab, pow_add]
    rw [mul_assoc, ← mul_pow, coordinate_relation, ← map_pow, mul_comm]
  · have hba : a ≤ b := by omega
    conv_lhs => rw [← Nat.sub_add_cancel hba, pow_add]
    rw [mul_left_comm, ← mul_pow, coordinate_relation, ← map_pow, mul_comm]

/-- The two complementary lifts reconstruct every original node element exactly. -/
theorem laurent_reconstruction (z : ChartRing t) :
    z = outgoingPolynomialLift t (leftLaurentMap t z) +
      incomingPolynomialLift t (precedingLaurentMap R t z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on' with
  | monomial v r =>
    rw [leftLaurentMap_monomial, precedingLaurentMap_monomial,
      outgoingPolynomialLift, incomingPolynomialLift,
      ← single_eq_C_mul_T, ← single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
    rw [chart_monomial, mul_assoc, coordinate_mixedPower]
    by_cases hab : v 1 ≤ v 0
    · have he : (v 0 : ℤ) - v 1 = ((v 0 - v 1 : ℕ) : ℤ) := by omega
      rw [ite_eq_left hab, ite_eq_left (by omega : 0 ≤ (v 0 : ℤ) - v 1),
        ite_eq_right (by omega : ¬(v 0 : ℤ) - v 1 < 0)]
      simp only [smul_zero, add_zero]
      rw [he, Int.toNat_natCast]
      rw [← mul_assoc, ← map_mul]
      exact (Algebra.smul_def (r * t ^ v 1) _).symm
    · have he : -((v 0 : ℤ) - v 1) = ((v 1 - v 0 : ℕ) : ℤ) := by omega
      have hn : (v 0 : ℤ) - v 1 < 0 := by omega
      rw [ite_eq_right hab, ite_eq_right (not_le.mpr hn), ite_eq_left hn]
      simp only [smul_zero, zero_add]
      rw [he, Int.toNat_natCast]
      rw [← mul_assoc, ← map_mul]
      exact (Algebra.smul_def (r * t ^ v 0) _).symm
  | add p q hp hq =>
    simp only [map_add, outgoingPolynomialLift, incomingPolynomialLift,
      AddMonoidAlgebra.coeff_add] at hp hq ⊢
    conv_lhs => rw [hp, hq]
    abel

end FLT.Mazur.PolygonSmoothing
