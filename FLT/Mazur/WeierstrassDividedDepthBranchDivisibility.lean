/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# Derive strict-branch divisibilities from actual doubled-depth data

Two factorizations of the same original coefficients force the quotients
needed by the deeper branch construction. A normalized second coefficient
supplies the remaining slope divisibility at every depth.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + k))

include hπ in
/-- The next third quotient is forced by the original third coefficient. -/
theorem branch_depth_factor3 : d.b3 = π ^ k * e.b3 := by
  simpa using depth_coefficient_factor π k (k + k) hπ (Nat.le_add_right k k)
    d.factor3 e.factor3

include hπ in
/-- The next fourth quotient is forced by the original fourth coefficient. -/
theorem branch_depth_factor4 : d.b4 = π ^ k * e.b4 := by
  simpa using depth_coefficient_factor π k (k + k) hπ (Nat.le_add_right k k)
    d.factor4 e.factor4

include hπ in
/-- The next constant quotient has the square of the intervening scale. -/
theorem branch_depth_factor6 : d.b6 = (π ^ k) ^ 2 * e.b6 := by
  simpa using depth_constant_factor π k (k + k) hπ (Nat.le_add_right k k)
    d.factor6 e.factor6

include hπ in
/-- The first branch constant quotient is constructed from the deeper actual coefficient. -/
theorem branch_depth_first_factor6 : d.b6 = π ^ k * (π ^ k * e.b6) := by
  rw [branch_depth_factor6 hπ d e, pow_two, mul_assoc]

omit [IsDomain R] in
/-- A zero normalized second coefficient supplies the branch slope factor at every depth. -/
theorem branch_normalized_factor2 (h2 : W.a₂ = 0) : W.a₂ = π ^ k * 0 := by
  rw [h2, mul_zero]

end FLT.Mazur.WeierstrassDividedDepth
