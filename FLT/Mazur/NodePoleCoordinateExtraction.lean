/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Tactic.LinearCombination

/-!
# Recover an original node coordinate from its two pole equations

The incoming correction cancels using the original node relation. No
smoothing parameter, residue characteristic, or coordinate is inverted.
-/

public section
namespace FLT.Mazur.NodePoleCoordinateExtraction
variable {R : Type*} [CommRing R]

/-- Eliminate the quadratic lower term while retaining the exact incoming correction. -/
theorem extract (x y e a b c u v : R) (he : e * x * y = 0)
    (h₂ : (x - 1) ^ 2 * u = a * (x + e * y))
    (h₃ : (x - 1) ^ 3 * v = c * x * (x - 1) + b * x - c * e * y) :
    (x - 1) ^ 3 * (a * v - c * u) = a * b * x := by
  linear_combination a * h₃ - c * (x - 1) * h₂ - a * c * he

/-- The same cancellation holds for the full original numerators before localization. -/
theorem extract_numerators (x y e a b c A B u v : R) (he : e * x * y = 0)
    (h₂ : u = A * (x - 1) ^ 2 + a * x + a * e * y)
    (h₃ : v = B * (x - 1) ^ 3 + c * x * (x - 1) + b * x - c * e * y) :
    a * (v - B * (x - 1) ^ 3) - c * (x - 1) * (u - A * (x - 1) ^ 2) =
      a * b * x := by
  linear_combination a * h₃ - c * (x - 1) * h₂ - a * c * he

/-- A square-zero smoothing term contributes no mixed-coordinate correction. -/
theorem correction_mixed (x y t : R) (hxy : x * y = t) (ht : t ^ 2 = 0)
    (e : Prop) [Decidable e] : (if e then t else 0) * x * y = 0 := by
  split_ifs
  · rw [mul_assoc, hxy, ← pow_two, ht]
  · rw [zero_mul, zero_mul]

end FLT.Mazur.NodePoleCoordinateExtraction
