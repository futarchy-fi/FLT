/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonTransition
public import Mathlib.Tactic.LinearCombination

/-!
# Clearing cubic Möbius equations

Multiplication by the cube of the coordinate difference turns the punctured
cubic equations into polynomial equations valid at both endpoints.
-/

@[expose] public section
namespace FLT.Mazur.CubicMobiusClearing
variable {R : Type*} [CommRing R]

/-- Homogenize all three cubic ratios using the same factor. -/
lemma equations (c₀ c₁ c₂ z a w t b : R) (ht : z * b = t)
    (h₀ : c₀ * (z - a) ^ 3 = 1 + w * z ^ 3)
    (h₁ : c₁ * (z - a) ^ 3 = z)
    (h₂ : c₂ * (z - a) ^ 3 = z ^ 2) :
    c₀ * (t - a * b) ^ 3 = b ^ 3 + w * t ^ 3 ∧
    c₁ * (t - a * b) ^ 3 = t * b ^ 2 ∧
    c₂ * (t - a * b) ^ 3 = t ^ 2 * b := by
  rw [← ht]
  constructor
  · linear_combination b ^ 3 * h₀
  constructor
  · linear_combination b ^ 3 * h₁
  · linear_combination b ^ 3 * h₂

end CubicMobiusClearing
namespace OneGonTransition
variable (R : Type*) [CommRing R]

/-- The Möbius coordinate times the original difference is the original coordinate. -/
lemma mobius_mul_difference :
    (mobius R : puncture R) * (difference R : puncture R) =
      (coordinate R : puncture R) := by
  change ((coordinate R : puncture R) * ↑(difference R)⁻¹) * ↑(difference R) = _
  rw [mul_assoc, Units.inv_mul, mul_one]

end FLT.Mazur.OneGonTransition
