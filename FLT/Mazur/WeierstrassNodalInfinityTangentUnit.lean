/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import Mathlib.Tactic.LinearCombination

/-!
# Tangent factors are units on the full nodal infinity chart

The original infinity equation forces both tangent factors to be units.
An explicit inverse permits root shear on the whole chart, without deleting points.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "A" => Coordinate W 1
local notation "x" => coord W 1 0
local notation "z" => coord W 1 2

include h₃ h₄ h₆ in
/-- The original infinity equation, before any root shear. -/
theorem nodalInfinity_relation :
    z * (1 + algebraMap R A W.a₁ * x - algebraMap R A W.a₂ * x ^ 2) = x ^ 3 := by
  have h := coord_equation W 1
  rw [WeierstrassCurve.Projective.equation_iff] at h
  change coord W 1 1 ^ 2 * z + algebraMap R A W.a₁ * x * coord W 1 1 * z +
    algebraMap R A W.a₃ * coord W 1 1 * z ^ 2 -
    (x ^ 3 + algebraMap R A W.a₂ * x ^ 2 * z +
      algebraMap R A W.a₄ * x * z ^ 2 + algebraMap R A W.a₆ * z ^ 3) = 0 at h
  rw [h₃, h₄, h₆, map_zero, coord_self] at h
  linear_combination h

variable (r : R) (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
local notation "q" => algebraMap R A r

include h₃ h₄ h₆ hr in
/-- The root relation factors the original infinity equation into its two tangent factors. -/
theorem nodalInfinity_tangent_relation :
    z * ((1 - q * x) * (1 + algebraMap R A (W.a₁ + r) * x)) = x ^ 3 := by
  have h := congrArg (algebraMap R A) hr
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  rw [map_add]
  linear_combination nodalInfinity_relation W h₃ h₄ h₆ - z * x ^ 2 * h

/-- A polynomial inverse for the original first tangent factor. -/
def nodalInfinityTangentInverse : A :=
  1 + q * x + (q * x) ^ 2 + q ^ 3 * z * (1 + algebraMap R A (W.a₁ + r) * x)

include h₃ h₄ h₆ hr in
/-- The inverse identity holds on the full original infinity chart. -/
theorem nodalInfinity_tangent_mul_inverse :
    (1 - q * x) * nodalInfinityTangentInverse W r = 1 := by
  unfold nodalInfinityTangentInverse
  linear_combination q ^ 3 * nodalInfinity_tangent_relation W h₃ h₄ h₆ r hr

/-- The actual original tangent factor as a unit, with no localization. -/
def nodalInfinityTangentUnit : Aˣ where
  val := 1 - q * x
  inv := nodalInfinityTangentInverse W r
  val_inv := nodalInfinity_tangent_mul_inverse W h₃ h₄ h₆ r hr
  inv_val := by
    rw [mul_comm]
    exact nodalInfinity_tangent_mul_inverse W h₃ h₄ h₆ r hr

/-- Root shear can divide by its new Y coordinate everywhere on the original chart. -/
@[simp] theorem nodalInfinityTangentUnit_val :
    (nodalInfinityTangentUnit W h₃ h₄ h₆ r hr : A) = 1 - q * x := rfl

end FLT.Mazur.WeierstrassIntegralChart
