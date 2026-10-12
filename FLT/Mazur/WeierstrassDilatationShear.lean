/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearData

/-!
# The shear on the entire divided chart

Construct inverse algebra maps by the original substitutions x ↦ x and
 y ↦ y + rx. No localization or nonzero scale is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => Coordinate U s b3 (b4 - r * b3) b6
local notation "x₀" => x W s b3 b4 b6
local notation "y₀" => y W s b3 b4 b6
local notation "x₁" => x U s b3 (b4 - r * b3) b6
local notation "y₁" => y U s b3 (b4 - r * b3) b6

/-- Substituting the sheared coordinates solves the original divided equation. -/
theorem shearForward_equation :
    (y₁ + algebraMap R B r * x₁) ^ 2 +
        (algebraMap R B W.a₁ * x₁ + algebraMap R B b3) *
          (y₁ + algebraMap R B r * x₁) =
      algebraMap R B s * x₁ ^ 3 + algebraMap R B W.a₂ * x₁ ^ 2 +
        algebraMap R B b4 * x₁ + algebraMap R B b6 := by
  have h := equation U s b3 (b4 - r * b3) b6
  rw [(rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1] at h
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at h
  linear_combination h

/-- The original divided chart algebra maps to the actual sheared algebra. -/
def shearForward : A →ₐ[R] B :=
  evaluation W s b3 b4 b6 x₁ (y₁ + algebraMap R B r * x₁)
    (shearForward_equation W s b3 b4 b6 r)

/-- Inverse substitution solves the actual sheared divided equation. -/
theorem shearBackward_equation :
    (y₀ - algebraMap R A r * x₀) ^ 2 +
        (algebraMap R A (U).a₁ * x₀ + algebraMap R A b3) *
          (y₀ - algebraMap R A r * x₀) =
      algebraMap R A s * x₀ ^ 3 + algebraMap R A (U).a₂ * x₀ ^ 2 +
        algebraMap R A (b4 - r * b3) * x₀ + algebraMap R A b6 := by
  rw [(rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination equation W s b3 b4 b6

/-- The inverse algebra map subtracts rx from the divided y-coordinate. -/
def shearBackward : B →ₐ[R] A :=
  evaluation U s b3 (b4 - r * b3) b6 x₀ (y₀ - algebraMap R A r * x₀)
    (shearBackward_equation W s b3 b4 b6 r)

/-- The forward map fixes the divided x-coordinate. -/
@[simp] theorem shearForward_x : shearForward W s b3 b4 b6 r x₀ = x₁ :=
  evaluation_x _ _ _ _ _ _ _ _

/-- The forward map retains the actual original divided y-coordinate. -/
@[simp] theorem shearForward_y :
    shearForward W s b3 b4 b6 r y₀ = y₁ + algebraMap R B r * x₁ :=
  evaluation_y _ _ _ _ _ _ _ _

/-- The inverse map fixes the divided x-coordinate. -/
@[simp] theorem shearBackward_x : shearBackward W s b3 b4 b6 r x₁ = x₀ :=
  evaluation_x _ _ _ _ _ _ _ _

/-- The inverse map subtracts the actual shear parameter. -/
@[simp] theorem shearBackward_y :
    shearBackward W s b3 b4 b6 r y₁ = y₀ - algebraMap R A r * x₀ :=
  evaluation_y _ _ _ _ _ _ _ _

/-- The entire divided equations are isomorphic by the explicit shear. -/
def shearEquiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (shearForward W s b3 b4 b6 r) (shearBackward W s b3 b4 b6 r)
    (by
      apply hom_ext <;>
        simp only [AlgHom.comp_apply, AlgHom.id_apply, shearForward_x, shearForward_y,
          shearBackward_x, shearBackward_y, map_sub, map_mul, AlgHom.commutes,
          add_sub_cancel_right])
    (by
      apply hom_ext <;>
        simp only [AlgHom.comp_apply, AlgHom.id_apply, shearForward_x, shearForward_y,
          shearBackward_x, shearBackward_y, map_add, map_mul, AlgHom.commutes, sub_add_cancel])

end FLT.Mazur.WeierstrassDilatation
