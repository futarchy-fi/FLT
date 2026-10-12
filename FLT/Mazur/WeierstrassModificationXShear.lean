/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearData
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# Shearing the original incidence chart

The full incidence algebra is preserved by t ↦ t and v ↦ v + r.
The recovered original x is unchanged, including on the exceptional conic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => Coordinate U s b3 (b4 - r * b3) b6
local notation "t₀" => t W s b3 b4 b6
local notation "v₀" => v W s b3 b4 b6
local notation "x₀" => x W s b3 b4 b6
local notation "t₁" => t U s b3 (b4 - r * b3) b6
local notation "v₁" => v U s b3 (b4 - r * b3) b6
local notation "x₁" => x U s b3 (b4 - r * b3) b6

/-- The recovered original x is invariant under the full slope shear. -/
theorem shearForward_horizontal :
    (v₁ + algebraMap R B r) ^ 2 +
        (algebraMap R B W.a₁ + algebraMap R B b3 * t₁) * (v₁ + algebraMap R B r) -
        (algebraMap R B W.a₂ + algebraMap R B b4 * t₁ + algebraMap R B b6 * t₁ ^ 2) =
      x₁ := by
  rw [x, (rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The actual incidence equation gives the forward map without inverting x or t. -/
def shearForward : A →ₐ[R] B :=
  evaluation W s b3 b4 b6 t₁ (v₁ + algebraMap R B r) (by
    rw [shearForward_horizontal]
    exact incidence U s b3 (b4 - r * b3) b6)

/-- The recovered sheared x is the original x after inverse substitution. -/
theorem shearBackward_horizontal :
    (v₀ - algebraMap R A r) ^ 2 +
        (algebraMap R A (U).a₁ + algebraMap R A b3 * t₀) * (v₀ - algebraMap R A r) -
        (algebraMap R A (U).a₂ + algebraMap R A (b4 - r * b3) * t₀ +
          algebraMap R A b6 * t₀ ^ 2) = x₀ := by
  rw [(rootShearCurve_coefficients r).1, (rootShearCurve_coefficients r).2.1, x]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The inverse incidence map subtracts the shear from the slope. -/
def shearBackward : B →ₐ[R] A :=
  evaluation U s b3 (b4 - r * b3) b6 t₀ (v₀ - algebraMap R A r) (by
    rw [shearBackward_horizontal]
    exact incidence W s b3 b4 b6)

/-- The full incidence parameter is retained. -/
@[simp] theorem shearForward_t : shearForward W s b3 b4 b6 r t₀ = t₁ :=
  evaluation_t _ _ _ _ _ _ _ _

/-- The full original slope is retained. -/
@[simp] theorem shearForward_v :
    shearForward W s b3 b4 b6 r v₀ = v₁ + algebraMap R B r :=
  evaluation_v _ _ _ _ _ _ _ _

/-- The inverse fixes the incidence parameter. -/
@[simp] theorem shearBackward_t : shearBackward W s b3 b4 b6 r t₁ = t₀ :=
  evaluation_t _ _ _ _ _ _ _ _

/-- The inverse subtracts the tangent shear. -/
@[simp] theorem shearBackward_v :
    shearBackward W s b3 b4 b6 r v₁ = v₀ - algebraMap R A r :=
  evaluation_v _ _ _ _ _ _ _ _

/-- The shear fixes the actual cubic x function everywhere on the incidence chart. -/
@[simp] theorem shearForward_x : shearForward W s b3 b4 b6 r x₀ = x₁ := by
  conv_lhs => rw [x]
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    shearForward_t, shearForward_v]
  exact shearForward_horizontal W s b3 b4 b6 r

/-- The actual cubic y function changes by rx, even on exceptional components. -/
@[simp] theorem shearForward_y :
    shearForward W s b3 b4 b6 r (y W s b3 b4 b6) =
      y U s b3 (b4 - r * b3) b6 + algebraMap R B r * x₁ := by
  rw [y, map_mul, shearForward_x, shearForward_v, y]
  ring

/-- The entire incidence equations are isomorphic, including the exceptional conic. -/
def shearEquiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (shearForward W s b3 b4 b6 r) (shearBackward W s b3 b4 b6 r)
    (by
      apply hom_ext <;>
        simp only [AlgHom.comp_apply, AlgHom.id_apply, shearForward_t, shearForward_v,
          shearBackward_t, shearBackward_v, map_sub, AlgHom.commutes, add_sub_cancel_right])
    (by
      apply hom_ext <;>
        simp only [AlgHom.comp_apply, AlgHom.id_apply, shearForward_t, shearForward_v,
          shearBackward_t, shearBackward_v, map_add, AlgHom.commutes, sub_add_cancel])

end FLT.Mazur.WeierstrassModificationX
