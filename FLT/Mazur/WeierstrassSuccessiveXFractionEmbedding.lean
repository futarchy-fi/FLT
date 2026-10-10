/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXFlat
public import FLT.Mazur.WeierstrassSuccessiveXHorizontalLocalization

/-!
# The successive chart embeds in preceding horizontal fractions

The actual contraction identifies the chart with a subalgebra of the preceding
horizontal localization. The three generators become π/x, y/x and x.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveX

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "L" => PreviousHorizontalOpen W s π b3 b4 b6

/-- The actual chart maps to the preceding horizontal fraction algebra. -/
def toPreviousHorizontalOpen : Coordinate W s π b3 b4 b6 →ₐ[R] L :=
  (horizontalEquiv W s π b3 b4 b6).symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ _)

/-- The fraction embedding equals the previously constructed inverse substitution. -/
theorem toPreviousHorizontalOpen_eq :
    toPreviousHorizontalOpen W s π b3 b4 b6 =
      horizontalMap W s π b3 b4 b6 (IsScalarTower.toAlgHom R B L)
        (previousHorizontalUnit W s π b3 b4 b6)
        (previousHorizontalUnit_val W s π b3 b4 b6).symm := by
  apply AlgHom.ext
  intro z
  exact horizontalBackward_base W s π b3 b4 b6 z

/-- The chosen inverse unit is the actual localization inverse. -/
theorem previousHorizontalUnit_inverse :
    (↑(previousHorizontalUnit W s π b3 b4 b6)⁻¹ : L) =
      IsLocalization.Away.invSelf BX := by
  apply (previousHorizontalUnit W s π b3 b4 b6).isUnit.mul_left_inj.mp
  rw [Units.inv_mul, previousHorizontalUnit_val,
    mul_comm (IsLocalization.Away.invSelf BX), IsLocalization.Away.mul_invSelf]

/-- The incidence ratio is exactly π/x in the preceding horizontal localization. -/
@[simp] theorem toPreviousHorizontalOpen_t :
    toPreviousHorizontalOpen W s π b3 b4 b6 (coord W s π b3 b4 b6 0) =
      algebraMap R L π * IsLocalization.Away.invSelf BX := by
  rw [toPreviousHorizontalOpen_eq, horizontalMap_t, previousHorizontalUnit_inverse]

/-- The slope is exactly y/x in the preceding horizontal localization. -/
@[simp] theorem toPreviousHorizontalOpen_v :
    toPreviousHorizontalOpen W s π b3 b4 b6 (coord W s π b3 b4 b6 1) =
      IsLocalization.Away.invSelf BX * algebraMap B L BY := by
  rw [toPreviousHorizontalOpen_eq, horizontalMap_v, previousHorizontalUnit_inverse]
  rfl

/-- The retained horizontal coordinate is exactly the preceding x. -/
@[simp] theorem toPreviousHorizontalOpen_u :
    toPreviousHorizontalOpen W s π b3 b4 b6 (coord W s π b3 b4 b6 2) =
      algebraMap B L BX := by
  rw [toPreviousHorizontalOpen_eq, horizontalMap_u, previousHorizontalUnit_val]

/-- Every preceding function is carried by its original contraction. -/
theorem toPreviousHorizontalOpen_fromDivided :
    (toPreviousHorizontalOpen W s π b3 b4 b6).comp (fromDivided W s π b3 b4 b6) =
      IsScalarTower.toAlgHom R B L := by
  rw [toPreviousHorizontalOpen_eq]
  exact horizontalMap_fromDivided W s π b3 b4 b6 _ _ _

/-- No chart functions disappear in the preceding fraction algebra. -/
theorem toPreviousHorizontalOpen_injective [IsDomain R] (hπ : π ≠ 0) :
    Function.Injective (toPreviousHorizontalOpen W s π b3 b4 b6) :=
  (horizontalEquiv W s π b3 b4 b6).symm.injective.comp
    (horizontal_algebraMap_injective W s π b3 b4 b6 hπ)

end FLT.Mazur.WeierstrassSuccessiveX
