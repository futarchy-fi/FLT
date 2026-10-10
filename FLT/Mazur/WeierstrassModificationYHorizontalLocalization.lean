/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYInverse
public import FLT.Mazur.WeierstrassModificationXLocalization

/-!
# The actual horizontal-ratio overlap of the y-direction chart

The localization at u=x/y is isomorphic to the localization of the
x-direction chart at its slope coordinate. Both maps are constructed from the proved
coordinate substitutions, and the inverse identities are checked on generators.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The horizontal-ratio principal open of the y-chart. -/
abbrev HorizontalOpen := Localization.Away (coord W s b3 b4 b6 1)

/-- The slope principal open of the x-direction chart. -/
abbrev XVertical := Localization.Away (WeierstrassModificationX.v W s b3 b4 b6)

/-- The horizontal ratio as a unit in its actual localization. -/
def horizontalUnit : (HorizontalOpen W s b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := HorizontalOpen W s b3 b4 b6)
    (coord W s b3 b4 b6 1)).unit

/-- The vertical coordinate as a unit in its actual localization. -/
def xVerticalUnit : (XVertical W s b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := XVertical W s b3 b4 b6)
    (WeierstrassModificationX.v W s b3 b4 b6)).unit

/-- The chosen horizontal unit is the actual image of the horizontal ratio. -/
theorem horizontalUnit_val : (↑(horizontalUnit W s b3 b4 b6) : HorizontalOpen W s b3 b4 b6) =
    algebraMap _ _ (coord W s b3 b4 b6 1) := IsUnit.unit_spec _

/-- The chosen vertical unit is the actual localized slope coordinate. -/
theorem xVerticalUnit_val :
    (↑(xVerticalUnit W s b3 b4 b6) : XVertical W s b3 b4 b6) =
      algebraMap _ _ (WeierstrassModificationX.v W s b3 b4 b6) := IsUnit.unit_spec _

/-- Extension of the x-direction substitution to the actual principal opens. -/
def horizontalForward : XVertical W s b3 b4 b6 →ₐ[R] HorizontalOpen W s b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (WeierstrassModificationX.v W s b3 b4 b6)
    (f := toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (horizontalUnit W s b3 b4 b6) (horizontalUnit_val W s b3 b4 b6).symm) (by
        rw [toX_v]
        exact Units.isUnit _)

/-- Extension of the y-coordinate substitution in the reverse direction. -/
def horizontalBackward : HorizontalOpen W s b3 b4 b6 →ₐ[R] XVertical W s b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (coord W s b3 b4 b6 1)
    (f := fromX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (xVerticalUnit W s b3 b4 b6) (xVerticalUnit_val W s b3 b4 b6).symm) (by
        rw [fromX_coord]
        exact Units.isUnit _)

/-- The forward map restricts to the prescribed x-direction evaluation. -/
@[simp] theorem horizontalForward_base (z : WeierstrassModificationX.Coordinate W s b3 b4 b6) :
    horizontalForward W s b3 b4 b6 (algebraMap _ _ z) =
      toX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (horizontalUnit W s b3 b4 b6) (horizontalUnit_val W s b3 b4 b6).symm z := by
  rw [horizontalForward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The reverse map restricts to the prescribed y-coordinate evaluation. -/
@[simp] theorem horizontalBackward_base (z : Coordinate W s b3 b4 b6) :
    horizontalBackward W s b3 b4 b6 (algebraMap _ _ z) =
      fromX W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (xVerticalUnit W s b3 b4 b6) (xVerticalUnit_val W s b3 b4 b6).symm z := by
  rw [horizontalBackward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The forward map sends the inverse vertical unit to the horizontal unit. -/
@[simp] theorem horizontalForward_inverse :
    horizontalForward W s b3 b4 b6 (↑(xVerticalUnit W s b3 b4 b6)⁻¹) =
      (↑(horizontalUnit W s b3 b4 b6) : HorizontalOpen W s b3 b4 b6) := by
  apply WeierstrassModificationX.map_inverse_unit
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [xVerticalUnit_val, horizontalForward_base, toX_v]

/-- The reverse map sends the inverse horizontal unit to the vertical unit. -/
@[simp] theorem horizontalBackward_inverse :
    horizontalBackward W s b3 b4 b6 (↑(horizontalUnit W s b3 b4 b6)⁻¹) =
      (↑(xVerticalUnit W s b3 b4 b6) : XVertical W s b3 b4 b6) := by
  apply WeierstrassModificationX.map_inverse_unit
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [horizontalUnit_val, horizontalBackward_base, fromX_coord]
  rfl

/-- The actual two localization algebras are isomorphic. -/
def horizontalEquiv : XVertical W s b3 b4 b6 ≃ₐ[R] HorizontalOpen W s b3 b4 b6 := by
  apply AlgEquiv.ofAlgHom (horizontalForward W s b3 b4 b6) (horizontalBackward W s b3 b4 b6)
  · apply IsLocalization.algHom_ext (Submonoid.powers (coord W s b3 b4 b6 1))
    apply hom_ext
    intro i
    change horizontalForward W s b3 b4 b6
      (horizontalBackward W s b3 b4 b6 (algebraMap _ _ (coord W s b3 b4 b6 i))) =
        algebraMap _ _ (coord W s b3 b4 b6 i)
    rw [horizontalBackward_base, fromX_coord]
    fin_cases i
    · change horizontalForward W s b3 b4 b6 (algebraMap _ _
        (WeierstrassModificationX.t W s b3 b4 b6) * ↑(xVerticalUnit W s b3 b4 b6)⁻¹) = _
      rw [map_mul, horizontalForward_base, toX_t, horizontalForward_inverse,
        mul_assoc, Units.inv_mul, mul_one]
      rfl
    · exact (horizontalForward_inverse W s b3 b4 b6).trans
        (horizontalUnit_val W s b3 b4 b6)
    · change horizontalForward W s b3 b4 b6
        (algebraMap _ _ (WeierstrassModificationX.x W s b3 b4 b6) *
          ↑(xVerticalUnit W s b3 b4 b6)) = _
      rw [map_mul, horizontalForward_base, toX_x, xVerticalUnit_val,
        horizontalForward_base, toX_v, mul_assoc, Units.mul_inv, mul_one]
      rfl
  · apply IsLocalization.algHom_ext
      (Submonoid.powers (WeierstrassModificationX.v W s b3 b4 b6))
    apply WeierstrassModificationX.hom_ext
    · change horizontalBackward W s b3 b4 b6
        (horizontalForward W s b3 b4 b6 (algebraMap _ _
          (WeierstrassModificationX.t W s b3 b4 b6))) = _
      rw [horizontalForward_base, toX_t]
      change horizontalBackward W s b3 b4 b6
        (algebraMap _ _ (coord W s b3 b4 b6 0) * ↑(horizontalUnit W s b3 b4 b6)⁻¹) = _
      rw [map_mul, horizontalBackward_base, fromX_coord, horizontalBackward_inverse]
      change (algebraMap _ (XVertical W s b3 b4 b6)
        (WeierstrassModificationX.t W s b3 b4 b6) *
        ↑(xVerticalUnit W s b3 b4 b6)⁻¹) * ↑(xVerticalUnit W s b3 b4 b6) = _
      rw [mul_assoc, Units.inv_mul, mul_one]
      rfl
    · change horizontalBackward W s b3 b4 b6
        (horizontalForward W s b3 b4 b6 (algebraMap _ _
          (WeierstrassModificationX.v W s b3 b4 b6))) = _
      rw [horizontalForward_base, toX_v, horizontalBackward_inverse]
      exact xVerticalUnit_val W s b3 b4 b6

end FLT.Mazur.WeierstrassModificationY
