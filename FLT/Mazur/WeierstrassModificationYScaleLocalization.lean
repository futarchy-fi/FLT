/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYInverse
public import FLT.Mazur.WeierstrassModificationXLocalization

/-!
# The actual scale-ratio overlap of the y-direction chart

The localization at r=s/y is isomorphic to the localization of the divided
chart at its vertical coordinate. Both maps are constructed from the proved
coordinate substitutions, and the inverse identities are checked on generators.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The scale-ratio principal open of the y-chart. -/
abbrev ScaleOpen := Localization.Away (coord W s b3 b4 b6 0)

/-- The vertical principal open of the divided chart. -/
abbrev DividedVertical := Localization.Away (WeierstrassDilatation.y W s b3 b4 b6)

/-- The scale ratio as a unit in its actual localization. -/
def scaleUnit : (ScaleOpen W s b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := ScaleOpen W s b3 b4 b6)
    (coord W s b3 b4 b6 0)).unit

/-- The vertical coordinate as a unit in its actual localization. -/
def dividedVerticalUnit : (DividedVertical W s b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := DividedVertical W s b3 b4 b6)
    (WeierstrassDilatation.y W s b3 b4 b6)).unit

/-- The chosen scale unit is the actual image of the scale ratio. -/
theorem scaleUnit_val : (↑(scaleUnit W s b3 b4 b6) : ScaleOpen W s b3 b4 b6) =
    algebraMap _ _ (coord W s b3 b4 b6 0) := IsUnit.unit_spec _

/-- The chosen vertical unit is the actual localized divided coordinate. -/
theorem dividedVerticalUnit_val :
    (↑(dividedVerticalUnit W s b3 b4 b6) : DividedVertical W s b3 b4 b6) =
      algebraMap _ _ (WeierstrassDilatation.y W s b3 b4 b6) := IsUnit.unit_spec _

/-- Extension of the divided-coordinate substitution to the actual principal opens. -/
def scaleForward : DividedVertical W s b3 b4 b6 →ₐ[R] ScaleOpen W s b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (WeierstrassDilatation.y W s b3 b4 b6)
    (f := toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (scaleUnit W s b3 b4 b6) (scaleUnit_val W s b3 b4 b6).symm) (by
        rw [toDivided_y]
        exact Units.isUnit _)

/-- Extension of the y-coordinate substitution in the reverse direction. -/
def scaleBackward : ScaleOpen W s b3 b4 b6 →ₐ[R] DividedVertical W s b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (coord W s b3 b4 b6 0)
    (f := fromDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
      (dividedVerticalUnit W s b3 b4 b6) (dividedVerticalUnit_val W s b3 b4 b6).symm) (by
        rw [fromDivided_coord]
        exact Units.isUnit _)

/-- The forward map restricts to the prescribed divided-coordinate evaluation. -/
@[simp] theorem scaleForward_base (z : WeierstrassDilatation.Coordinate W s b3 b4 b6) :
    scaleForward W s b3 b4 b6 (algebraMap _ _ z) =
      toDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (scaleUnit W s b3 b4 b6) (scaleUnit_val W s b3 b4 b6).symm z := by
  rw [scaleForward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The reverse map restricts to the prescribed y-coordinate evaluation. -/
@[simp] theorem scaleBackward_base (z : Coordinate W s b3 b4 b6) :
    scaleBackward W s b3 b4 b6 (algebraMap _ _ z) =
      fromDivided W s b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (dividedVerticalUnit W s b3 b4 b6) (dividedVerticalUnit_val W s b3 b4 b6).symm z := by
  rw [scaleBackward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The forward map sends the inverse vertical unit to the scale unit. -/
@[simp] theorem scaleForward_inverse :
    scaleForward W s b3 b4 b6 (↑(dividedVerticalUnit W s b3 b4 b6)⁻¹) =
      (↑(scaleUnit W s b3 b4 b6) : ScaleOpen W s b3 b4 b6) := by
  apply WeierstrassModificationX.map_inverse_unit
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [dividedVerticalUnit_val, scaleForward_base, toDivided_y]

/-- The reverse map sends the inverse scale unit to the vertical unit. -/
@[simp] theorem scaleBackward_inverse :
    scaleBackward W s b3 b4 b6 (↑(scaleUnit W s b3 b4 b6)⁻¹) =
      (↑(dividedVerticalUnit W s b3 b4 b6) : DividedVertical W s b3 b4 b6) := by
  apply WeierstrassModificationX.map_inverse_unit
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [scaleUnit_val, scaleBackward_base, fromDivided_coord]
  rfl

/-- The actual two localization algebras are isomorphic. -/
def scaleEquiv : DividedVertical W s b3 b4 b6 ≃ₐ[R] ScaleOpen W s b3 b4 b6 := by
  apply AlgEquiv.ofAlgHom (scaleForward W s b3 b4 b6) (scaleBackward W s b3 b4 b6)
  · apply IsLocalization.algHom_ext (Submonoid.powers (coord W s b3 b4 b6 0))
    apply hom_ext
    intro i
    change scaleForward W s b3 b4 b6
      (scaleBackward W s b3 b4 b6 (algebraMap _ _ (coord W s b3 b4 b6 i))) =
        algebraMap _ _ (coord W s b3 b4 b6 i)
    rw [scaleBackward_base, fromDivided_coord]
    fin_cases i
    · exact (scaleForward_inverse W s b3 b4 b6).trans (scaleUnit_val W s b3 b4 b6)
    · change scaleForward W s b3 b4 b6 (algebraMap _ _
        (WeierstrassDilatation.x W s b3 b4 b6) * ↑(dividedVerticalUnit W s b3 b4 b6)⁻¹) = _
      rw [map_mul, scaleForward_base, toDivided_x, scaleForward_inverse,
        mul_assoc, Units.inv_mul, mul_one]
      rfl
    · change scaleForward W s b3 b4 b6
        (algebraMap R _ s * ↑(dividedVerticalUnit W s b3 b4 b6)) = _
      rw [map_mul, AlgHom.commutes, dividedVerticalUnit_val, scaleForward_base, toDivided_y]
      have h := congrArg (algebraMap (Coordinate W s b3 b4 b6) (ScaleOpen W s b3 b4 b6))
        (incidence W s b3 b4 b6)
      simp only [map_mul, ← scaleUnit_val, ← IsScalarTower.algebraMap_apply] at h
      rw [← h, mul_right_comm, Units.mul_inv, one_mul]
      rfl
  · apply IsLocalization.algHom_ext
      (Submonoid.powers (WeierstrassDilatation.y W s b3 b4 b6))
    apply WeierstrassDilatation.hom_ext
    · change scaleBackward W s b3 b4 b6
        (scaleForward W s b3 b4 b6 (algebraMap _ _
          (WeierstrassDilatation.x W s b3 b4 b6))) = _
      rw [scaleForward_base, toDivided_x]
      change scaleBackward W s b3 b4 b6
        (algebraMap _ _ (coord W s b3 b4 b6 1) * ↑(scaleUnit W s b3 b4 b6)⁻¹) = _
      rw [map_mul, scaleBackward_base, fromDivided_coord, scaleBackward_inverse]
      change (algebraMap _ (DividedVertical W s b3 b4 b6)
        (WeierstrassDilatation.x W s b3 b4 b6) *
        ↑(dividedVerticalUnit W s b3 b4 b6)⁻¹) * ↑(dividedVerticalUnit W s b3 b4 b6) = _
      rw [mul_assoc, Units.inv_mul, mul_one]
      rfl
    · change scaleBackward W s b3 b4 b6
        (scaleForward W s b3 b4 b6 (algebraMap _ _
          (WeierstrassDilatation.y W s b3 b4 b6))) = _
      rw [scaleForward_base, toDivided_y, scaleBackward_inverse]
      exact dividedVerticalUnit_val W s b3 b4 b6

end FLT.Mazur.WeierstrassModificationY
