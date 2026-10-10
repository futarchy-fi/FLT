/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXOverlapCompatibility
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual principal-open overlap of the modification charts

The coordinate substitutions extend to inverse maps between the localization
of the x-direction chart at t and that of the divided chart at u. This gives
an actual overlap algebra equivalence, ready for scheme gluing.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The principal open of the x-direction chart where t is invertible. -/
abbrev XOpen := Localization.Away (coord W s π b3 b4 b6 0)

/-- The corresponding principal open of the divided chart where u is invertible. -/
abbrev DividedOpen := Localization.Away (WeierstrassDilatation.x W (s * π) b3 b4 b6)

/-- The invertible incidence coordinate on its actual principal open. -/
def xOpenUnit : (XOpen W s π b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := XOpen W s π b3 b4 b6) (coord W s π b3 b4 b6 0)).unit

/-- The invertible divided coordinate on its actual principal open. -/
def dividedOpenUnit : (DividedOpen W s π b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := DividedOpen W s π b3 b4 b6)
    (WeierstrassDilatation.x W (s * π) b3 b4 b6)).unit

/-- The chosen incidence unit is the actual localized coordinate. -/
theorem xOpenUnit_val : (↑(xOpenUnit W s π b3 b4 b6) : XOpen W s π b3 b4 b6) =
    algebraMap (Coordinate W s π b3 b4 b6) _ (coord W s π b3 b4 b6 0) := IsUnit.unit_spec _

/-- The chosen divided unit is the actual localized coordinate. -/
theorem dividedOpenUnit_val :
    (↑(dividedOpenUnit W s π b3 b4 b6) : DividedOpen W s π b3 b4 b6) =
      algebraMap (WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6) _
        (WeierstrassDilatation.x W (s * π) b3 b4 b6) := IsUnit.unit_spec _

/-- The divided chart maps into the actual x-direction principal open. -/
def dividedToXOpen : WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6 →ₐ[R]
    XOpen W s π b3 b4 b6 :=
  dividedOverlapMap W s π b3 b4 b6 (IsScalarTower.toAlgHom R _ _) (xOpenUnit W s π b3 b4 b6)
    (xOpenUnit_val W s π b3 b4 b6).symm

/-- The x-direction chart maps into the actual divided principal open. -/
def xToDividedOpen : Coordinate W s π b3 b4 b6 →ₐ[R] DividedOpen W s π b3 b4 b6 :=
  xOverlapMap W s π b3 b4 b6 (IsScalarTower.toAlgHom R _ _) (dividedOpenUnit W s π b3 b4 b6)
    (dividedOpenUnit_val W s π b3 b4 b6).symm

/-- Extending the first coordinate substitution to both localized coordinates. -/
def overlapForward : DividedOpen W s π b3 b4 b6 →ₐ[R] XOpen W s π b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (WeierstrassDilatation.x W (s * π) b3 b4 b6)
    (f := dividedToXOpen W s π b3 b4 b6) (by
      change IsUnit (dividedOverlapMap _ _ _ _ _ _ _ _ _ _)
      rw [dividedOverlapMap_x]
      exact Units.isUnit _)

/-- Extending the reverse substitution to the other principal-open algebra. -/
def overlapBackward : XOpen W s π b3 b4 b6 →ₐ[R] DividedOpen W s π b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom (coord W s π b3 b4 b6 0)
    (f := xToDividedOpen W s π b3 b4 b6) (by
      change IsUnit (xOverlapMap _ _ _ _ _ _ _ _ _ _)
      rw [xOverlapMap_t]
      exact Units.isUnit _)

/-- The extended map agrees with the forward substitution on original functions. -/
@[simp] theorem overlapForward_base (z : WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6) :
    overlapForward W s π b3 b4 b6 (algebraMap _ (DividedOpen W s π b3 b4 b6) z) =
      dividedToXOpen W s π b3 b4 b6 z := by
  rw [overlapForward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The reverse extension agrees with the reverse substitution on original functions. -/
@[simp] theorem overlapBackward_base (z : Coordinate W s π b3 b4 b6) :
    overlapBackward W s π b3 b4 b6 (algebraMap _ (XOpen W s π b3 b4 b6) z) =
      xToDividedOpen W s π b3 b4 b6 z := by
  rw [overlapBackward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- A homomorphism sending one unit to an inverse sends its inverse to the original unit. -/
theorem map_inverse_unit {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Aˣ) (b : Bˣ) (h : f (↑a : A) = (↑b⁻¹ : B)) :
    f (↑a⁻¹ : A) = (↑b : B) := by
  apply (IsUnit.mul_left_inj b⁻¹.isUnit).mp
  rw [← h, ← map_mul, Units.inv_mul, map_one]
  rw [h, Units.mul_inv]

/-- The forward substitution sends the inverse divided unit to the incidence unit. -/
@[simp] theorem overlapForward_inverse :
    overlapForward W s π b3 b4 b6 (↑(dividedOpenUnit W s π b3 b4 b6)⁻¹) =
      (↑(xOpenUnit W s π b3 b4 b6) : XOpen W s π b3 b4 b6) := by
  apply map_inverse_unit
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [dividedOpenUnit_val, overlapForward_base]
  exact dividedOverlapMap_x _ _ _ _ _ _ _ _ _

/-- The reverse substitution sends the inverse incidence unit to the divided unit. -/
@[simp] theorem overlapBackward_inverse :
    overlapBackward W s π b3 b4 b6 (↑(xOpenUnit W s π b3 b4 b6)⁻¹) =
      (↑(dividedOpenUnit W s π b3 b4 b6) : DividedOpen W s π b3 b4 b6) := by
  apply map_inverse_unit
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [xOpenUnit_val, overlapBackward_base]
  exact xOverlapMap_t _ _ _ _ _ _ _ _ _

/-- The two actual principal-open coordinate algebras are isomorphic. -/
def overlapEquiv : DividedOpen W s π b3 b4 b6 ≃ₐ[R] XOpen W s π b3 b4 b6 := by
  apply AlgEquiv.ofAlgHom (overlapForward W s π b3 b4 b6) (overlapBackward W s π b3 b4 b6)
  · apply IsLocalization.algHom_ext (Submonoid.powers (coord W s π b3 b4 b6 0))
    apply hom_ext
    intro i
    fin_cases i
    · change overlapForward W s π b3 b4 b6
        (overlapBackward W s π b3 b4 b6 (algebraMap _ _ (coord W s π b3 b4 b6 0))) = _
      rw [overlapBackward_base, xToDividedOpen, xOverlapMap_t, overlapForward_inverse]
      exact xOpenUnit_val W s π b3 b4 b6
    · change overlapForward W s π b3 b4 b6
        (overlapBackward W s π b3 b4 b6 (algebraMap _ _ (coord W s π b3 b4 b6 1))) = _
      rw [overlapBackward_base, xToDividedOpen, xOverlapMap_v, map_mul,
        overlapForward_inverse]
      change (↑(xOpenUnit W s π b3 b4 b6) : XOpen W s π b3 b4 b6) *
        overlapForward W s π b3 b4 b6 (algebraMap _ _
          (WeierstrassDilatation.y W (s * π) b3 b4 b6)) = _
      rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_y,
        ← mul_assoc, Units.mul_inv, one_mul]
      rfl
    · change overlapForward W s π b3 b4 b6
        (overlapBackward W s π b3 b4 b6
          (algebraMap _ _ (coord W s π b3 b4 b6 2))) = _
      rw [overlapBackward_base, xToDividedOpen, xOverlapMap_u, map_mul,
        AlgHom.commutes, dividedOpenUnit_val, overlapForward_base,
        dividedToXOpen, dividedOverlapMap_x]
      exact incidence_inverse W s π b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
        (xOpenUnit W s π b3 b4 b6) (xOpenUnit_val W s π b3 b4 b6).symm
  · apply IsLocalization.algHom_ext
      (Submonoid.powers (WeierstrassDilatation.x W (s * π) b3 b4 b6))
    apply WeierstrassDilatation.hom_ext
    · change overlapBackward W s π b3 b4 b6
        (overlapForward W s π b3 b4 b6
          (algebraMap _ _ (WeierstrassDilatation.x W (s * π) b3 b4 b6))) = _
      rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_x, overlapBackward_inverse]
      exact dividedOpenUnit_val W s π b3 b4 b6
    · change overlapBackward W s π b3 b4 b6
        (overlapForward W s π b3 b4 b6
          (algebraMap _ _ (WeierstrassDilatation.y W (s * π) b3 b4 b6))) = _
      rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_y, map_mul,
        overlapBackward_inverse]
      change (↑(dividedOpenUnit W s π b3 b4 b6) : DividedOpen W s π b3 b4 b6) *
        overlapBackward W s π b3 b4 b6 (algebraMap _ _ (coord W s π b3 b4 b6 1)) = _
      rw [overlapBackward_base, xToDividedOpen, xOverlapMap_v,
        ← mul_assoc, Units.mul_inv, one_mul]
      rfl

end FLT.Mazur.WeierstrassSuccessiveX
