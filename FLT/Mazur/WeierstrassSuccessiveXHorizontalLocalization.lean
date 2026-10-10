/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXHorizontalMaps
public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# Actual localization comparison over the preceding horizontal open

The successive x-direction contraction is an isomorphism after inverting
the preceding horizontal coordinate. This identifies actual open algebras,
without assuming a regular scale or a reduced coefficient ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "U" => coord W s π b3 b4 b6 2

/-- The retained-horizontal principal open in the successive x-chart. -/
abbrev HorizontalOpen := Localization.Away U

/-- The same horizontal principal open in the preceding divided chart. -/
abbrev PreviousHorizontalOpen := Localization.Away BX

/-- The actual retained horizontal unit. -/
def horizontalUnit : (HorizontalOpen W s π b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := HorizontalOpen W s π b3 b4 b6) U).unit

/-- The actual preceding horizontal unit. -/
def previousHorizontalUnit : (PreviousHorizontalOpen W s π b3 b4 b6)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := PreviousHorizontalOpen W s π b3 b4 b6) BX).unit

/-- The retained unit is the original localized function. -/
theorem horizontalUnit_val :
    (↑(horizontalUnit W s π b3 b4 b6) : HorizontalOpen W s π b3 b4 b6) =
      algebraMap A _ U := IsUnit.unit_spec _

/-- The preceding unit is its original localized function. -/
theorem previousHorizontalUnit_val :
    (↑(previousHorizontalUnit W s π b3 b4 b6) : PreviousHorizontalOpen W s π b3 b4 b6) =
      algebraMap B _ BX := IsUnit.unit_spec _

/-- The contraction extends to the two actual horizontal principal opens. -/
def horizontalForward : PreviousHorizontalOpen W s π b3 b4 b6 →ₐ[R]
    HorizontalOpen W s π b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom BX
    (f := (IsScalarTower.toAlgHom R A _).comp (fromDivided W s π b3 b4 b6)) (by
      change IsUnit (algebraMap A _ (fromDivided W s π b3 b4 b6 BX))
      rw [fromDivided_x]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- The inverse coordinate substitutions extend to the horizontal principal opens. -/
def horizontalBackward : HorizontalOpen W s π b3 b4 b6 →ₐ[R]
    PreviousHorizontalOpen W s π b3 b4 b6 :=
  IsLocalization.Away.liftAlgHom U
    (f := horizontalMap W s π b3 b4 b6 (IsScalarTower.toAlgHom R B _)
      (previousHorizontalUnit W s π b3 b4 b6)
      (previousHorizontalUnit_val W s π b3 b4 b6).symm) (by
        rw [horizontalMap_u]
        exact Units.isUnit _)

/-- The localized contraction agrees with the original contraction on every function. -/
@[simp] theorem horizontalForward_base (z : B) :
    horizontalForward W s π b3 b4 b6
        (algebraMap B (PreviousHorizontalOpen W s π b3 b4 b6) z) =
      algebraMap A _ (fromDivided W s π b3 b4 b6 z) := by
  rw [horizontalForward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The localized reverse map agrees with the explicit fraction substitution. -/
@[simp] theorem horizontalBackward_base (z : A) :
    horizontalBackward W s π b3 b4 b6
        (algebraMap A (HorizontalOpen W s π b3 b4 b6) z) =
      horizontalMap W s π b3 b4 b6 (IsScalarTower.toAlgHom R B _)
        (previousHorizontalUnit W s π b3 b4 b6)
        (previousHorizontalUnit_val W s π b3 b4 b6).symm z := by
  rw [horizontalBackward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The localized contraction preserves the inverse of the horizontal coordinate. -/
@[simp] theorem horizontalForward_inverse :
    horizontalForward W s π b3 b4 b6 (↑(previousHorizontalUnit W s π b3 b4 b6)⁻¹) =
      (↑(horizontalUnit W s π b3 b4 b6)⁻¹ : HorizontalOpen W s π b3 b4 b6) := by
  apply map_inverse_unit _ _ (horizontalUnit W s π b3 b4 b6)⁻¹
  simp only [inv_inv, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [previousHorizontalUnit_val, horizontalForward_base, fromDivided_x, horizontalUnit_val]

/-- The actual successive and preceding horizontal opens are isomorphic. -/
def horizontalEquiv : PreviousHorizontalOpen W s π b3 b4 b6 ≃ₐ[R]
    HorizontalOpen W s π b3 b4 b6 := by
  apply AlgEquiv.ofAlgHom (horizontalForward W s π b3 b4 b6)
    (horizontalBackward W s π b3 b4 b6)
  · apply IsLocalization.algHom_ext (Submonoid.powers U)
    apply hom_ext
    intro i
    fin_cases i
    · change horizontalForward W s π b3 b4 b6
        (horizontalBackward W s π b3 b4 b6
          (algebraMap A _ (coord W s π b3 b4 b6 0))) = _
      rw [horizontalBackward_base, horizontalMap_t, map_mul, AlgHom.commutes,
        horizontalForward_inverse]
      have h := congrArg (algebraMap A (HorizontalOpen W s π b3 b4 b6))
        (incidence W s π b3 b4 b6)
      rw [map_mul, ← IsScalarTower.algebraMap_apply R A, ← horizontalUnit_val] at h
      rw [← h, mul_assoc, Units.mul_inv, mul_one]
      rfl
    · change horizontalForward W s π b3 b4 b6
        (horizontalBackward W s π b3 b4 b6
          (algebraMap A _ (coord W s π b3 b4 b6 1))) = _
      rw [horizontalBackward_base, horizontalMap_v, map_mul, horizontalForward_inverse]
      change _ * horizontalForward W s π b3 b4 b6 (algebraMap B _ _) = _
      rw [horizontalForward_base, fromDivided_y, map_mul, ← horizontalUnit_val,
        ← mul_assoc, Units.inv_mul, one_mul]
      rfl
    · change horizontalForward W s π b3 b4 b6
        (horizontalBackward W s π b3 b4 b6 (algebraMap A _ U)) = _
      rw [horizontalBackward_base, horizontalMap_u, previousHorizontalUnit_val,
        horizontalForward_base, fromDivided_x]
      rfl
  · apply IsLocalization.algHom_ext (Submonoid.powers BX)
    apply AlgHom.ext
    intro z
    change horizontalBackward W s π b3 b4 b6
      (horizontalForward W s π b3 b4 b6 (algebraMap B _ z)) = _
    rw [horizontalForward_base, horizontalBackward_base]
    exact AlgHom.congr_fun (horizontalMap_fromDivided W s π b3 b4 b6
      (IsScalarTower.toAlgHom R B _) (previousHorizontalUnit W s π b3 b4 b6)
      (previousHorizontalUnit_val W s π b3 b4 b6).symm) z

end FLT.Mazur.WeierstrassSuccessiveX
