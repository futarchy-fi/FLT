/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXShear
public import FLT.Mazur.WeierstrassDilatationShear
public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# Shearing the successive principal-open overlap

Localize the incidence isomorphism at its preserved parameter, and check
the complete map from the divided chart used in the original pushout.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => XOpen W s π b3 b4 b6
local notation "B" => XOpen U s π b3 (b4 - r * b3) b6
local notation "a" => xOpenUnit W s π b3 b4 b6
local notation "b" => xOpenUnit U s π b3 (b4 - r * b3) b6

/-- The shear isomorphism extends to the actual incidence principal open. -/
def xOpenShearEquiv : A ≃ₐ[R] B :=
  IsLocalization.algEquivOfAlgEquiv A B
    (M := Submonoid.powers (coord W s π b3 b4 b6 0))
    (T := Submonoid.powers (coord U s π b3 (b4 - r * b3) b6 0))
    (shearEquiv W s π b3 b4 b6 r) (by
      rw [Submonoid.map_powers]
      congr 1
      exact shearForward_coord W s π b3 b4 b6 r 0)

/-- Every original incidence function survives the localized comparison. -/
theorem xOpenShearEquiv_base (z : Coordinate W s π b3 b4 b6) :
    xOpenShearEquiv W s π b3 b4 b6 r (algebraMap _ A z) =
      algebraMap _ B (shearForward W s π b3 b4 b6 r z) := by
  rw [xOpenShearEquiv, IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

/-- The localized shear preserves the actual reciprocal incidence coordinate. -/
theorem xOpenShearEquiv_inverse :
    xOpenShearEquiv W s π b3 b4 b6 r (↑a⁻¹ : A) = (↑b⁻¹ : B) := by
  have hval : xOpenShearEquiv W s π b3 b4 b6 r (↑a : A) = (↑b : B) := by
    rw [xOpenUnit_val, xOpenShearEquiv_base, shearForward_coord]
    exact (xOpenUnit_val U s π b3 (b4 - r * b3) b6).symm
  exact map_inverse_unit (xOpenShearEquiv W s π b3 b4 b6 r).toRingHom a b⁻¹
    (by rw [inv_inv]; exact hval)

/-- The full divided-chart attachment commutes with the localized incidence shear. -/
theorem xOpenShearEquiv_dividedToXOpen :
    (xOpenShearEquiv W s π b3 b4 b6 r).toAlgHom.comp (dividedToXOpen W s π b3 b4 b6) =
      (dividedToXOpen U s π b3 (b4 - r * b3) b6).comp
        (WeierstrassDilatation.shearForward W (s * π) b3 b4 b6 r) := by
  apply WeierstrassDilatation.hom_ext
  · change xOpenShearEquiv W s π b3 b4 b6 r
      (dividedToXOpen W s π b3 b4 b6 (WeierstrassDilatation.x W (s * π) b3 b4 b6)) = _
    rw [dividedToXOpen, dividedOverlapMap_x, xOpenShearEquiv_inverse]
    rw [AlgHom.comp_apply, WeierstrassDilatation.shearForward_x,
      dividedToXOpen, dividedOverlapMap_x]
  · change xOpenShearEquiv W s π b3 b4 b6 r
      (dividedToXOpen W s π b3 b4 b6 (WeierstrassDilatation.y W (s * π) b3 b4 b6)) = _
    rw [dividedToXOpen, dividedOverlapMap_y, map_mul, xOpenShearEquiv_inverse]
    change (↑b⁻¹ : B) * xOpenShearEquiv W s π b3 b4 b6 r
      (algebraMap _ A (coord W s π b3 b4 b6 1)) = _
    rw [xOpenShearEquiv_base, shearForward_coord]
    change (↑b⁻¹ : B) * algebraMap _ B
      (coord U s π b3 (b4 - r * b3) b6 1 + algebraMap R _ r) = _
    rw [map_add]
    rw [AlgHom.comp_apply, WeierstrassDilatation.shearForward_y, map_add, map_mul,
      AlgHom.commutes, dividedToXOpen, dividedOverlapMap_y, dividedOverlapMap_x]
    rw [← IsScalarTower.algebraMap_apply R _ B]
    simp only [IsScalarTower.toAlgHom_apply]
    ring

end FLT.Mazur.WeierstrassSuccessiveX
