/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationShearOverlap
public import FLT.Mazur.WeierstrassModificationXLocalization

/-!
# Shearing the full principal-open overlap

Localize the incidence isomorphism at its preserved parameter, and check
the complete map from the divided chart used in the original pushout.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => XOpen W s b3 b4 b6
local notation "B" => XOpen U s b3 (b4 - r * b3) b6
local notation "a" => xOpenUnit W s b3 b4 b6
local notation "b" => xOpenUnit U s b3 (b4 - r * b3) b6

/-- The shear isomorphism extends to the actual incidence principal open. -/
def xOpenShearEquiv : A ≃ₐ[R] B :=
  IsLocalization.algEquivOfAlgEquiv A B
    (M := Submonoid.powers (t W s b3 b4 b6))
    (T := Submonoid.powers (t U s b3 (b4 - r * b3) b6))
    (shearEquiv W s b3 b4 b6 r) (by
      rw [Submonoid.map_powers]
      congr 1
      exact shearForward_t W s b3 b4 b6 r)

/-- Every original incidence function survives the localized comparison. -/
theorem xOpenShearEquiv_base (z : Coordinate W s b3 b4 b6) :
    xOpenShearEquiv W s b3 b4 b6 r (algebraMap _ A z) =
      algebraMap _ B (shearForward W s b3 b4 b6 r z) := by
  rw [xOpenShearEquiv, IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

/-- The localized shear preserves the actual reciprocal incidence coordinate. -/
theorem xOpenShearEquiv_inverse :
    xOpenShearEquiv W s b3 b4 b6 r (↑a⁻¹ : A) = (↑b⁻¹ : B) := by
  have hval : xOpenShearEquiv W s b3 b4 b6 r (↑a : A) = (↑b : B) := by
    rw [xOpenUnit_val, xOpenShearEquiv_base, shearForward_t, xOpenUnit_val]
  exact map_inverse_unit (xOpenShearEquiv W s b3 b4 b6 r).toRingHom a b⁻¹
    (by rw [inv_inv]; exact hval)

/-- The full divided-chart attachment commutes with the localized incidence shear. -/
theorem xOpenShearEquiv_dividedToXOpen :
    (xOpenShearEquiv W s b3 b4 b6 r).toAlgHom.comp (dividedToXOpen W s b3 b4 b6) =
      (dividedToXOpen U s b3 (b4 - r * b3) b6).comp
        (WeierstrassDilatation.shearForward W s b3 b4 b6 r) := by
  apply WeierstrassDilatation.hom_ext
  · change xOpenShearEquiv W s b3 b4 b6 r
      (dividedToXOpen W s b3 b4 b6 (WeierstrassDilatation.x W s b3 b4 b6)) = _
    rw [dividedToXOpen, dividedOverlapMap_x, xOpenShearEquiv_inverse]
    rw [AlgHom.comp_apply, WeierstrassDilatation.shearForward_x,
      dividedToXOpen, dividedOverlapMap_x]
  · change xOpenShearEquiv W s b3 b4 b6 r
      (dividedToXOpen W s b3 b4 b6 (WeierstrassDilatation.y W s b3 b4 b6)) = _
    rw [dividedToXOpen, dividedOverlapMap_y, map_mul, xOpenShearEquiv_inverse]
    change (↑b⁻¹ : B) * xOpenShearEquiv W s b3 b4 b6 r
      (algebraMap _ A (v W s b3 b4 b6)) = _
    rw [xOpenShearEquiv_base, shearForward_v, map_add]
    rw [AlgHom.comp_apply, WeierstrassDilatation.shearForward_y, map_add, map_mul,
      AlgHom.commutes, dividedToXOpen, dividedOverlapMap_y, dividedOverlapMap_x]
    rw [← IsScalarTower.algebraMap_apply R _ B]
    simp only [IsScalarTower.toAlgHom_apply]
    ring

end FLT.Mazur.WeierstrassModificationX
