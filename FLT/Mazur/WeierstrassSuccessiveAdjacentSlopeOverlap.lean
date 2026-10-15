/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveLaurentSlopeLocalization
public import FLT.Mazur.WeierstrassSuccessiveXHorizontalLocalization

/-!
# The entire original adjacent localization transition on slope branches

The two original localized transitions agree on all functions whenever their
constructed slopes agree in the original Laurent coordinate.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r : SuccessiveIncidence.Coordinate π)
  (hr : r ^ 2 + nodeSlopeLinear W π b3 * r = nodeSlopeConstant W s π b4 b6)
local notation "U" => rightIncidenceLaurent π
local notation "ev" => AlgHom.comp (rightIncidenceLaurent π)
  (simpleSlopeRetraction W s π b3 b4 b6 r hr)

/-- Extend the original right slope evaluation to the full horizontal localization. -/
def rightSlopeLaurent : HorizontalOpen W s π b3 b4 b6 →ₐ[R] R[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (coord W s π b3 b4 b6 2) (f := ev) (by
    change IsUnit (U (simpleSlopeRetraction W s π b3 b4 b6 r hr
      (coord W s π b3 b4 b6 2)))
    simp only [simpleSlopeRetraction_coord, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, rightIncidenceLaurent_u]
    exact LaurentPolynomial.isUnit_T (R := R) 1)

/-- The right localization retains every original chart function. -/
theorem rightSlopeLaurent_base (z : Coordinate W s π b3 b4 b6) :
    rightSlopeLaurent W s π b3 b4 b6 r hr (algebraMap _ _ z) =
      U (simpleSlopeRetraction W s π b3 b4 b6 r hr z) := by
  rw [rightSlopeLaurent, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

variable (r₀ r₁ : SuccessiveIncidence.Coordinate π)
  (h₀ : r₀ ^ 2 + nodeSlopeLinear W π (π * b3) * r₀ =
    nodeSlopeConstant W s π (π * b4) (π ^ 2 * b6))
  (h₁ : r₁ ^ 2 + nodeSlopeLinear W π b3 * r₁ =
    nodeSlopeConstant W (s * π) π b4 b6)
  (h : inverseLeftIncidenceLaurent π r₀ = rightIncidenceLaurent π r₁)
local notation "L₀" => inverseLeftSlopeLaurent W s π (π * b3) (π * b4) (π ^ 2 * b6) r₀ h₀
local notation "U₁" => rightSlopeLaurent W (s * π) π b3 b4 b6 r₁ h₁

include h in
/-- The complete original divided boundary maps agree, with no functions discarded. -/
theorem adjacentSlopeLaurent_overlap :
    (L₀).comp (overlapForward W s π (π * b3) (π * b4) (π ^ 2 * b6)) =
      (U₁).comp (horizontalForward W (s * π) π b3 b4 b6) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (WeierstrassDilatation.x W (s * π)
      (π * b3) (π * b4) (π ^ 2 * b6)))
  apply WeierstrassDilatation.hom_ext
  · change L₀ (overlapForward _ _ _ _ _ _ (algebraMap _ _ _)) =
      U₁ (horizontalForward _ _ _ _ _ _ (algebraMap _ _ _))
    rw [overlapForward_base, inverseLeftSlopeLaurent_divided_x,
      horizontalForward_base, fromDivided_x, rightSlopeLaurent_base,
      simpleSlopeRetraction_coord]
    exact (rightIncidenceLaurent_u π).symm
  · change L₀ (overlapForward _ _ _ _ _ _ (algebraMap _ _ _)) =
      U₁ (horizontalForward _ _ _ _ _ _ (algebraMap _ _ _))
    rw [overlapForward_base, inverseLeftSlopeLaurent_divided_y,
      horizontalForward_base, fromDivided_y, rightSlopeLaurent_base,
      map_mul, simpleSlopeRetraction_coord, simpleSlopeRetraction_coord]
    change _ * inverseLeftIncidenceLaurent π r₀ =
      U (SuccessiveIncidence.u π * r₁)
    rw [map_mul, rightIncidenceLaurent_u, h]

end FLT.Mazur.WeierstrassSuccessiveX
