/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveLaurentBoundary
public import FLT.Mazur.WeierstrassSuccessiveSimpleSlopeChart
public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# Evaluating the original localized overlap on a constructed Laurent branch

The inverse-left evaluation extends the original slope retraction to the
actual localization. Its divided coordinates are z and z times the slope.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r : SuccessiveIncidence.Coordinate π)
  (hr : r ^ 2 + nodeSlopeLinear W π b3 * r = nodeSlopeConstant W s π b4 b6)
local notation "L" => inverseLeftIncidenceLaurent π
local notation "ev" => AlgHom.comp (inverseLeftIncidenceLaurent π)
  (simpleSlopeRetraction W s π b3 b4 b6 r hr)

/-- Evaluate the original left localization in the inverse polygon edge coordinate. -/
def inverseLeftSlopeLaurent : XOpen W s π b3 b4 b6 →ₐ[R] R[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (coord W s π b3 b4 b6 0) (f := ev) (by
    simp only [AlgHom.comp_apply, simpleSlopeRetraction_coord,
      Matrix.cons_val_zero, inverseLeftIncidenceLaurent_t]
    exact LaurentPolynomial.isUnit_T (-1))

/-- Localization retains the original slope evaluation on every chart function. -/
theorem inverseLeftSlopeLaurent_base (z : Coordinate W s π b3 b4 b6) :
    inverseLeftSlopeLaurent W s π b3 b4 b6 r hr (algebraMap _ _ z) =
      L (simpleSlopeRetraction W s π b3 b4 b6 r hr z) := by
  rw [inverseLeftSlopeLaurent, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The inverse localized incidence coordinate is the next original Laurent variable. -/
theorem inverseLeftSlopeLaurent_inverse :
    inverseLeftSlopeLaurent W s π b3 b4 b6 r hr
      (↑(xOpenUnit W s π b3 b4 b6)⁻¹) = LaurentPolynomial.T 1 := by
  apply map_inverse_unit _ _ (LaurentUnitPoints.pointUnit (AlgHom.id R R[T;T⁻¹]))
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [xOpenUnit_val, inverseLeftSlopeLaurent_base, simpleSlopeRetraction_coord]
  exact inverseLeftIncidenceLaurent_t π

/-- The original divided horizontal coordinate evaluates to the next right coordinate. -/
theorem inverseLeftSlopeLaurent_divided_x :
    inverseLeftSlopeLaurent W s π b3 b4 b6 r hr
      (dividedToXOpen W s π b3 b4 b6
        (WeierstrassDilatation.x W (s * π) b3 b4 b6)) = LaurentPolynomial.T 1 := by
  rw [dividedToXOpen, dividedOverlapMap_x, inverseLeftSlopeLaurent_inverse]

/-- The original divided vertical coordinate keeps the constructed slope as its ratio. -/
theorem inverseLeftSlopeLaurent_divided_y :
    inverseLeftSlopeLaurent W s π b3 b4 b6 r hr
      (dividedToXOpen W s π b3 b4 b6
        (WeierstrassDilatation.y W (s * π) b3 b4 b6)) =
      LaurentPolynomial.T 1 * L r := by
  rw [dividedToXOpen, dividedOverlapMap_y, map_mul, inverseLeftSlopeLaurent_inverse]
  change _ * inverseLeftSlopeLaurent W s π b3 b4 b6 r hr (algebraMap _ _ _) = _
  rw [inverseLeftSlopeLaurent_base, simpleSlopeRetraction_coord]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
