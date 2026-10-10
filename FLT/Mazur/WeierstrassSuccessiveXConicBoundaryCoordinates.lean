/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleOverlap

/-!
# Exact conic coordinates on the next divided boundary

The original transition sends the next divided coordinates to t⁻¹ and v/t
on the full conic incidence open. The slope v keeps its original orientation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "C₀" => ConicCoordinate W.a₁ c
local notation "B" => MiddleConicOpen W c
local notation "A" => WeierstrassDilatation.Coordinate W (0 * 0) 0 0 c

/-- The invertible original incidence coordinate on the entire conic boundary. -/
def conicBoundaryUnit : Bˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := B) (conicT W.a₁ c)).unit

/-- The boundary unit retains exactly the original incidence function. -/
theorem conicBoundaryUnit_val : (↑(conicBoundaryUnit W c) : B) =
    algebraMap C₀ B (conicT W.a₁ c) := IsUnit.unit_spec _

/-- The original middle comparison preserves the actual incidence unit. -/
theorem middleConicBoundary_unit :
    middleOverlapToConic W c h2 (↑(xOpenUnit W 0 0 0 0 c)) =
      (↑(conicBoundaryUnit W c) : B) := by
  rw [xOpenUnit_val, middleOverlapToConic_base, middleConicMap_coord]
  exact (conicBoundaryUnit_val W c).symm

/-- The original comparison also preserves the inverse of that incidence unit. -/
theorem middleConicBoundary_inverse :
    middleOverlapToConic W c h2 (↑(xOpenUnit W 0 0 0 0 c)⁻¹) =
      (↑(conicBoundaryUnit W c)⁻¹ : B) := by
  apply (IsUnit.mul_left_inj (conicBoundaryUnit W c).isUnit).mp
  rw [← middleConicBoundary_unit W c h2, ← map_mul, Units.inv_mul, map_one,
    middleConicBoundary_unit, Units.inv_mul]

/-- The next divided horizontal coordinate is precisely the reciprocal conic incidence. -/
theorem middleDividedConicOverlap_x :
    middleDividedConicOverlap W c h2
      (algebraMap A _ (WeierstrassDilatation.x W (0 * 0) 0 0 c)) =
        (↑(conicBoundaryUnit W c)⁻¹ : B) := by
  change middleOverlapToConic W c h2 (overlapForward W 0 0 0 0 c _) = _
  rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_x]
  exact middleConicBoundary_inverse W c h2

/-- The next divided vertical coordinate retains the original conic slope divided by incidence. -/
theorem middleDividedConicOverlap_y :
    middleDividedConicOverlap W c h2
      (algebraMap A _ (WeierstrassDilatation.y W (0 * 0) 0 0 c)) =
        (↑(conicBoundaryUnit W c)⁻¹ : B) * algebraMap C₀ B (conicV W.a₁ c) := by
  change middleOverlapToConic W c h2 (overlapForward W 0 0 0 0 c _) = _
  rw [overlapForward_base, dividedToXOpen, dividedOverlapMap_y, map_mul,
    middleConicBoundary_inverse]
  congr 1
  change middleOverlapToConic W c h2
    (algebraMap (Coordinate W 0 0 0 0 c) _ (coord W 0 0 0 0 c 1)) = _
  rw [middleOverlapToConic_base, middleConicMap_coord]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
