/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginParameter
public import FLT.Mazur.WeierstrassProductOverlap

/-!
# Exact pole formulas for the original affine coordinates

On the punctured parameter neighborhood, the original affine coordinates
satisfy x_aff t^2 = D and y_aff t^3 = D. The coefficient D is a unit with
value one at the origin. These are identities on the actual chart overlap.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Remove the parameter divisor from the actual origin neighborhood. -/
abbrev OriginPuncture := Localization.Away (originCoordinate W 0)

/-- The original infinity chart map into the punctured neighborhood. -/
def originPunctureChart : Coordinate W 1 →ₐ[R] OriginPuncture W :=
  IsScalarTower.toAlgHom R (Coordinate W 1) (OriginPuncture W)

/-- The actual parameter becomes a unit on the punctured neighborhood. -/
theorem originPuncture_parameter_isUnit :
    IsUnit (originPunctureChart W (coord W 1 0)) := by
  change IsUnit (algebraMap (Coordinate W 1) (OriginPuncture W) (coord W 1 0))
  rw [IsScalarTower.algebraMap_apply (Coordinate W 1) (OriginNeighborhood W)]
  exact IsLocalization.Away.algebraMap_isUnit (originCoordinate W 0)

/-- The original z coordinate is a unit on the punctured neighborhood. -/
theorem originPuncture_z_isUnit : IsUnit (originPunctureChart W (coord W 1 2)) := by
  have h := congrArg (originPunctureChart W) (originDenominator_relation W)
  simp only [map_mul, map_pow] at h
  have he : IsUnit (originPunctureChart W (coord W 1 2) *
      originPunctureChart W (originDenominator W)) := by
    rw [h]
    exact (originPuncture_parameter_isUnit W).pow 3
  exact isUnit_of_mul_isUnit_left he

/-- The original overlap map on the punctured parameter neighborhood. -/
def originPunctureOverlap : Overlap W 1 2 →ₐ[R] OriginPuncture W :=
  overlapLift W 1 2 (originPunctureChart W) (originPuncture_z_isUnit W)

/-- Restriction retains every original infinity coordinate. -/
@[simp] theorem originPunctureOverlap_coord (i : Fin 3) :
    originPunctureOverlap W (overlapCoord W 1 2 i) = originPunctureChart W (coord W 1 i) :=
  DFunLike.congr_fun (overlapLift_restriction W 1 2
    (originPunctureChart W) (originPuncture_z_isUnit W)) (coord W 1 i)

/-- The actual original affine chart map into the punctured parameter neighborhood. -/
def originPunctureAffine : Coordinate W 2 →ₐ[R] OriginPuncture W :=
  (originPunctureOverlap W).comp (transitionBase W 1 2)

/-- Original affine coordinates are the original homogeneous coordinates divided by z. -/
theorem originPunctureAffine_mul_z (i : Fin 3) :
    originPunctureAffine W (coord W 2 i) * originPunctureChart W (coord W 1 2) =
      originPunctureChart W (coord W 1 i) := by
  have hi := congrArg (originPunctureOverlap W) (overlapInverse_mul W 1 2)
  simp only [map_mul, map_one, originPunctureOverlap_coord] at hi
  change originPunctureOverlap W (transitionBase W 1 2 (coord W 2 i)) * _ = _
  rw [transitionBase_coord, map_mul, originPunctureOverlap_coord]
  linear_combination originPunctureChart W (coord W 1 i) * hi

/-- The original affine x coordinate has the exact pole-two parameter formula. -/
theorem originPunctureAffine_x_pole :
    originPunctureAffine W (coord W 2 0) * originPunctureChart W (coord W 1 0) ^ 2 =
      originPunctureChart W (originDenominator W) := by
  apply (originPuncture_parameter_isUnit W).mul_left_inj.mp
  have hr := congrArg (originPunctureChart W) (originDenominator_relation W)
  simp only [map_mul, map_pow] at hr
  linear_combination originPunctureChart W (originDenominator W) *
    originPunctureAffine_mul_z W 0 - originPunctureAffine W (coord W 2 0) * hr

/-- The original affine y coordinate has the exact pole-three parameter formula. -/
theorem originPunctureAffine_y_pole :
    originPunctureAffine W (coord W 2 1) * originPunctureChart W (coord W 1 0) ^ 3 =
      originPunctureChart W (originDenominator W) := by
  have hr := congrArg (originPunctureChart W) (originDenominator_relation W)
  simp only [map_mul, map_pow] at hr
  have hy := originPunctureAffine_mul_z W 1
  rw [coord_self, map_one] at hy
  linear_combination originPunctureChart W (originDenominator W) * hy -
    originPunctureAffine W (coord W 2 1) * hr

end FLT.Mazur.WeierstrassIntegralChart
