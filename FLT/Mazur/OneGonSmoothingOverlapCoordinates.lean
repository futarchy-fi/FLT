/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingNodeChart
public import FLT.Mazur.OneGonSmoothingInfinityChart
public import FLT.Mazur.OneGonMobiusConductors

/-!
# The original puncture coordinates in the zero-parameter cubic

The actual endpoint-equalizer restriction makes y invertible. Its inverse
rescales x,y,1 to the original torus coordinates on the chart at infinity.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart PolygonNodePresentation OneGonTransition
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

/-- Restriction from the original pinched algebra, as a coefficient algebra map. -/
def nodePunctureAlgebraMap : B (R := K) →ₐ[K] puncture K where
  __ := bPunctureMap
  commutes' r := by
    exact (IsScalarTower.algebraMap_apply K (Polynomial K) (puncture K) r).symm

/-- The affine chart restricts through the actual original pinched chart. -/
def zeroAffinePuncture : Coordinate (equation (0 : K)) 2 →ₐ[K] puncture K :=
  (nodePunctureAlgebraMap K).comp (zeroAffineNodeEquiv K).toAlgHom

/-- The first coordinate retains the original conductor. -/
@[simp] theorem zeroAffinePuncture_x :
    zeroAffinePuncture K (coord (equation (0 : K)) 2 0) =
      (coordinate K : puncture K) * (difference K : puncture K) := by
  change nodePunctureAlgebraMap K (zeroAffineNodeEquiv K _) = _
  rw [zeroAffineNodeEquiv_x]
  exact puncture_conductor K

/-- The second coordinate retains the original conductor monomial. -/
@[simp] theorem zeroAffinePuncture_y :
    zeroAffinePuncture K (coord (equation (0 : K)) 2 1) =
      (coordinate K : puncture K) ^ 2 * (difference K : puncture K) := by
  change nodePunctureAlgebraMap K (zeroAffineNodeEquiv K _) = _
  rw [zeroAffineNodeEquiv_y]
  exact puncture_monomial K

/-- The original y coordinate is invertible on the actual overlap. -/
theorem zeroAffinePuncture_y_isUnit :
    IsUnit (zeroAffinePuncture K (coord (equation (0 : K)) 2 1)) := by
  rw [zeroAffinePuncture_y]
  exact ((coordinate K).isUnit.pow 2).mul (difference K).isUnit

/-- The actual original puncture supplies a point of the normalized Y/Z overlap. -/
def zeroOverlapPuncture : Overlap (equation (0 : K)) 2 1 →ₐ[K] puncture K :=
  IsLocalization.Away.liftAlgHom _ (zeroAffinePuncture_y_isUnit K)

/-- The overlap lift retains each original affine coordinate. -/
@[simp] theorem zeroOverlapPuncture_coord (i : Fin 3) :
    zeroOverlapPuncture K (overlapCoord (equation (0 : K)) 2 1 i) =
      zeroAffinePuncture K (coord (equation (0 : K)) 2 i) :=
  IsLocalization.Away.lift_eq _ (zeroAffinePuncture_y_isUnit K) _

/-- The normalizing inverse is the inverse of the original conductor monomial. -/
theorem zeroOverlapPuncture_inverse :
    zeroOverlapPuncture K (overlapInverse (equation (0 : K)) 2 1) =
      (↑((coordinate K ^ 2 * difference K)⁻¹) : puncture K) := by
  apply (zeroAffinePuncture_y_isUnit K).mul_left_inj.mp
  have h := congrArg (zeroOverlapPuncture K)
    (overlapInverse_mul (equation (0 : K)) 2 1)
  rw [map_mul, map_one, zeroOverlapPuncture_coord] at h
  rw [h, zeroAffinePuncture_y]
  exact (Units.inv_mul (coordinate K ^ 2 * difference K)).symm

/-- The actual Möbius coordinate gives the reciprocal normalization coordinate. -/
theorem one_sub_mobius_inverse :
    1 - (↑(mobius K)⁻¹ : puncture K) = (↑(coordinate K)⁻¹ : puncture K) := by
  apply (coordinate K).isUnit.mul_right_inj.mp
  have hd := difference_val K
  have hi := Units.inv_mul (coordinate K)
  change (↑(coordinate K)⁻¹ : puncture K) * ↑(coordinate K) = 1 at hi
  simp only [mobius, mul_inv_rev, inv_inv, Units.val_mul]
  linear_combination -hd - (1 + (difference K : puncture K)) * hi

/-- Restriction to the original puncture retains the negative Laurent generator. -/
theorem overlapMap_T_neg :
    overlapMap K (LaurentPolynomial.T (-1)) = (↑(mobius K)⁻¹ : puncture K) := by
  apply (mobius K).isUnit.mul_right_inj.mp
  rw [← overlapMap_T K, ← map_mul, ← LaurentPolynomial.T_add]
  norm_num

end FLT.Mazur.OneGonSmoothing
