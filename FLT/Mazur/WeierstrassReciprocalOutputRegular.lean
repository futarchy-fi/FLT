/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineProductDifference
public import FLT.Mazur.WeierstrassReciprocalAffineUnits
public import FLT.Mazur.WeierstrassAffinePolynomialIntersections

/-!
# Regular reciprocal slopes and output coordinates

The regular affine X difference remains regular on every addition chart.
The reciprocal line relation then makes both reciprocal slopes regular,
including the vertical tangent chart. Their normalized output Z coordinates
are regular even where those coordinates are not units.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The ordinary secant denominator is regular on the original affine product. -/
theorem secantDenominator_regular : IsRegular (secantDenominator W) := by
  have h : IsRegular (productX₂ W - productX₁ W) :=
    affineProduct_x_right_sub_left_regular W
  have hn := (isUnit_neg_one (α := AffineProduct W)).isRegular.mul h
  simpa only [neg_one_mul, neg_sub, secantDenominator] using hn

/-- All four actual affine addition restrictions are flat. -/
theorem additionChartRestriction_flat (i : AdditionChartIndex) :
    (additionChartRestriction W i).Flat :=
  Flat.SpecMap_iff.mp (inferInstance : Flat (additionChartInclusion W i))

/-- The actual reciprocal slope is regular by its line equation. -/
theorem reciprocalChartSlope_regular (b : Bool) : IsRegular (reciprocalChartSlope W b) := by
  have h := flatRingHom_isRegular (additionChartRestriction W (reciprocalIndex b))
    (additionChartRestriction_flat W (reciprocalIndex b)) (secantDenominator_regular W)
  rw [← additionChartAlgRestriction_toRingHom] at h
  change IsRegular (additionChartAlgRestriction W (reciprocalIndex b)
    (secantDenominator W)) at h
  rw [← reciprocalChartSlope_line] at h
  exact h.of_mul_left

/-- Both actual reciprocal addition charts have regular normalized output Z. -/
theorem reciprocalChartAddition_z_regular (b : Bool) :
    IsRegular (reciprocalChartAddition W b (coord W 1 2)) := by
  have h := reciprocalSpecialization_z W b (AlgHom.id R _)
  simp only [AlgHom.id_apply] at h
  rw [h]
  exact (reciprocalChartInverse_isUnit W b).isRegular.mul
    ((reciprocalChartSlope_regular W b).pow 3)

/-- Every ordinary or reciprocal affine-input law has regular output Z. -/
theorem additionChartAlgOutput_z_regular (i : AdditionChartIndex) :
    IsRegular (additionChartAlgOutput W i (coord W (additionChartOutput i) 2)) := by
  cases i with
  | secant =>
    change IsRegular (secantAddition W (coord W 2 2))
    rw [coord_self, map_one]
    exact isRegular_one
  | tangent =>
    change IsRegular (tangentAddition W (coord W 2 2))
    rw [coord_self, map_one]
    exact isRegular_one
  | verticalSecant => exact reciprocalChartAddition_z_regular W false
  | verticalTangent => exact reciprocalChartAddition_z_regular W true

/-- Flat scheme maps preserve the actual output regularity, without source affineness. -/
theorem additionChart_output_z_regular_sections (i : AdditionChartIndex) {X : Scheme}
    (f : X ⟶ Spec (additionChartRing W i)) [Flat f] :
    IsRegular (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))) :=
  specSectionHom_isRegular f (additionChartAlgOutput_z_regular W i)

end FLT.Mazur.WeierstrassIntegralChart
