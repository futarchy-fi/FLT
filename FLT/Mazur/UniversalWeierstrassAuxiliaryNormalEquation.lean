/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryFrameUnits
public import FLT.Mazur.UniversalWeierstrassAuxiliaryPullbackSections
public import FLT.Mazur.WeierstrassFrameNormalEquation
public import FLT.Mazur.WeierstrassAffineProduct

/-!
# The explicit normalized equation of the original auxiliary family

Apply canonical frame normalization to the original auxiliary sections after
any ring pullback. The resulting smooth equation has only three coefficients;
its normalization and nonzero separation are constructed, not assumed.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original auxiliary affine coordinates solve the pulled-back affine equation. -/
theorem auxiliaryPullbackCoordinate_affine (a : Labels 4) (ha : a ≠ 1) :
    (auxiliaryPullbackEquation g).toAffine.Equation
      (g (auxiliaryCoordinate a ha 0)) (g (auxiliaryCoordinate a ha 1)) := by
  simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id,
    auxiliaryPullbackEvaluation_coord] using
    affine_equation_of_hom _ (auxiliaryPullbackEvaluation g a ha)

/-- The actual original family after applying its constructed frame normalization. -/
def auxiliaryNormalizedEquation : WeierstrassCurve R :=
  auxiliaryFrameChange g • auxiliaryPullbackEquation g

/-- The normalized auxiliary equation has the explicit three-parameter form. -/
theorem auxiliaryNormalizedEquation_eq :
    auxiliaryNormalizedEquation g = WeierstrassFrameNormalEquation.equation
      (auxiliaryNormalizedEquation g).a₁ (auxiliaryNormalizedEquation g).a₂
      (auxiliaryFrameSeparation g) := by
  apply WeierstrassFrameNormalEquation.normalized_eq
    (auxiliaryPullbackEquation g)
    (g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0))
    (g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 1))
    (g (auxiliaryCoordinate frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne) 1))
    (g (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0))
    (g (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 1))
    (Units.map g auxiliaryFrameHorizontalUnit) (Units.map g auxiliaryFrameVerticalUnit)
  · change g (auxiliaryFrameHorizontalUnit : AuxiliarySectionRing) = _
    rw [auxiliaryFrameHorizontalUnit_val, map_sub]
  · change g (auxiliaryFrameVerticalUnit : AuxiliarySectionRing) = _
    rw [auxiliaryFrameVerticalUnit_val, map_sub]
  · exact auxiliaryPullbackCoordinate_affine g frameLabelFirst frameLabelFirst_ne
  · have hn := auxiliaryPullbackCoordinate_affine g frameLabelFirst⁻¹
      (inv_ne_one.mpr frameLabelFirst_ne)
    rw [auxiliaryCoordinate_inverse_x frameLabelFirst frameLabelFirst_ne] at hn
    exact hn
  · exact auxiliaryPullbackCoordinate_affine g frameLabelThird frameLabelThird_ne

/-- The normalized equation stays smooth over the entire original coefficient ring. -/
theorem auxiliaryNormalizedEquation_discriminant :
    IsUnit (auxiliaryNormalizedEquation g).Δ := by
  rw [auxiliaryNormalizedEquation, variableChange_Δ]
  exact ((auxiliaryFrameChange g).u⁻¹.isUnit.pow 12).mul
    (auxiliaryPullbackEquation_discriminant g)

end FLT.Mazur.UniversalWeierstrass
