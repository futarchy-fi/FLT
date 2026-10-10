/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedSections

/-!
# The original marked sections have the canonical normalized frame coordinates

The actual transported evaluations of the three chosen labels are (0,0),
(0,-d), and (-d,0), where d is the constructed unit separation. Thus the
normal form retains its original marked scheme sections.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart WeierstrassFrameNormalization

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original transformation formulas recover coordinates of the actual normalized evaluation. -/
theorem auxiliaryNormalizedEvaluation_coordinates (a : Labels 4) (ha : a ≠ 1) (x y : R)
    (hx : ((auxiliaryFrameChange g).u : R) ^ 2 * x + (auxiliaryFrameChange g).r =
      g (auxiliaryCoordinate a ha 0))
    (hy : ((auxiliaryFrameChange g).u : R) ^ 3 * y +
      ((auxiliaryFrameChange g).u : R) ^ 2 * (auxiliaryFrameChange g).s * x +
        (auxiliaryFrameChange g).t = g (auxiliaryCoordinate a ha 1)) :
    auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 0) = x ∧
      auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 1) = y := by
  apply affineVariableChange_evaluation_coordinates _ _ _ rfl
    (auxiliaryNormalizedEvaluation g a ha) (auxiliaryPullbackEvaluation g a ha)
    (auxiliaryNormalizedEvaluation_comp g a ha) x y
  · simpa only [auxiliaryPullbackEvaluation_coord] using hx
  · simpa only [auxiliaryPullbackEvaluation_coord] using hy

/-- The first original marked section is the origin of the normalized affine chart. -/
theorem auxiliaryNormalizedEvaluation_first :
    auxiliaryNormalizedEvaluation g frameLabelFirst frameLabelFirst_ne
        (coord (auxiliaryNormalizedEquation g) 2 0) = 0 ∧
      auxiliaryNormalizedEvaluation g frameLabelFirst frameLabelFirst_ne
        (coord (auxiliaryNormalizedEquation g) 2 1) = 0 := by
  apply auxiliaryNormalizedEvaluation_coordinates
  · exact (change_first _ _ _ _ _).1
  · exact (change_first _ _ _ _ _).2

/-- The inverse original label is the vertically separated normalized point. -/
theorem auxiliaryNormalizedEvaluation_inverse :
    auxiliaryNormalizedEvaluation g frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne)
        (coord (auxiliaryNormalizedEquation g) 2 0) = 0 ∧
      auxiliaryNormalizedEvaluation g frameLabelFirst⁻¹ (inv_ne_one.mpr frameLabelFirst_ne)
        (coord (auxiliaryNormalizedEquation g) 2 1) = -(auxiliaryFrameSeparation g : R) := by
  apply auxiliaryNormalizedEvaluation_coordinates
  · rw [auxiliaryCoordinate_inverse_x frameLabelFirst frameLabelFirst_ne]
    exact (change_first _ _ _ _ _).1
  · apply change_inverse
    change g (auxiliaryFrameVerticalUnit : AuxiliarySectionRing) = _
    rw [auxiliaryFrameVerticalUnit_val, map_sub]

/-- The third original label is the horizontally separated normalized point. -/
theorem auxiliaryNormalizedEvaluation_third :
    auxiliaryNormalizedEvaluation g frameLabelThird frameLabelThird_ne
        (coord (auxiliaryNormalizedEquation g) 2 0) = -(auxiliaryFrameSeparation g : R) ∧
      auxiliaryNormalizedEvaluation g frameLabelThird frameLabelThird_ne
        (coord (auxiliaryNormalizedEquation g) 2 1) = 0 := by
  have hh : ((Units.map g auxiliaryFrameHorizontalUnit : Rˣ) : R) =
      g (auxiliaryCoordinate frameLabelFirst frameLabelFirst_ne 0) -
        g (auxiliaryCoordinate frameLabelThird frameLabelThird_ne 0) := by
    change g (auxiliaryFrameHorizontalUnit : AuxiliarySectionRing) = _
    rw [auxiliaryFrameHorizontalUnit_val, map_sub]
  apply auxiliaryNormalizedEvaluation_coordinates
  · exact (change_third _ _ _ _ _ _ hh).1
  · exact (change_third _ _ _ _ _ _ hh).2

end FLT.Mazur.UniversalWeierstrass
