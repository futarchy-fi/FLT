/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalPointComparison

/-!
# All four partial addition charts preserve the classical point law

The comparison is uniform in the chart index and in the coefficient extension.
Only nonsingularity of the two inputs is needed; the discriminant may vanish.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The first affine input on any one of the four addition charts. -/
def additionInputLeft (i : AdditionChartIndex) : Coordinate W 2 →ₐ[R] additionChartRing W i :=
  (additionChartAlgRestriction W i).comp (productLeft W)

/-- The second affine input on any one of the four addition charts. -/
def additionInputRight (i : AdditionChartIndex) : Coordinate W 2 →ₐ[R] additionChartRing W i :=
  (additionChartAlgRestriction W i).comp (productRight W)

variable {K : Type u} [Field K] [Algebra R K]
  (i : AdditionChartIndex) (f : additionChartRing W i →ₐ[R] K)
  (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (additionInputLeft W i (coord W 2 0))) (f (additionInputLeft W i (coord W 2 1))))
  (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (additionInputRight W i (coord W 2 0))) (f (additionInputRight W i (coord W 2 1))))

/-- Every actual affine-input chart outputs the scheme point of the classical sum. -/
theorem additionFieldPoint_chart_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W i =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  cases i
  · exact ordinaryFieldPoint_chart_sum W false f h₁ h₂
  · exact ordinaryFieldPoint_chart_sum W true f h₁ h₂
  · exact reciprocalFieldPoint_chart_sum W false f h₁ h₂
  · exact reciprocalFieldPoint_chart_sum W true f h₁ h₂

/-- The actual partial addition gives the classical sum on its four chart domains. -/
theorem additionFieldPoint_partial_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain W i ≫ affinePartialAddition W =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  rw [additionChartToDomain_addition]
  exact additionFieldPoint_chart_sum W i f h₁ h₂

end FLT.Mazur.WeierstrassIntegralChart
