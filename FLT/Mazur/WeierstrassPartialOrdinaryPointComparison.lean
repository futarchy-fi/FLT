/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryPointComparison
public import FLT.Mazur.WeierstrassAffinePartialAddition

/-!
# Ordinary partial addition agrees with classical field points in bad reduction

The original ordinary chart output represents the classical sum whenever
both inputs are nonsingular. This comparison uses no discriminant assumption
and applies to the actual partial addition on the union of the four charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R) (b : Bool)
  (f : additionChartRing W (ordinaryIndex b) →ₐ[R] K)
  (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (ordinaryInputLeft W b (coord W 2 0))) (f (ordinaryInputLeft W b (coord W 2 1))))
  (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (ordinaryInputRight W b (coord W 2 0))) (f (ordinaryInputRight W b (coord W 2 1))))

/-- The ordinary local output is the scheme point of the classical nonsingular sum. -/
theorem ordinaryFieldPoint_chart_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W (ordinaryIndex b) =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  have hc : additionCurveChart W (ordinaryIndex b) =
      Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) ≫
        integralCurveChart W 2 := by cases b <;> rfl
  rw [hc, ← Category.assoc, ← Spec.map_comp]
  rw [projectiveToIntegral_chart W _ 2 _
    (chartAlgHom_equation W 2 (f.comp (ordinaryChartAddition W b))) (by simp)
    (ordinarySpecialization_projective_sum W b f h₁ h₂).symm,
    integralChartPoint, evaluation_chartAlgHom]
  rfl

/-- The actual partial addition preserves the classical point sum on both ordinary charts. -/
theorem ordinaryFieldPoint_partial_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain W (ordinaryIndex b) ≫ affinePartialAddition W =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  rw [additionChartToDomain_addition]
  exact ordinaryFieldPoint_chart_sum W b f h₁ h₂

end FLT.Mazur.WeierstrassIntegralChart
