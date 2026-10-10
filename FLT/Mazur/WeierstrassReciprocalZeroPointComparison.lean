/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalCubicSpecialization
public import FLT.Mazur.WeierstrassPartialOrdinaryPointComparison

/-!
# Reciprocal slope zero agrees with the classical vertical sum

The original reciprocal chart evaluation is exactly the infinity evaluation
when its slope vanishes. The input relations then force opposite points, so
the actual partial addition and the classical sum agree on this vertical locus.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b : Bool)

/-- Zero reciprocal slope gives the original infinity evaluation over every target algebra. -/
theorem reciprocalZero_chart_evaluation
    (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
    (hm : f (reciprocalChartSlope W b) = 0) :
    f.comp (reciprocalChartAddition W b) = chartInfinityEvaluation W := by
  apply hom_ext
  intro i
  fin_cases i
  · simp [AlgHom.comp_apply, reciprocalSpecialization_coord, hm,
      chartInfinityEvaluation_coord]
  · simp [AlgHom.comp_apply]
  · simp [AlgHom.comp_apply, reciprocalSpecialization_z, hm,
      chartInfinityEvaluation_coord]

variable {K : Type u} [Field K] [Algebra R K]
  (f : additionChartRing W (reciprocalIndex b) →ₐ[R] K)
  (hm : f (reciprocalChartSlope W b) = 0)

include hm

/-- The two inputs on the vertical reciprocal locus are opposite. -/
theorem reciprocalZero_inputs_opposite :
    f (reciprocalInputLeft W b (coord W 2 0)) =
        f (reciprocalInputRight W b (coord W 2 0)) ∧
      f (reciprocalInputLeft W b (coord W 2 1)) =
        (W.map (algebraMap R K)).toAffine.negY
          (f (reciprocalInputRight W b (coord W 2 0)))
          (f (reciprocalInputRight W b (coord W 2 1))) := by
  have hl := reciprocalSpecialization_line W b f
  have hc := reciprocalSpecialization_cubic W b f
  dsimp only at hc
  rw [hm, zero_mul] at hl hc
  constructor
  · exact sub_eq_zero.mp hl.symm
  · simp only [Affine.negY]
    linear_combination -hc

variable
  (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (reciprocalInputLeft W b (coord W 2 0))) (f (reciprocalInputLeft W b (coord W 2 1))))
  (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (reciprocalInputRight W b (coord W 2 0))) (f (reciprocalInputRight W b (coord W 2 1))))

/-- The actual reciprocal chart output represents the classical sum on its vertical locus. -/
theorem reciprocalZero_fieldPoint_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W (reciprocalIndex b) =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  classical
  obtain ⟨hx, hy⟩ := reciprocalZero_inputs_opposite W b f hm
  have hs : Point.fromAffine (Affine.Point.some _ _ h₁) +
      Point.fromAffine (Affine.Point.some _ _ h₂) = 0 := by
    apply (Point.toAffineAddEquiv (W.map (algebraMap R K)).toProjective).injective
    change (Point.fromAffine (.some _ _ h₁) +
      Point.fromAffine (.some _ _ h₂)).toAffineLift =
        (0 : (W.map (algebraMap R K)).toProjective.Point).toAffineLift
    rw [Point.toAffineLift_add, Point.toAffineLift_zero, Point.fromAffine_some,
      Point.fromAffine_some, Point.toAffineLift_some, Point.toAffineLift_some]
    change Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂ = 0
    exact Affine.Point.add_of_Y_eq hx hy
  rw [hs, projectiveToIntegral_zero]
  have hc : additionCurveChart W (reciprocalIndex b) =
      Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) ≫
        integralCurveChart W 1 := by cases b <;> rfl
  rw [hc, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((f.comp (reciprocalChartAddition W b)).toRingHom)) ≫ _ = _
  rw [reciprocalZero_chart_evaluation W b f hm, chartInfinityEvaluation_base,
    integralCurveZero, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The actual partial addition agrees with the vertical classical sum in every reduction type. -/
theorem reciprocalZero_partial_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain W (reciprocalIndex b) ≫ affinePartialAddition W =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  rw [additionChartToDomain_addition]
  exact reciprocalZero_fieldPoint_sum W b f hm h₁ h₂

end FLT.Mazur.WeierstrassIntegralChart
