/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalOrdinaryComparison

/-!
# Reciprocal addition represents the classical sum over every field

Nonzero reciprocal slope is reduced to the ordinary chart using the actual
common-domain comparison. Together with the vertical case, this covers both
reciprocal charts with no restriction on the reduction type.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (b : Bool)
  (f : additionChartRing W (reciprocalIndex b) →ₐ[R] K)

variable
  (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (reciprocalInputLeft W b (coord W 2 0))) (f (reciprocalInputLeft W b (coord W 2 1))))
  (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (reciprocalInputRight W b (coord W 2 0))) (f (reciprocalInputRight W b (coord W 2 1))))

/-- Nonzero reciprocal slope gives the classical sum through the ordinary lift. -/
theorem reciprocalNonzero_fieldPoint_sum
    (hm : f (reciprocalChartSlope W b) ≠ 0) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W (reciprocalIndex b) =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  have hz := (reciprocalSpecialization_z_isUnit_iff W b f).mpr (isUnit_iff_ne_zero.mpr hm)
  let g := reciprocalAffineOrdinaryLift W b f hz
  have hl (i : Fin 3) : g (ordinaryInputLeft W b (coord W 2 i)) =
      f (reciprocalInputLeft W b (coord W 2 i)) :=
    DFunLike.congr_fun (reciprocalAffineOrdinaryLift_left W b f hz) (coord W 2 i)
  have hr (i : Fin 3) : g (ordinaryInputRight W b (coord W 2 i)) =
      f (reciprocalInputRight W b (coord W 2 i)) :=
    DFunLike.congr_fun (reciprocalAffineOrdinaryLift_right W b f hz) (coord W 2 i)
  have hg₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (g (ordinaryInputLeft W b (coord W 2 0)))
      (g (ordinaryInputLeft W b (coord W 2 1))) := by rw [hl, hl]; exact h₁
  have hg₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (g (ordinaryInputRight W b (coord W 2 0)))
      (g (ordinaryInputRight W b (coord W 2 1))) := by rw [hr, hr]; exact h₂
  rw [← reciprocalAffineOrdinaryLift_output W b f hz]
  simpa only [hl, hr] using ordinaryFieldPoint_chart_sum W b g hg₁ hg₂

/-- Both reciprocal charts agree with the classical nonsingular point group law. -/
theorem reciprocalFieldPoint_chart_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ additionCurveChart W (reciprocalIndex b) =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  by_cases hm : f (reciprocalChartSlope W b) = 0
  · exact reciprocalZero_fieldPoint_sum W b f hm h₁ h₂
  · exact reciprocalNonzero_fieldPoint_sum W b f h₁ h₂ hm

/-- The actual partial addition preserves the classical sum on both reciprocal charts. -/
theorem reciprocalFieldPoint_partial_sum :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionChartToDomain W (reciprocalIndex b) ≫ affinePartialAddition W =
      (projectiveToIntegral W
        (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂))).left := by
  rw [additionChartToDomain_addition]
  exact reciprocalFieldPoint_chart_sum W b f h₁ h₂

end FLT.Mazur.WeierstrassIntegralChart
