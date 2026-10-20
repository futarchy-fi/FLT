/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOriginalSmoothScale
public import FLT.Mazur.WeierstrassReciprocalSecantDomainLift
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# Invert the original ordinate difference on smooth divided overlaps

The original smooth input forces the scale to be a unit. Together with the
divided ordinate difference this makes the original reciprocal denominator
invertible. The output localization is constructed separately.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] B)
  (ha : Set.range (Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    toCurve W s b3 b4 b6 h3 h4 h6) ⊆ WeierstrassIntegralChart.integralSmoothOpen W)
  (hu : IsUnit (a (y W s b3 b4 b6) - c (y W s b3 b4 b6)))
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => a.comp orig
local notation "C" => c.comp orig

include ha hu in
/-- The concrete original pair evaluation has the invertible original reciprocal denominator. -/
theorem dividedOriginalSmoothReciprocalPair_denominator :
    IsUnit (WeierstrassIntegralChart.chartProductEvaluation W 2 2 A C
      (WeierstrassIntegralChart.verticalSecantDenominator W)) := by
  let f : WeierstrassIntegralChart.AffineProduct W →ₐ[R] B :=
    WeierstrassIntegralChart.chartProductEvaluation W 2 2 A C
  have hl : f.comp (WeierstrassIntegralChart.productLeft W) = A :=
    WeierstrassIntegralChart.chartProductEvaluation_left W 2 2 A C
  have hr : f.comp (WeierstrassIntegralChart.productRight W) = C :=
    WeierstrassIntegralChart.chartProductEvaluation_right W 2 2 A C
  change IsUnit (f (WeierstrassIntegralChart.verticalSecantDenominator W))
  rw [WeierstrassIntegralChart.map_verticalSecantDenominator]
  simp only [WeierstrassIntegralChart.productY₁, WeierstrassIntegralChart.productY₂,
    ← AlgHom.comp_apply, hl, hr]
  simp only [AlgHom.comp_apply, fromOriginal_y, map_mul, AlgHom.commutes]
  convert (dividedOriginalSmooth_scale_isUnit W s b3 b4 b6 h3 h4 h6 a ha).mul hu using 1
  ring

end FLT.Mazur.WeierstrassDilatation
