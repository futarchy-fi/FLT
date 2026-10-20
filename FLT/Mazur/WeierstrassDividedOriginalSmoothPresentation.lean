/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOriginalSmoothScale
public import FLT.Mazur.WeierstrassOrdinaryPairPresentation

/-!
# Construct the ordinary presentation on original-smooth divided overlaps

The original smooth input forces the scale to be a unit. Together with the
divided abscissa difference this constructs an ordinary secant presentation
of both original contractions. No extra ordinary presentation is assumed.
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
  (hu : IsUnit (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)))
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "A" => a.comp orig
local notation "C" => c.comp orig

include ha hu in
/-- The concrete original pair evaluation has the invertible ordinary secant denominator. -/
theorem dividedOriginalSmoothPair_denominator :
    IsUnit (WeierstrassIntegralChart.chartProductEvaluation W 2 2 A C
      (if false then WeierstrassIntegralChart.tangentDenominator W else
        WeierstrassIntegralChart.secantDenominator W)) := by
  let f : WeierstrassIntegralChart.AffineProduct W →ₐ[R] B :=
    WeierstrassIntegralChart.chartProductEvaluation W 2 2 A C
  have hl : f.comp (WeierstrassIntegralChart.productLeft W) = A :=
    WeierstrassIntegralChart.chartProductEvaluation_left W 2 2 A C
  have hr : f.comp (WeierstrassIntegralChart.productRight W) = C :=
    WeierstrassIntegralChart.chartProductEvaluation_right W 2 2 A C
  change IsUnit (f (WeierstrassIntegralChart.secantDenominator W))
  rw [WeierstrassIntegralChart.map_secantDenominator]
  simp only [WeierstrassIntegralChart.productX₁, WeierstrassIntegralChart.productX₂,
    ← AlgHom.comp_apply, hl, hr]
  exact dividedOriginalSmooth_originalDifference_isUnit W s b3 b4 b6 h3 h4 h6 a c ha hu

/-- The ordinary secant factorization is constructed from the actual divided inputs. -/
def dividedOriginalSmoothPairPresentation :
    WeierstrassIntegralChart.additionChartRing W
      (WeierstrassIntegralChart.ordinaryIndex false) →ₐ[R] B :=
  WeierstrassIntegralChart.ordinaryPairPresentation W A C false
    (dividedOriginalSmoothPair_denominator W s b3 b4 b6 h3 h4 h6 a c ha hu)

/-- The factorization retains the complete first original contraction. -/
theorem dividedOriginalSmoothPairPresentation_left :
    (dividedOriginalSmoothPairPresentation W s b3 b4 b6 h3 h4 h6 a c ha hu).comp
        (WeierstrassIntegralChart.ordinaryInputLeft W false) = A :=
  WeierstrassIntegralChart.ordinaryPairPresentation_left ..

/-- The same factorization retains the complete second original contraction. -/
theorem dividedOriginalSmoothPairPresentation_right :
    (dividedOriginalSmoothPairPresentation W s b3 b4 b6 h3 h4 h6 a c ha hu).comp
        (WeierstrassIntegralChart.ordinaryInputRight W false) = C :=
  WeierstrassIntegralChart.ordinaryPairPresentation_right ..

end FLT.Mazur.WeierstrassDilatation
