/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalSecantFormula
public import FLT.Mazur.WeierstrassDividedReciprocalOutput
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# The original pair and homogeneous output of a divided reciprocal

The concrete original pair evaluation has the divided reciprocal slope and
homogeneous output. These formulas prepare the actual original-chart lift.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedReciprocalOutputRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "O" => DividedReciprocalOutputRing W s b3 b4 b6 a c
local notation "et" => e.comp (IsScalarTower.toAlgHom R T O)
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => ((et).comp j).comp a
local notation "c'" => ((et).comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "m" => et (dividedReciprocalSlope W s b3 b4 b6 a c)

/-- The complete original pair determined by this refinement of the divided source. -/
def dividedReciprocalOriginalPair : WeierstrassIntegralChart.AffineProduct W →ₐ[R] B :=
  WeierstrassIntegralChart.chartProductEvaluation W 2 2 ((a').comp orig) ((c').comp orig)

local notation "f" => dividedReciprocalOriginalPair W s b3 b4 b6 a c h3 h4 h6 e

/-- The left coordinate ring maps to exactly the first original contraction. -/
theorem dividedReciprocalOriginalPair_left :
    (f).comp (WeierstrassIntegralChart.productLeft W) = (a').comp orig :=
  WeierstrassIntegralChart.chartProductEvaluation_left ..

/-- The right coordinate ring maps to exactly the second original contraction. -/
theorem dividedReciprocalOriginalPair_right :
    (f).comp (WeierstrassIntegralChart.productRight W) = (c').comp orig :=
  WeierstrassIntegralChart.chartProductEvaluation_right ..

/-- The original line equation follows from the divided one without canceling the scale. -/
theorem dividedReciprocalOriginalPair_line :
    m * f (WeierstrassIntegralChart.verticalSecantDenominator W) =
      f (WeierstrassIntegralChart.secantDenominator W) := by
  rw [WeierstrassIntegralChart.map_verticalSecantDenominator,
    WeierstrassIntegralChart.map_secantDenominator]
  simp only [WeierstrassIntegralChart.productY₁, WeierstrassIntegralChart.productY₂,
    WeierstrassIntegralChart.productX₁, WeierstrassIntegralChart.productX₂,
    ← AlgHom.comp_apply, dividedReciprocalOriginalPair_left,
    dividedReciprocalOriginalPair_right]
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]
  have h := congrArg et (dividedReciprocalSlope_line W s b3 b4 b6 a c)
  simp only [map_mul, map_sub, AlgHom.comp_apply] at h
  linear_combination algebraMap R B s * h

/-- The homogeneous original coordinates are exactly those already constructed. -/
theorem dividedReciprocalOriginalPair_coordinates (i : Fin 3) :
    WeierstrassIntegralChart.reciprocalCoordinates W f m i =
      et (dividedReciprocalCoordinates W s b3 b4 b6 a c i) := by
  rw [dividedReciprocalRefinement_coordinates]
  unfold WeierstrassIntegralChart.reciprocalCoordinates
  simp only [WeierstrassIntegralChart.productX₁, WeierstrassIntegralChart.productX₂,
    WeierstrassIntegralChart.productY₁, ← AlgHom.comp_apply,
    dividedReciprocalOriginalPair_left, dividedReciprocalOriginalPair_right]
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]

/-- The actual output open supplies the second localization denominator. -/
theorem dividedReciprocalOriginalPair_output_isUnit :
    IsUnit (WeierstrassIntegralChart.reciprocalCoordinates W f m 1) := by
  rw [dividedReciprocalOriginalPair_coordinates]
  exact (IsLocalization.Away.algebraMap_isUnit (S := O)
    (dividedReciprocalCoordinates W s b3 b4 b6 a c 1)).map e

end FLT.Mazur.WeierstrassDilatation
