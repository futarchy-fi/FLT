/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalOriginalCoordinates
public import FLT.Mazur.WeierstrassDividedOriginalSmoothReciprocalDenominator
public import FLT.Mazur.WeierstrassSlopeSwapFormula

/-!
# Reverse the original inputs of a divided reciprocal

The reversed pair has the same homogeneous output by the actual line equation.
Original smoothness of the right input supplies its denominator independently.
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

/-- The reversed pair retains the complete right and left original contractions. -/
def dividedReciprocalReversedPair : WeierstrassIntegralChart.AffineProduct W →ₐ[R] B :=
  WeierstrassIntegralChart.chartProductEvaluation W 2 2 ((c').comp orig) ((a').comp orig)

local notation "f" => dividedReciprocalReversedPair W s b3 b4 b6 a c h3 h4 h6 e

/-- The reversed first input is exactly the original right contraction. -/
theorem dividedReciprocalReversedPair_left :
    (f).comp (WeierstrassIntegralChart.productLeft W) = (c').comp orig :=
  WeierstrassIntegralChart.chartProductEvaluation_left ..

/-- The reversed second input is exactly the original left contraction. -/
theorem dividedReciprocalReversedPair_right :
    (f).comp (WeierstrassIntegralChart.productRight W) = (a').comp orig :=
  WeierstrassIntegralChart.chartProductEvaluation_right ..

/-- Reversing the original line preserves its reciprocal slope without cancellation. -/
theorem dividedReciprocalReversedPair_line :
    m * f (WeierstrassIntegralChart.verticalSecantDenominator W) =
      f (WeierstrassIntegralChart.secantDenominator W) := by
  rw [WeierstrassIntegralChart.map_verticalSecantDenominator,
    WeierstrassIntegralChart.map_secantDenominator]
  simp only [WeierstrassIntegralChart.productY₁, WeierstrassIntegralChart.productY₂,
    WeierstrassIntegralChart.productX₁, WeierstrassIntegralChart.productX₂,
    ← AlgHom.comp_apply, dividedReciprocalReversedPair_left,
    dividedReciprocalReversedPair_right]
  simp only [AlgHom.comp_apply, fromOriginal_x, fromOriginal_y, map_mul, AlgHom.commutes]
  have h := congrArg et (dividedReciprocalSlope_line W s b3 b4 b6 a c)
  simp only [map_mul, map_sub, AlgHom.comp_apply] at h
  linear_combination -algebraMap R B s * h

/-- The reversed homogeneous output equals the actual divided reciprocal output. -/
theorem dividedReciprocalReversedPair_coordinates (i : Fin 3) :
    WeierstrassIntegralChart.reciprocalCoordinates W f m i =
      et (dividedReciprocalCoordinates W s b3 b4 b6 a c i) := by
  rw [← dividedReciprocalOriginalPair_coordinates W s b3 b4 b6 a c h3 h4 h6 e]
  have hl := dividedReciprocalOriginalPair_line W s b3 b4 b6 a c h3 h4 h6 e
  simp only [WeierstrassIntegralChart.map_verticalSecantDenominator,
    WeierstrassIntegralChart.map_secantDenominator,
    WeierstrassIntegralChart.productY₁, WeierstrassIntegralChart.productY₂,
    WeierstrassIntegralChart.productX₁, WeierstrassIntegralChart.productX₂,
    ← AlgHom.comp_apply, dividedReciprocalOriginalPair_left,
    dividedReciprocalOriginalPair_right] at hl
  unfold WeierstrassIntegralChart.reciprocalCoordinates
  simp only [WeierstrassIntegralChart.productY₁,
    WeierstrassIntegralChart.productX₁, WeierstrassIntegralChart.productX₂,
    ← AlgHom.comp_apply, dividedReciprocalOriginalPair_left,
    dividedReciprocalOriginalPair_right, dividedReciprocalReversedPair_left,
    dividedReciprocalReversedPair_right]
  exact congrFun (WeierstrassIntegralChart.reciprocalAdditionXYZ_swap
    (W.map (algebraMap R B)) hl) i

/-- Reversal preserves the unit needed for the output localization. -/
theorem dividedReciprocalReversedPair_output_isUnit :
    IsUnit (WeierstrassIntegralChart.reciprocalCoordinates W f m 1) := by
  rw [dividedReciprocalReversedPair_coordinates]
  exact (IsLocalization.Away.algebraMap_isUnit (S := O)
    (dividedReciprocalCoordinates W s b3 b4 b6 a c 1)).map e

/-- Only the right input is assumed originally smooth in this denominator construction. -/
theorem dividedReciprocalReversedPair_denominator_isUnit
    (hc : Set.range (Spec.map (CommRingCat.ofHom (c').toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆ WeierstrassIntegralChart.integralSmoothOpen W) :
    IsUnit (f (WeierstrassIntegralChart.verticalSecantDenominator W)) := by
  apply dividedOriginalSmoothReciprocalPair_denominator W s b3 b4 b6 h3 h4 h6 c' a' hc
  have h := ((dividedReciprocal_difference_isUnit W s b3 b4 b6 a c).map et).neg
  simpa only [map_sub, AlgHom.comp_apply, neg_sub] using h

end FLT.Mazur.WeierstrassDilatation
