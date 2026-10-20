/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOriginalSmoothReciprocalDenominator
public import FLT.Mazur.WeierstrassDividedReciprocalOriginalCoordinates

/-!
# Construct the original reciprocal presentation from a divided smooth input

The first input's original smoothness supplies the unit scale. Both genuine
localizations of the original reciprocal chart are then constructed with their
full inputs, slope, and normalized output preserved.
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
local notation "f" => dividedReciprocalOriginalPair W s b3 b4 b6 a c h3 h4 h6 e

variable (ha : Set.range (Spec.map (CommRingCat.ofHom
    ((((e.comp (IsScalarTower.toAlgHom R
      (DividedReciprocalRing W s b3 b4 b6 a c)
      (DividedReciprocalOutputRing W s b3 b4 b6 a c))).comp
        (IsScalarTower.toAlgHom R S
          (DividedReciprocalRing W s b3 b4 b6 a c))).comp a).toRingHom)) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆ WeierstrassIntegralChart.integralSmoothOpen W)

include ha in
/-- The original pair has a unit reciprocal denominator on this actual refinement. -/
theorem dividedReciprocalOriginalPair_denominator_isUnit :
    IsUnit (f (WeierstrassIntegralChart.verticalSecantDenominator W)) := by
  apply dividedOriginalSmoothReciprocalPair_denominator W s b3 b4 b6 h3 h4 h6 a' c' ha
  simpa only [map_sub, AlgHom.comp_apply] using
    (dividedReciprocal_difference_isUnit W s b3 b4 b6 a c).map et

/-- The original reciprocal chart is constructed from these exact divided inputs. -/
def dividedOriginalSmoothReciprocalPresentation :
    WeierstrassIntegralChart.additionChartRing W
      (WeierstrassIntegralChart.reciprocalIndex false) →ₐ[R] B :=
  WeierstrassIntegralChart.reciprocalSecantDomainLift W f
    (dividedReciprocalOriginalPair_denominator_isUnit W s b3 b4 b6 a c h3 h4 h6 e ha) m
    (dividedReciprocalOriginalPair_line W s b3 b4 b6 a c h3 h4 h6 e)
    (dividedReciprocalOriginalPair_output_isUnit W s b3 b4 b6 a c h3 h4 h6 e)

local notation "v" => dividedOriginalSmoothReciprocalPresentation W s b3 b4 b6 a c h3 h4 h6 e ha

/-- The original presentation preserves every function of both inputs. -/
theorem dividedOriginalSmoothReciprocalPresentation_pair :
    (v).comp (WeierstrassIntegralChart.additionChartAlgRestriction W
      (WeierstrassIntegralChart.reciprocalIndex false)) = f :=
  WeierstrassIntegralChart.reciprocalSecantDomainLift_restriction ..

/-- Its first original affine input is exactly the first divided contraction. -/
theorem dividedOriginalSmoothReciprocalPresentation_left :
    (v).comp (WeierstrassIntegralChart.reciprocalInputLeft W false) = (a').comp orig := by
  rw [WeierstrassIntegralChart.reciprocalInputLeft, ← AlgHom.comp_assoc,
    dividedOriginalSmoothReciprocalPresentation_pair, dividedReciprocalOriginalPair_left]

/-- Its second original affine input is exactly the second divided contraction. -/
theorem dividedOriginalSmoothReciprocalPresentation_right :
    (v).comp (WeierstrassIntegralChart.reciprocalInputRight W false) = (c').comp orig := by
  rw [WeierstrassIntegralChart.reciprocalInputRight, ← AlgHom.comp_assoc,
    dividedOriginalSmoothReciprocalPresentation_pair, dividedReciprocalOriginalPair_right]

/-- The actual reciprocal slope is preserved by the constructed original presentation. -/
theorem dividedOriginalSmoothReciprocalPresentation_slope :
    v (WeierstrassIntegralChart.reciprocalChartSlope W false) = m :=
  WeierstrassIntegralChart.reciprocalSecantDomainLift_slope ..

/-- The same actual output normalization is used in both presentations. -/
theorem dividedOriginalSmoothReciprocalPresentation_inverse :
    v (WeierstrassIntegralChart.reciprocalChartInverse W false) =
      e (↑(dividedReciprocalOutputUnit W s b3 b4 b6 a c)⁻¹ : O) := by
  apply WeierstrassIntegralChart.reciprocalSecantDomainLift_inverse
  rw [dividedReciprocalOriginalPair_coordinates]
  simpa only [map_mul, map_one, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using
    congrArg e (dividedReciprocalOutput_normalize W s b3 b4 b6 a c)

/-- The normalized original chart output equals the constructed divided reciprocal output. -/
theorem dividedOriginalSmoothReciprocalPresentation_output :
    (v).comp (WeierstrassIntegralChart.reciprocalChartAddition W false) =
      e.comp (dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  rw [AlgHom.comp_apply, WeierstrassIntegralChart.reciprocalChartAddition_coord, map_mul]
  rw [WeierstrassIntegralChart.reciprocalCoordinates_map,
    dividedOriginalSmoothReciprocalPresentation_pair,
    dividedOriginalSmoothReciprocalPresentation_slope,
    dividedOriginalSmoothReciprocalPresentation_inverse,
    dividedReciprocalOriginalPair_coordinates]
  simp only [AlgHom.comp_apply, dividedReciprocalOutput_coord, map_mul]
  rfl

end FLT.Mazur.WeierstrassDilatation
