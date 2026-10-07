/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionIntersections
public import FLT.Mazur.WeierstrassReciprocalAdditionCompatibility

/-!
# Ordinary and reciprocal slopes on all four mixed intersections

Index each pair by a boolean, retain the two polynomial slope relations,
and deduce inverse slopes on every common restriction. No extra denominator
is inverted on these mixed intersections.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Select the ordinary secant or tangent domain. -/
def ordinaryIndex : Bool → AdditionChartIndex
  | false => .secant
  | true => .tangent

/-- Select the normalized reciprocal secant or tangent domain. -/
def reciprocalIndex : Bool → AdditionChartIndex
  | false => .verticalSecant
  | true => .verticalTangent

/-- Regular ordinary slope in its actual addition-domain ring. -/
def ordinaryChartSlope (b : Bool) : additionChartRing W (ordinaryIndex b) :=
  match b with
  | false => secantSlope W
  | true => tangentSlope W

/-- Regular reciprocal slope after localization at its output coordinate. -/
def reciprocalChartSlope (b : Bool) : additionChartRing W (reciprocalIndex b) :=
  match b with
  | false => reciprocalTargetRestriction W _ (verticalSecantSlope W) (verticalSecantSlope W)
  | true => reciprocalTargetRestriction W _ (verticalTangentSlope W) (verticalTangentSlope W)

/-- The chosen ordinary denominator is invertible on its domain. -/
theorem ordinaryChartDenominator_isUnit (b : Bool) :
    IsUnit (additionChartAlgRestriction W (ordinaryIndex b)
      (if b then tangentDenominator W else secantDenominator W)) := by
  cases b
  · exact IsLocalization.Away.algebraMap_isUnit (secantDenominator W) (S := SecantChart W)
  · exact IsLocalization.Away.algebraMap_isUnit (tangentDenominator W) (S := TangentChart W)

/-- Both ordinary slopes solve the same line relation. -/
theorem ordinaryChartSlope_line (b : Bool) :
    ordinaryChartSlope W b *
        additionChartAlgRestriction W (ordinaryIndex b) (secantDenominator W) =
      additionChartAlgRestriction W (ordinaryIndex b) (verticalSecantDenominator W) := by
  cases b
  · change secantSlope W * secantRestriction W (secantDenominator W) =
      secantRestriction W (verticalSecantDenominator W)
    simpa only [map_secantDenominator, map_verticalSecantDenominator] using
      secantSlope_relation W
  · change tangentSlope W * tangentRestriction W (secantDenominator W) =
      tangentRestriction W (verticalSecantDenominator W)
    simpa only [map_secantDenominator, map_verticalSecantDenominator] using
      tangentSlope_line W

/-- Both ordinary slopes solve the divided-difference relation. -/
theorem ordinaryChartSlope_cubic (b : Bool) :
    ordinaryChartSlope W b *
        additionChartAlgRestriction W (ordinaryIndex b) (tangentDenominator W) =
      additionChartAlgRestriction W (ordinaryIndex b) (tangentNumerator W) := by
  cases b
  · change secantSlope W * secantRestriction W (tangentDenominator W) =
      secantRestriction W (tangentNumerator W)
    have hu := IsLocalization.Away.algebraMap_isUnit (secantDenominator W)
      (S := SecantChart W)
    change IsUnit (secantRestriction W (secantDenominator W)) at hu
    have h := secant_relation _ (productLeft_equation W (secantRestriction W))
      (productRight_equation W (secantRestriction W))
      (by simpa only [map_secantDenominator] using hu) (secantSlope_relation W)
    simpa only [map_tangentDenominator, map_tangentNumerator,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using h
  · exact tangentSlope_relation W

/-- Both reciprocal slopes solve the reversed line relation. -/
theorem reciprocalChartSlope_line (b : Bool) :
    reciprocalChartSlope W b *
        additionChartAlgRestriction W (reciprocalIndex b) (verticalSecantDenominator W) =
      additionChartAlgRestriction W (reciprocalIndex b) (secantDenominator W) := by
  cases b
  · have h : verticalSecantSlope W *
        ratioRestriction W (verticalSecantDenominator W) (verticalSecantDenominator W) =
      ratioRestriction W (verticalSecantDenominator W) (secantDenominator W) :=
      ratioSlope_mul W _ _
    exact (map_mul _ _ _).symm.trans
      (congrArg (reciprocalTargetRestriction W _ (verticalSecantSlope W)) h)
  · have h : verticalTangentSlope W *
        ratioRestriction W (tangentNumerator W) (verticalSecantDenominator W) =
      ratioRestriction W (tangentNumerator W) (secantDenominator W) := by
      simpa only [map_secantDenominator, map_verticalSecantDenominator] using
        verticalTangent_line W
    exact (map_mul _ _ _).symm.trans
      (congrArg (reciprocalTargetRestriction W _ (verticalTangentSlope W)) h)

/-- Both reciprocal slopes solve the reversed divided-difference relation. -/
theorem reciprocalChartSlope_cubic (b : Bool) :
    reciprocalChartSlope W b *
        additionChartAlgRestriction W (reciprocalIndex b) (tangentNumerator W) =
      additionChartAlgRestriction W (reciprocalIndex b) (tangentDenominator W) := by
  cases b
  · exact (map_mul _ _ _).symm.trans
      (congrArg (reciprocalTargetRestriction W
      (ratioRestriction W (verticalSecantDenominator W)) (verticalSecantSlope W))
        (verticalSecant_cubic W))
  · exact (map_mul _ _ _).symm.trans
      (congrArg (reciprocalTargetRestriction W
      (ratioRestriction W (tangentNumerator W)) (verticalTangentSlope W))
        (verticalTangent_cubic W))

/-- All four ordinary/reciprocal intersections have inverse slopes. -/
theorem mixedChartSlopes_inverse (b c : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (reciprocalIndex c) →ₐ[R] S)
    (hbase : f.comp (additionChartAlgRestriction W (ordinaryIndex b)) =
      g.comp (additionChartAlgRestriction W (reciprocalIndex c))) :
    g (reciprocalChartSlope W c) * f (ordinaryChartSlope W b) = 1 := by
  have hb (a) : f (additionChartAlgRestriction W (ordinaryIndex b) a) =
      g (additionChartAlgRestriction W (reciprocalIndex c) a) := DFunLike.congr_fun hbase a
  have hu := (ordinaryChartDenominator_isUnit W b).map f
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hu
  · apply inverse_slopes_of_relations hu
    · simpa only [map_mul] using congrArg f (ordinaryChartSlope_line W false)
    · simpa only [map_mul, ← hb] using congrArg g (reciprocalChartSlope_line W c)
  · apply inverse_slopes_of_relations hu
    · simpa only [map_mul] using congrArg f (ordinaryChartSlope_cubic W true)
    · simpa only [map_mul, ← hb] using congrArg g (reciprocalChartSlope_cubic W c)

end FLT.Mazur.WeierstrassIntegralChart
