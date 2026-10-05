/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralAdditionCharts
public import FLT.Mazur.WeierstrassReciprocalAdditionChart

/-!
# Regular integral addition charts at vertical chords and tangents

Invert either the y-difference or the divided-difference numerator to obtain a
regular reciprocal slope. Then invert the output y-coordinate to obtain an
actual algebra map from the integral chart containing infinity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- A principal open of the affine product, used for reciprocal slopes. -/
def RatioChart (d : AffineProduct W) := Localization.Away d

instance (d : AffineProduct W) : CommRing (RatioChart W d) :=
  inferInstanceAs (CommRing (Localization.Away d))

instance (d : AffineProduct W) : Algebra (AffineProduct W) (RatioChart W d) :=
  inferInstanceAs (Algebra (AffineProduct W) (Localization.Away d))

instance (d : AffineProduct W) : Algebra R (RatioChart W d) :=
  inferInstanceAs (Algebra R (Localization.Away d))

instance (d : AffineProduct W) : IsScalarTower R (AffineProduct W) (RatioChart W d) :=
  inferInstanceAs (IsScalarTower R (AffineProduct W) (Localization.Away d))

instance (d : AffineProduct W) : IsLocalization.Away d (RatioChart W d) :=
  inferInstanceAs (IsLocalization.Away d (Localization.Away d))

/-- Restriction from the affine product to a principal open. -/
def ratioRestriction (d : AffineProduct W) : AffineProduct W →ₐ[R] RatioChart W d :=
  IsScalarTower.toAlgHom R (AffineProduct W) (RatioChart W d)

/-- A regular ratio with its denominator inverted. -/
def ratioSlope (d n : AffineProduct W) : RatioChart W d :=
  ratioRestriction W d n * IsLocalization.Away.invSelf d

/-- The denominator equation for a regular ratio. -/
theorem ratioSlope_mul (d n : AffineProduct W) :
    ratioSlope W d n * ratioRestriction W d d = ratioRestriction W d n := by
  rw [ratioSlope, mul_assoc, mul_comm (IsLocalization.Away.invSelf _)]
  have h : ratioRestriction W d d * IsLocalization.Away.invSelf d = 1 :=
    IsLocalization.Away.mul_invSelf d
  rw [h, mul_one]

/-- The denominator of a vertical secant's reciprocal slope. -/
def verticalSecantDenominator : AffineProduct W := productY₁ W - productY₂ W

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluation of the vertical secant denominator. -/
theorem map_verticalSecantDenominator (f : AffineProduct W →ₐ[R] S) :
    f (verticalSecantDenominator W) = f (productY₁ W) - f (productY₂ W) := by
  rw [verticalSecantDenominator, map_sub]

/-- Evaluation of the ordinary secant denominator. -/
theorem map_secantDenominator (f : AffineProduct W →ₐ[R] S) :
    f (secantDenominator W) = f (productX₁ W) - f (productX₂ W) := by
  rw [secantDenominator, map_sub]

/-- Evaluation of the ordinary tangent denominator. -/
theorem map_tangentDenominator (f : AffineProduct W →ₐ[R] S) :
    f (tangentDenominator W) = f (productY₁ W) + f (productY₂ W) +
      algebraMap R S W.a₁ * f (productX₂ W) + algebraMap R S W.a₃ := by
  simp only [tangentDenominator, map_add, map_mul, AlgHom.commutes]

/-- Evaluation of the ordinary tangent numerator. -/
theorem map_tangentNumerator (f : AffineProduct W →ₐ[R] S) :
    f (tangentNumerator W) = f (productX₁ W) ^ 2 + f (productX₁ W) * f (productX₂ W) +
      f (productX₂ W) ^ 2 + algebraMap R S W.a₂ * (f (productX₁ W) + f (productX₂ W)) +
      algebraMap R S W.a₄ - algebraMap R S W.a₁ * f (productY₁ W) := by
  simp only [tangentNumerator, map_sub, map_add, map_mul, map_pow, AlgHom.commutes]

/-- The reciprocal secant slope on its principal open. -/
def verticalSecantSlope : RatioChart W (verticalSecantDenominator W) :=
  ratioSlope W (verticalSecantDenominator W) (secantDenominator W)

/-- The reciprocal secant slope satisfies its line equation. -/
theorem verticalSecant_line :
    verticalSecantSlope W *
      (ratioRestriction W (verticalSecantDenominator W) (productY₁ W) -
        ratioRestriction W (verticalSecantDenominator W) (productY₂ W)) =
      ratioRestriction W (verticalSecantDenominator W) (productX₁ W) -
        ratioRestriction W (verticalSecantDenominator W) (productX₂ W) := by
  simpa only [verticalSecantSlope, map_verticalSecantDenominator, map_secantDenominator]
    using ratioSlope_mul W (verticalSecantDenominator W) (secantDenominator W)

/-- The reciprocal secant also satisfies the divided-difference equation. -/
theorem verticalSecant_cubic :
    verticalSecantSlope W *
      ratioRestriction W (verticalSecantDenominator W) (tangentNumerator W) =
      ratioRestriction W (verticalSecantDenominator W) (tangentDenominator W) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (verticalSecantDenominator W)
    (S := RatioChart W (verticalSecantDenominator W))
  change IsUnit (ratioRestriction W (verticalSecantDenominator W)
    (verticalSecantDenominator W)) at hu
  simp only [map_verticalSecantDenominator] at hu
  have h := reciprocal_secant_relation _ (productLeft_equation W _)
    (productRight_equation W _) hu (verticalSecant_line W)
  simpa only [map_tangentNumerator, map_tangentDenominator, map_a₁, map_a₂, map_a₃, map_a₄] using h

/-- Addition through the vertical secant locus into the chart containing infinity. -/
def verticalSecantAddition : Coordinate W 1 →ₐ[R]
    ReciprocalTargetOpen W (ratioRestriction W (verticalSecantDenominator W))
      (verticalSecantSlope W) :=
  reciprocalAddition W _ _ (verticalSecant_line W) (by
    simpa only [map_tangentNumerator, map_tangentDenominator] using verticalSecant_cubic W)

/-- The reciprocal tangent slope on the divided-difference numerator open. -/
def verticalTangentSlope : RatioChart W (tangentNumerator W) :=
  ratioSlope W (tangentNumerator W) (tangentDenominator W)

/-- The reciprocal tangent's defining denominator equation. -/
theorem verticalTangent_cubic :
    verticalTangentSlope W * ratioRestriction W (tangentNumerator W) (tangentNumerator W) =
      ratioRestriction W (tangentNumerator W) (tangentDenominator W) :=
  ratioSlope_mul W (tangentNumerator W) (tangentDenominator W)

/-- The reciprocal tangent also satisfies the line equation. -/
theorem verticalTangent_line :
    verticalTangentSlope W *
      (ratioRestriction W (tangentNumerator W) (productY₁ W) -
        ratioRestriction W (tangentNumerator W) (productY₂ W)) =
      ratioRestriction W (tangentNumerator W) (productX₁ W) -
        ratioRestriction W (tangentNumerator W) (productX₂ W) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (tangentNumerator W)
    (S := RatioChart W (tangentNumerator W))
  change IsUnit (ratioRestriction W (tangentNumerator W) (tangentNumerator W)) at hu
  simp only [map_tangentNumerator] at hu
  apply reciprocal_tangent_relation _ (productLeft_equation W _)
    (productRight_equation W _) hu
  simpa only [map_tangentNumerator, map_tangentDenominator, map_a₁, map_a₂, map_a₃,
    map_a₄] using verticalTangent_cubic W

/-- Addition through the vertical tangent locus into the chart containing infinity. -/
def verticalTangentAddition : Coordinate W 1 →ₐ[R]
    ReciprocalTargetOpen W (ratioRestriction W (tangentNumerator W)) (verticalTangentSlope W) :=
  reciprocalAddition W _ _ (verticalTangent_line W) (by
    simpa only [map_tangentNumerator, map_tangentDenominator, map_a₁, map_a₂, map_a₃,
    map_a₄] using verticalTangent_cubic W)

end FLT.Mazur.WeierstrassIntegralChart
