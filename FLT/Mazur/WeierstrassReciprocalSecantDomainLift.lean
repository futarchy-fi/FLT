/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalChartSpecialization

/-!
# Construct the reciprocal secant domain over an arbitrary algebra

An invertible ordinate difference and an invertible homogeneous output ordinate
construct both localization maps. The resulting chart retains the whole pair
and its prescribed reciprocal slope.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassIntegralAddition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (W : WeierstrassCurve R) (f : AffineProduct W →ₐ[R] B)
  (hd : IsUnit (f (verticalSecantDenominator W)))
local notation "D" => verticalSecantDenominator W
local notation "A" => RatioChart W D

/-- Lift the complete pair through its ordinate-difference localization. -/
def reciprocalSecantRatioLift : A →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom D hd

/-- The first localization retains every function on the pair. -/
theorem reciprocalSecantRatioLift_restriction :
    (reciprocalSecantRatioLift W f hd).comp (ratioRestriction W D) = f := by
  ext z
  exact IsLocalization.Away.lift_eq D hd z

variable (m : B)
  (hl : m * f (verticalSecantDenominator W) = f (secantDenominator W))

include hl in
/-- An invertible ordinate difference determines the prescribed reciprocal slope. -/
theorem reciprocalSecantRatioLift_slope :
    reciprocalSecantRatioLift W f hd (verticalSecantSlope W) = m := by
  apply hd.mul_left_inj.mp
  have h := congrArg (reciprocalSecantRatioLift W f hd)
    (ratioSlope_mul W D (secantDenominator W))
  have he (z) : reciprocalSecantRatioLift W f hd (ratioRestriction W D z) = f z :=
    DFunLike.congr_fun (reciprocalSecantRatioLift_restriction W f hd) z
  simpa only [map_mul, he, hl, verticalSecantSlope] using h

include hl in
/-- The first localization evaluates to the prescribed homogeneous output coordinates. -/
theorem reciprocalSecantRatioLift_coordinates (i : Fin 3) :
    reciprocalSecantRatioLift W f hd
        (reciprocalCoordinates W (ratioRestriction W D) (verticalSecantSlope W) i) =
      reciprocalCoordinates W f m i := by
  rw [reciprocalCoordinates_map, reciprocalSecantRatioLift_slope W f hd m hl,
    reciprocalSecantRatioLift_restriction]

variable (hy : IsUnit (reciprocalCoordinates W f m 1))

/-- Both principal opens now have a map from the given test algebra. -/
def reciprocalSecantDomainLift : additionChartRing W (reciprocalIndex false) →ₐ[R] B := by
  change ReciprocalTargetOpen W (ratioRestriction W D) (verticalSecantSlope W) →ₐ[R] B
  exact IsLocalization.Away.liftAlgHom (f := reciprocalSecantRatioLift W f hd)
    (reciprocalCoordinates W (ratioRestriction W D) (verticalSecantSlope W) 1)
    (by rw [reciprocalSecantRatioLift_coordinates W f hd m hl]; exact hy)

/-- Output normalization preserves the full intermediate ratio ring. -/
theorem reciprocalSecantDomainLift_ratio (z : A) :
    reciprocalSecantDomainLift W f hd m hl hy
        (reciprocalTargetRestriction W (ratioRestriction W D) (verticalSecantSlope W) z) =
      reciprocalSecantRatioLift W f hd z :=
  IsLocalization.Away.lift_eq
    (S := ReciprocalTargetOpen W (ratioRestriction W D) (verticalSecantSlope W)) _
    (by
      change IsUnit (reciprocalSecantRatioLift W f hd
        (reciprocalCoordinates W (ratioRestriction W D) (verticalSecantSlope W) 1))
      rw [reciprocalSecantRatioLift_coordinates W f hd m hl]
      exact hy) z

/-- The constructed reciprocal domain retains the complete affine input pair. -/
theorem reciprocalSecantDomainLift_restriction :
    (reciprocalSecantDomainLift W f hd m hl hy).comp
      (additionChartAlgRestriction W (reciprocalIndex false)) = f := by
  ext z
  change reciprocalSecantDomainLift W f hd m hl hy
    (reciprocalTargetRestriction W (ratioRestriction W D) (verticalSecantSlope W)
      (ratioRestriction W D z)) = f z
  rw [reciprocalSecantDomainLift_ratio]
  exact DFunLike.congr_fun (reciprocalSecantRatioLift_restriction W f hd) z

/-- The normalized domain still carries exactly the chosen reciprocal slope. -/
theorem reciprocalSecantDomainLift_slope :
    reciprocalSecantDomainLift W f hd m hl hy (reciprocalChartSlope W false) = m := by
  change reciprocalSecantDomainLift W f hd m hl hy
    (reciprocalTargetRestriction W (ratioRestriction W D) (verticalSecantSlope W)
      (verticalSecantSlope W)) = m
  rw [reciprocalSecantDomainLift_ratio, reciprocalSecantRatioLift_slope W f hd m hl]

/-- Any normalizing inverse agrees with the inverse in the constructed output chart. -/
theorem reciprocalSecantDomainLift_inverse (q : B)
    (hq : q * reciprocalCoordinates W f m 1 = 1) :
    reciprocalSecantDomainLift W f hd m hl hy (reciprocalChartInverse W false) = q := by
  apply hy.mul_left_inj.mp
  have h := congrArg (reciprocalSecantDomainLift W f hd m hl hy)
    (reciprocalTargetInverse_mul W (ratioRestriction W D) (verticalSecantSlope W))
  simp only [map_mul, map_one, reciprocalSecantDomainLift_ratio,
    reciprocalSecantRatioLift_coordinates W f hd m hl] at h
  exact h.trans hq.symm

end FLT.Mazur.WeierstrassIntegralChart
