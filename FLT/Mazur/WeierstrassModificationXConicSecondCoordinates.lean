/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicSecondOpen

/-!
# Original coordinates on the second rational conic chart

The second parameter is exactly t/v. Its denominator satisfies
(1-c*z²)*v=-a. The parameter equivalence retains the original t and v,
including the translation back from the recentered conic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "O" => ConicSecondOpen a c
local notation "C₀" => ConicCoordinate a c
local notation "C₁" => ConicCoordinate (-a) c
local notation "T" => algebraMap C₀ O (conicT a c)
local notation "V" => algebraMap C₀ O (conicV a c)
local notation "A" => algebraMap R O a

/-- The actual second parameter is t divided by the original v. -/
def conicSecondParameter : O := T * IsLocalization.Away.invSelf (conicV a c)

/-- Multiplying the second parameter by its original denominator recovers t. -/
theorem conicSecondParameter_mul : conicSecondParameter a c * V = T := by
  rw [conicSecondParameter]
  calc (T * IsLocalization.Away.invSelf (conicV a c)) * V =
      T * (V * IsLocalization.Away.invSelf (conicV a c)) := by ring
    _ = T := by rw [IsLocalization.Away.mul_invSelf, mul_one]

/-- Returning from recentered coordinates preserves t. -/
theorem conicFirstToSecond_t : conicFirstToSecond a c
    (algebraMap C₁ (ConicFirstOpen (-a) c) (conicT (-a) c)) = T := by
  rw [conicFirstToSecond_base]
  change algebraMap C₀ O (conicTangentBackward a c (conicT (-a) c)) = T
  rw [conicTangentBackward_t]

/-- Returning from recentered coordinates sends w to v+a. -/
theorem conicFirstToSecond_v : conicFirstToSecond a c
    (algebraMap C₁ (ConicFirstOpen (-a) c) (conicV (-a) c)) = V + A := by
  rw [conicFirstToSecond_base]
  change algebraMap C₀ O (conicTangentBackward a c (conicV (-a) c)) = V + A
  rw [conicTangentBackward_v, map_add, ← IsScalarTower.algebraMap_apply R C₀ O]

/-- Returning from recentered coordinates identifies the inverted factors exactly. -/
theorem conicFirstToSecond_denominator : conicFirstToSecond a c
    (algebraMap C₁ (ConicFirstOpen (-a) c) (conicV (-a) c + algebraMap R C₁ (-a))) =
      V := by
  rw [map_add, ← IsScalarTower.algebraMap_apply R C₁ (ConicFirstOpen (-a) c),
    map_add, conicFirstToSecond_v, AlgHom.commutes, map_neg, add_neg_cancel_right]

/-- The transported parameter is the actual t/v, not an unrelated rational function. -/
theorem conicFirstToSecond_parameter :
    conicFirstToSecond a c (conicFirstParameter (-a) c) = conicSecondParameter a c := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := O) (conicV a c)).mul_right_cancel
  have h := congrArg (conicFirstToSecond a c) (conicFirstParameter_mul (-a) c)
  simpa only [map_mul, conicFirstToSecond_denominator, conicFirstToSecond_t,
    conicSecondParameter_mul] using h

/-- The second parameter retains the sign of the original tangent difference. -/
theorem conicSecondParameter_denominator_mul :
    (1 - algebraMap R O c * conicSecondParameter a c ^ 2) * V = -A := by
  have h := congrArg (conicFirstToSecond a c)
    (conicFirstParameter_denominator_mul (-a) c)
  rw [map_mul, conicFirstToSecond_denominator] at h
  simpa only [map_mul, map_sub, map_one, map_pow, AlgHom.commutes, map_neg,
    conicFirstToSecond_parameter] using h

/-- The second equivalence sends the polynomial variable to the original ratio t/v. -/
theorem conicSecondParameterEquiv_z (ha : IsUnit a) :
    conicSecondParameterEquiv a c ha (conicParameterZ c) = conicSecondParameter a c := by
  change conicFirstToSecond a c
    (conicParameterToFirst (-a) c ha.neg (conicParameterZ c)) = _
  rw [conicParameterToFirst_z, conicFirstToSecond_parameter]

/-- The inverse second chart expresses the original incidence coordinate. -/
theorem conicSecondParameterEquiv_symm_t (ha : IsUnit a) :
    (conicSecondParameterEquiv a c ha).symm T = conicInverseT (-a) c := by
  apply (conicSecondParameterEquiv a c ha).injective
  rw [AlgEquiv.apply_symm_apply]
  change T = conicFirstToSecond a c (conicParameterToFirst (-a) c ha.neg _)
  rw [conicParameterToFirst_inverseT, conicFirstToSecond_t]

/-- The inverse second chart expresses the original slope, retaining its translation. -/
theorem conicSecondParameterEquiv_symm_v (ha : IsUnit a) :
    (conicSecondParameterEquiv a c ha).symm V =
      conicInverseV (-a) c - algebraMap R (ConicParameterOpen c) a := by
  apply (conicSecondParameterEquiv a c ha).injective
  rw [AlgEquiv.apply_symm_apply, map_sub, AlgEquiv.commutes]
  change V = conicFirstToSecond a c (conicParameterToFirst (-a) c ha.neg _) - A
  rw [conicParameterToFirst_inverseV, conicFirstToSecond_v, add_sub_cancel_right]

end FLT.Mazur.WeierstrassModificationX
