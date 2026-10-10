/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicParameterOverlap

/-!
# Both ordered parameters on the full incidence boundary

For unit divided constant, inverting incidence inverts both tangent factors.
The original slope v/t equals c*z₁ and is inverse to z₂ on this entire open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R)
local notation "C₀" => ConicCoordinate a c
/-- The entire original incidence boundary of the conic. -/
abbrev ConicIncidenceOpen := Localization.Away (conicT a c)
local notation "B" => ConicIncidenceOpen a c
local notation "U" => algebraMap C₀ B (conicV a c + algebraMap R C₀ a)
local notation "V" => algebraMap C₀ B (conicV a c)
local notation "T" => algebraMap C₀ B (conicT a c)
local notation "C" => algebraMap R B c

/-- The original conic equation on the entire incidence localization. -/
theorem conicIncidence_relation : V * U = C * T ^ 2 := by
  have h := congrArg (algebraMap C₀ B) (conic_relation a c)
  simpa only [map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply R C₀ B, sub_eq_zero] using h

/-- The two original tangent factors are units when the divided constant is a unit. -/
theorem conicIncidence_tangent_units (hc : IsUnit c) : IsUnit V ∧ IsUnit U := by
  have h : IsUnit (V * U) := by
    rw [conicIncidence_relation]
    exact (hc.map (algebraMap R B)).mul
      ((IsLocalization.Away.algebraMap_isUnit (S := B) (conicT a c)).pow 2)
  exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩

/-- Restriction of the full first tangent neighborhood to the incidence boundary. -/
def conicFirstToIncidence (hc : IsUnit c) : ConicFirstOpen a c →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := Algebra.algHom R C₀ B)
    (conicV a c + algebraMap R C₀ a) (conicIncidence_tangent_units a c hc).2

/-- Restriction of the full second tangent neighborhood to the incidence boundary. -/
def conicSecondToIncidence (hc : IsUnit c) : ConicSecondOpen a c →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := Algebra.algHom R C₀ B)
    (conicV a c) (conicIncidence_tangent_units a c hc).1

/-- The first restriction preserves every original conic function. -/
theorem conicFirstToIncidence_base (hc : IsUnit c) (q : C₀) :
    conicFirstToIncidence a c hc (algebraMap C₀ (ConicFirstOpen a c) q) =
      algebraMap C₀ B q := by
  rw [conicFirstToIncidence, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The second restriction preserves every original conic function. -/
theorem conicSecondToIncidence_base (hc : IsUnit c) (q : C₀) :
    conicSecondToIncidence a c hc (algebraMap C₀ (ConicSecondOpen a c) q) =
      algebraMap C₀ B q := by
  rw [conicSecondToIncidence, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The first ordered parameter on the entire incidence boundary. -/
def conicIncidenceFirstParameter (hc : IsUnit c) : B :=
  conicFirstToIncidence a c hc (conicFirstParameter a c)

/-- The second ordered parameter on the entire incidence boundary. -/
def conicIncidenceSecondParameter (hc : IsUnit c) : B :=
  conicSecondToIncidence a c hc (conicSecondParameter a c)
local notation "z₁" => conicIncidenceFirstParameter a c
local notation "z₂" => conicIncidenceSecondParameter a c

/-- The first parameter has its original denominator v+a. -/
theorem conicIncidenceFirstParameter_mul (hc : IsUnit c) : z₁ hc * U = T := by
  have h := congrArg (conicFirstToIncidence a c hc) (conicFirstParameter_mul a c)
  simpa only [map_mul, conicFirstToIncidence_base, conicIncidenceFirstParameter] using h

/-- The second parameter has its original denominator v. -/
theorem conicIncidenceSecondParameter_mul (hc : IsUnit c) : z₂ hc * V = T := by
  have h := congrArg (conicSecondToIncidence a c hc) (conicSecondParameter_mul a c)
  simpa only [map_mul, conicSecondToIncidence_base, conicIncidenceSecondParameter] using h

/-- The original oriented slope divided by incidence. -/
def conicIncidenceSlope : B := IsLocalization.Away.invSelf (conicT a c) * V
local notation "y" => conicIncidenceSlope a c

/-- Multiplication by incidence recovers the original slope. -/
theorem conicIncidenceSlope_mul : y * T = V := by
  rw [conicIncidenceSlope]
  calc (IsLocalization.Away.invSelf (conicT a c) * V) * T =
      V * (T * IsLocalization.Away.invSelf (conicT a c)) := by ring
    _ = V := by rw [IsLocalization.Away.mul_invSelf, mul_one]

/-- The Laurent coordinate is exactly c times the first ordered parameter. -/
theorem conicIncidenceSlope_first (hc : IsUnit c) : y = C * z₁ hc := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := B) (conicT a c)).mul_right_cancel
  rw [conicIncidenceSlope_mul]
  apply (conicIncidence_tangent_units a c hc).2.mul_right_cancel
  calc V * U = C * T ^ 2 := conicIncidence_relation a c
    _ = (C * z₁ hc * T) * U := by
      rw [← conicIncidenceFirstParameter_mul a c hc]
      ring

/-- The Laurent coordinate is inverse to the second ordered parameter. -/
theorem conicIncidenceSlope_second (hc : IsUnit c) : y * z₂ hc = 1 := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := B) (conicT a c)).mul_right_cancel
  calc (y * z₂ hc) * T = z₂ hc * (y * T) := by ring
    _ = T := by rw [conicIncidenceSlope_mul, conicIncidenceSecondParameter_mul]
    _ = 1 * T := (one_mul _).symm

/-- The exact ordered reciprocal relation holds on the entire incidence boundary. -/
theorem conicIncidence_parameter_relation (hc : IsUnit c) : C * z₁ hc * z₂ hc = 1 := by
  rw [← conicIncidenceSlope_first, conicIncidenceSlope_second]

end FLT.Mazur.WeierstrassModificationX
