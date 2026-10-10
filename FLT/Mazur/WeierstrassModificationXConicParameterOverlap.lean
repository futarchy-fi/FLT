/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicSecondCoordinates

/-!
# The actual overlap of the ordered conic parameter charts

Invert the second tangent factor on the full first tangent neighborhood.
The two original ratios satisfy c*z₁*z₂=1 on this overlap. In particular
when c=0 the overlap is empty; neither full chart is discarded.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R)
local notation "C₀" => ConicCoordinate a c
local notation "O₁" => ConicFirstOpen a c
local notation "O₂" => ConicSecondOpen a c

/-- The original first tangent open with the second tangent factor inverted. -/
abbrev ConicParameterOverlap := Localization.Away (algebraMap C₀ O₁ (conicV a c))
local notation "B" => ConicParameterOverlap a c
local notation "g" => IsScalarTower.toAlgHom R C₀ B
local notation "U" => g (conicV a c + algebraMap R C₀ a)
local notation "V" => g (conicV a c)
local notation "T" => g (conicT a c)

/-- Both original tangent factors are units on the actual overlap. -/
theorem conicOverlap_first_isUnit : IsUnit U := by
  change IsUnit (algebraMap O₁ B (algebraMap C₀ O₁ _))
  exact (IsLocalization.Away.algebraMap_isUnit (S := O₁)
    (conicV a c + algebraMap R C₀ a)).map (algebraMap O₁ B)

/-- The second original tangent factor is inverted on the actual overlap. -/
theorem conicOverlap_second_isUnit : IsUnit V := by
  change IsUnit (algebraMap O₁ B (algebraMap C₀ O₁ (conicV a c)))
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The second full tangent neighborhood maps into the overlap algebra. -/
def conicSecondToOverlap : O₂ →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := g) (conicV a c)
    (conicOverlap_second_isUnit a c)

/-- The second localization map retains every original conic function. -/
theorem conicSecondToOverlap_base (q : C₀) :
    conicSecondToOverlap a c (algebraMap C₀ O₂ q) = g q := by
  rw [conicSecondToOverlap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The first rational parameter viewed on the actual overlap. -/
def conicOverlapFirstParameter : B := algebraMap O₁ B (conicFirstParameter a c)

/-- The second rational parameter viewed on the same actual overlap. -/
def conicOverlapSecondParameter : B := conicSecondToOverlap a c (conicSecondParameter a c)
local notation "z₁" => conicOverlapFirstParameter a c
local notation "z₂" => conicOverlapSecondParameter a c

/-- The first overlap parameter keeps its original denominator v+a. -/
theorem conicOverlapFirstParameter_mul : z₁ * U = T := by
  dsimp only [conicOverlapFirstParameter]
  change algebraMap O₁ B _ * algebraMap O₁ B _ = algebraMap O₁ B _
  rw [← map_mul]
  exact congrArg (algebraMap O₁ B) (conicFirstParameter_mul a c)

/-- The second overlap parameter keeps its original denominator v. -/
theorem conicOverlapSecondParameter_mul : z₂ * V = T := by
  have h := congrArg (conicSecondToOverlap a c) (conicSecondParameter_mul a c)
  simpa only [map_mul, conicSecondToOverlap_base, conicOverlapSecondParameter] using h

/-- The actual rational overlap transition is c*z₁*z₂=1, with both tangent orders fixed. -/
theorem conicOverlap_parameter_relation : algebraMap R B c * z₁ * z₂ = 1 := by
  have hr : V * U = algebraMap R B c * T ^ 2 := by
    have h := congrArg g (conic_relation a c)
    simpa only [map_sub, map_mul, map_pow, map_zero, AlgHom.commutes,
      sub_eq_zero] using h
  apply ((conicOverlap_first_isUnit a c).mul
    (conicOverlap_second_isUnit a c)).mul_right_cancel
  calc (algebraMap R B c * z₁ * z₂) * (U * V) =
      algebraMap R B c * (z₁ * U) * (z₂ * V) := by ring
    _ = algebraMap R B c * T ^ 2 := by
      rw [conicOverlapFirstParameter_mul, conicOverlapSecondParameter_mul, pow_two, mul_assoc]
    _ = 1 * (U * V) := by rw [← hr]; ring

/-- The divided conic constant is invertible on the actual parameter overlap. -/
theorem conicOverlap_constant_isUnit : IsUnit (algebraMap R B c) := by
  have h : IsUnit (algebraMap R B c * z₁ * z₂) := by
    rw [conicOverlap_parameter_relation]
    exact isUnit_one
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)

/-- The first parameter itself is invertible on the overlap. -/
theorem conicOverlap_firstParameter_isUnit : IsUnit z₁ := by
  have h : IsUnit (algebraMap R B c * z₁ * z₂) := by
    rw [conicOverlap_parameter_relation]
    exact isUnit_one
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)

/-- The second parameter itself is invertible on the overlap. -/
theorem conicOverlap_secondParameter_isUnit : IsUnit z₂ := by
  have h : IsUnit (algebraMap R B c * z₁ * z₂) := by
    rw [conicOverlap_parameter_relation]
    exact isUnit_one
  exact isUnit_of_mul_isUnit_right h

/-- With zero divided constant the overlap ring is trivial. -/
theorem conicOverlap_zero_subsingleton : Subsingleton (ConicParameterOverlap a (0 : R)) := by
  apply subsingleton_of_zero_eq_one
  have h := conicOverlap_parameter_relation a (0 : R)
  simpa only [map_zero, zero_mul] using h

end FLT.Mazur.WeierstrassModificationX
