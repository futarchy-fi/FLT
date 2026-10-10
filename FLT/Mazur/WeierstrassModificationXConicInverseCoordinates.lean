/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicFirstParameter

/-!
# Coordinates of the inverse conic parameterization

The localized polynomial line carries the actual solution t=a*z/d,
v=a*c*z²/d, where d=1-c*z². The inverse map to the first tangent open is
constructed from this solution, with no conic equation assumed as input.
-/

@[expose] public noncomputable section

open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)

/-- The polynomial coordinate on the parameter open. -/
def conicParameterZ : ConicParameterOpen c := algebraMap R[X] _ X
/-- The inverted polynomial denominator on the parameter open. -/
def conicParameterInv : ConicParameterOpen c :=
  IsLocalization.Away.invSelf (conicParameterPolynomial c)
local notation "P" => ConicParameterOpen c
local notation "z" => conicParameterZ c
local notation "i" => conicParameterInv c
local notation "A" => algebraMap R P a
local notation "C" => algebraMap R P c

/-- The displayed denominator and its chosen inverse multiply to one. -/
theorem conicParameter_mul_inv : (1 - C * z ^ 2) * i = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := P) (conicParameterPolynomial c)
  have hc : algebraMap R[X] P (Polynomial.C c) = C :=
    (IsScalarTower.algebraMap_apply R R[X] P c).symm
  simpa only [conicParameterPolynomial, map_sub, map_one, map_mul, map_pow,
    hc, conicParameterZ, conicParameterInv] using h

/-- The incidence coordinate of the inverse parameterization. -/
def conicInverseT : P := A * z * i
/-- The slope coordinate of the inverse parameterization. -/
def conicInverseV : P := A * C * z ^ 2 * i

/-- The opposite tangent factor is exactly a times the inverted denominator. -/
theorem conicInverseV_add : conicInverseV a c + A = A * i := by
  have h := conicParameter_mul_inv c
  dsimp [conicInverseV]
  calc A * C * z ^ 2 * i + A = A * C * z ^ 2 * i + A * ((1 - C * z ^ 2) * i) :=
      by rw [h, mul_one]
    _ = A * i := by ring

/-- The proposed inverse coordinates satisfy the original conic equation. -/
theorem conicInverse_relation :
    conicInverseV a c * (conicInverseV a c + A) - C * conicInverseT a c ^ 2 = 0 := by
  rw [conicInverseV_add]
  dsimp [conicInverseV, conicInverseT]
  ring

/-- The inverse denominator is a unit. -/
theorem conicParameterInv_isUnit : IsUnit i :=
  isUnit_of_mul_isUnit_right (by rw [conicParameter_mul_inv]; exact isUnit_one)

/-- The original tangent factor is a unit when a is a unit. -/
theorem conicInverseV_add_isUnit (ha : IsUnit a) : IsUnit (conicInverseV a c + A) := by
  rw [conicInverseV_add]
  exact (ha.map (algebraMap R P)).mul (conicParameterInv_isUnit c)

/-- The actual map from the conic to its parameter line. -/
def conicToParameter : ConicCoordinate a c →ₐ[R] P :=
  conicEvaluation a c (conicInverseT a c) (conicInverseV a c) (conicInverse_relation a c)

/-- The inverse map preserves the incidence formula. -/
@[simp] theorem conicToParameter_t :
    conicToParameter a c (conicT a c) = conicInverseT a c := conicEvaluation_t _ _ _ _ _
/-- The inverse map preserves the slope formula. -/
@[simp] theorem conicToParameter_v :
    conicToParameter a c (conicV a c) = conicInverseV a c := conicEvaluation_v _ _ _ _ _

/-- The conic map extends to the actual first tangent neighborhood. -/
def conicFirstToParameter (ha : IsUnit a) : ConicFirstOpen a c →ₐ[R] P :=
  IsLocalization.Away.liftAlgHom (f := conicToParameter a c)
    (conicV a c + algebraMap R _ a) (by
      simpa only [map_add, conicToParameter_v, AlgHom.commutes] using
        conicInverseV_add_isUnit a c ha)

/-- The localized inverse restricts to the proved conic evaluation. -/
theorem conicFirstToParameter_base (ha : IsUnit a) (q : ConicCoordinate a c) :
    conicFirstToParameter a c ha (algebraMap (ConicCoordinate a c) _ q) =
    conicToParameter a c q := by
  rw [conicFirstToParameter, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
