/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleConic
public import FLT.Mazur.WeierstrassModificationXConicFirstParameter
public import FLT.Mazur.SuccessiveIncidenceAlgebra

/-!
# The node parameter on the actual successive middle attachment

On v+a₁ invertible the whole middle chart retains z=t/(v+a₁) and u.
They satisfy z*u=0, and 1-c*z² is a unit. These identities hold in the
original open algebra, with no reduction or component quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c

/-- The first ordered tangent neighborhood in the full middle chart. -/
abbrev MiddleFirstOpen :=
  Localization.Away (coord W 0 0 0 0 c 1 + algebraMap R A W.a₁)
local notation "O" => MiddleFirstOpen W c
local notation "V" => algebraMap A O (coord W 0 0 0 0 c 1)
local notation "T" => algebraMap A O (coord W 0 0 0 0 c 0)
local notation "U" => algebraMap A O (coord W 0 0 0 0 c 2)
local notation "d" => coord W 0 0 0 0 c 1 + algebraMap R A W.a₁

/-- The original rational incidence parameter on the full attachment neighborhood. -/
def middleFirstParameter : O := T * IsLocalization.Away.invSelf d

/-- The rational parameter recovers the original incidence coordinate. -/
theorem middleFirstParameter_mul :
    middleFirstParameter W c * algebraMap A O d = T := by
  rw [middleFirstParameter, mul_assoc, mul_comm (IsLocalization.Away.invSelf d),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The original node equation holds on the entire attachment neighborhood. -/
theorem middleFirstParameter_node : middleFirstParameter W c * U = 0 := by
  have h : T * U = 0 := by rw [← map_mul, incidence, map_zero, map_zero]
  calc middleFirstParameter W c * U =
      (T * U) * IsLocalization.Away.invSelf d := by unfold middleFirstParameter; ring
    _ = 0 := by rw [h, zero_mul]

/-- The conic parameter chart maps into the whole middle attachment by its section. -/
def conicFirstToMiddleFirst : ConicFirstOpen W.a₁ c →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (conicV W.a₁ c + algebraMap R _ W.a₁)
    (f := (IsScalarTower.toAlgHom R A O).comp (middleConicSection W c h2)) (by
      change IsUnit (algebraMap A O (middleConicSection W c h2 _))
      rw [map_add, middleConicSection_v, AlgHom.commutes]
      exact IsLocalization.Away.algebraMap_isUnit (S := O) d)

/-- The conic section is unchanged on its original functions. -/
@[simp] theorem conicFirstToMiddleFirst_base (q : ConicCoordinate W.a₁ c) :
    conicFirstToMiddleFirst W c h2 (algebraMap (ConicCoordinate W.a₁ c) _ q) =
      algebraMap A O (middleConicSection W c h2 q) := by
  rw [conicFirstToMiddleFirst, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The conic rational parameter is the actual parameter of the entire attachment. -/
@[simp] theorem conicFirstToMiddleFirst_parameter :
    conicFirstToMiddleFirst W c h2 (conicFirstParameter W.a₁ c) =
      middleFirstParameter W c := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := O) d).mul_right_cancel
  rw [middleFirstParameter_mul]
  have h := congrArg (conicFirstToMiddleFirst W c h2) (conicFirstParameter_mul W.a₁ c)
  simpa only [map_mul, conicFirstToMiddleFirst_base, map_add,
    middleConicSection_v, middleConicSection_t, AlgHom.commutes] using h

include h2 in
/-- The node-parameter denominator is invertible in the full original neighborhood. -/
theorem middleFirstParameter_denominator_isUnit (ha : IsUnit W.a₁) :
    IsUnit (1 - algebraMap R O c * middleFirstParameter W c ^ 2) := by
  have h := (conicFirstParameter_denominator_isUnit W.a₁ c ha).map
    (conicFirstToMiddleFirst W c h2)
  simpa only [map_sub, map_one, map_mul, map_pow, AlgHom.commutes,
    conicFirstToMiddleFirst_parameter] using h

/-- The actual node algebra maps to the entire attachment neighborhood. -/
def middleNodeToFirstBase : SuccessiveIncidence.Coordinate (0 : R) →ₐ[R] O :=
  SuccessiveIncidence.evaluation 0 (middleFirstParameter W c) U (by
    rw [map_zero]; exact middleFirstParameter_node W c)

end FLT.Mazur.WeierstrassSuccessiveX
