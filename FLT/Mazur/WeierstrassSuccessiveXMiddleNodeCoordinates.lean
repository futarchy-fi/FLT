/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SuccessiveIncidenceAlgebra
public import FLT.Mazur.WeierstrassModificationXConicInverseCoordinates

/-!
# Inverse coordinates on the localized attachment node

The node z*u=0 is localized only at 1-c*z². Its original two generators
supply t=a*z/(1-c*z²), v=a*c*z²/(1-c*z²), and the retained u.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "B" => SuccessiveIncidence.Coordinate (0 : R)

/-- The exact denominator of the attachment-node parameter chart. -/
def middleNodeDenominator : B :=
  1 - algebraMap R B c * SuccessiveIncidence.t (0 : R) ^ 2

/-- The actual principal open of the standard incidence node. -/
abbrev MiddleNodeOpen := Localization.Away (middleNodeDenominator c)

/-- The retained incidence generator on the localized node. -/
def middleNodeZ : MiddleNodeOpen c := algebraMap B _ (SuccessiveIncidence.t (0 : R))

/-- The retained horizontal generator on the localized node. -/
def middleNodeU : MiddleNodeOpen c := algebraMap B _ (SuccessiveIncidence.u (0 : R))
local notation "N" => MiddleNodeOpen c

/-- The localized coordinates satisfy exactly the original node equation. -/
theorem middleNode_relation : middleNodeZ c * middleNodeU c = 0 := by
  rw [middleNodeZ, middleNodeU, ← map_mul, SuccessiveIncidence.incidence,
    map_zero, map_zero]

/-- The parameter-line denominator is invertible on the actual localized node. -/
theorem middleNode_denominator_isUnit :
    IsUnit (1 - algebraMap R N c * middleNodeZ c ^ 2) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := N) (middleNodeDenominator c)
  simpa only [middleNodeDenominator, map_sub, map_one, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply R B N, middleNodeZ] using h

/-- The original conic parameter line maps into this full node neighborhood. -/
def conicParameterToMiddleNode : ConicParameterOpen c →ₐ[R] N :=
  IsLocalization.Away.liftAlgHom (conicParameterPolynomial c)
    (f := aeval (middleNodeZ c)) (by
      simpa only [conicParameterPolynomial, map_sub, map_one, map_mul, map_pow,
        aeval_C, aeval_X] using middleNode_denominator_isUnit c)

/-- The polynomial parameter is the actual localized node generator. -/
@[simp] theorem conicParameterToMiddleNode_z :
    conicParameterToMiddleNode c (conicParameterZ c) = middleNodeZ c := by
  rw [conicParameterZ, conicParameterToMiddleNode,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact aeval_X _

/-- The original conic incidence coordinate in the full node chart. -/
def middleNodeT : N := conicParameterToMiddleNode c (conicInverseT a c)

/-- The original conic slope coordinate in the full node chart. -/
def middleNodeV : N := conicParameterToMiddleNode c (conicInverseV a c)

/-- These coordinates satisfy the whole retained conic equation. -/
theorem middleNode_conic :
    middleNodeV a c * (middleNodeV a c + algebraMap R N a) -
      algebraMap R N c * middleNodeT a c ^ 2 = 0 := by
  have h := congrArg (conicParameterToMiddleNode c) (conicInverse_relation a c)
  simpa only [map_sub, map_mul, map_add, map_pow, map_zero, AlgHom.commutes,
    middleNodeT, middleNodeV] using h

/-- The original t coordinate still annihilates the full horizontal branch. -/
theorem middleNode_incidence : middleNodeT a c * middleNodeU c = 0 := by
  simp only [middleNodeT, conicInverseT, map_mul, AlgHom.commutes,
    conicParameterToMiddleNode_z]
  calc algebraMap R N a * middleNodeZ c *
      conicParameterToMiddleNode c (conicParameterInv c) * middleNodeU c =
      (algebraMap R N a * conicParameterToMiddleNode c (conicParameterInv c)) *
        (middleNodeZ c * middleNodeU c) := by ring
    _ = 0 := by rw [middleNode_relation, mul_zero]

/-- The original opposite tangent factor is a unit on the full node open. -/
theorem middleNode_v_add_isUnit (ha : IsUnit a) :
    IsUnit (middleNodeV a c + algebraMap R N a) := by
  simpa only [map_add, AlgHom.commutes, middleNodeV] using
    (conicInverseV_add_isUnit a c ha).map (conicParameterToMiddleNode c)

/-- The original incidence formula retains the rational parameter. -/
theorem middleNode_parameter_mul :
    middleNodeZ c * (middleNodeV a c + algebraMap R N a) = middleNodeT a c := by
  have h : conicParameterZ c * (conicInverseV a c + algebraMap R _ a) =
      conicInverseT a c := by rw [conicInverseV_add, conicInverseT]; ring
  simpa only [map_mul, map_add, AlgHom.commutes, conicParameterToMiddleNode_z,
    middleNodeV, middleNodeT] using congrArg (conicParameterToMiddleNode c) h

end FLT.Mazur.WeierstrassSuccessiveX
