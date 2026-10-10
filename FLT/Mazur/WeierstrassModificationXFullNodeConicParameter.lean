/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeBranchCoordinates
public import FLT.Mazur.WeierstrassModificationXConicInverseCoordinates

/-!
# The first localized node branch is the original conic parameter open

The branch denominator is exactly 1-c*z². Its comparison preserves the node
parameter and the actual inverse denominator, hence both rational coordinates.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (a c : K) (ha : IsUnit a)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "L" => FullNodeOpen a c
local notation "B" => Localization.Away (PolygonNodeEqualizer.first s)
local notation "P" => ConicParameterOpen c

include ha in
/-- The actual first branch ring is localized at the original conic denominator. -/
theorem fullNodeFirstBranch_isLocalization :
    IsLocalization.Away (conicParameterPolynomial c) B := by
  rw [show conicParameterPolynomial c = PolygonNodeEqualizer.first s from
    (fullNodeNormalizedDenominator_first a c ha).symm]
  infer_instance

/-- The first branch's full coordinate ring is the original rational parameter ring. -/
def fullNodeConicParameterEquiv : B ≃ₐ[K] P := by
  let _ := fullNodeFirstBranch_isLocalization a c ha
  exact AlgEquiv.restrictScalars K
    (IsLocalization.algEquiv (Submonoid.powers (conicParameterPolynomial c)) B P)

/-- The parameter comparison preserves every polynomial. -/
theorem fullNodeConicParameterEquiv_base (p : K[X]) :
    fullNodeConicParameterEquiv a c ha (algebraMap K[X] B p) = algebraMap K[X] P p := by
  let _ := fullNodeFirstBranch_isLocalization a c ha
  exact (IsLocalization.algEquiv (Submonoid.powers (conicParameterPolynomial c)) B P).commutes p

/-- The first restriction preserves the original coefficient field. -/
theorem fullNodeFirstRestriction_constant (k : K) :
    fullNodeFirstRestriction a c ha (algebraMap K L k) = algebraMap K B k := by
  rw [IsScalarTower.algebraMap_apply K (NodalFiber.Coordinate (0 : K)) L,
    fullNodeFirstRestriction_base, AlgEquiv.commutes, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply K K[X] B]

/-- The first branch restriction as a map over the original field. -/
def fullNodeFirstRestrictionAlg : L →ₐ[K] B where
  __ := fullNodeFirstRestriction a c ha
  commutes' := fullNodeFirstRestriction_constant a c ha

/-- The original node restricted to its original conic parameter open. -/
def fullNodeConicRestriction : L →ₐ[K] P :=
  (fullNodeConicParameterEquiv a c ha).toAlgHom.comp (fullNodeFirstRestrictionAlg a c ha)

/-- The first original node coordinate is the unchanged conic parameter. -/
@[simp] theorem fullNodeConicRestriction_p :
    fullNodeConicRestriction a c ha (fullNodeP a c) = conicParameterZ c := by
  change fullNodeConicParameterEquiv a c ha
    (fullNodeFirstRestriction a c ha (fullNodeP a c)) = _
  rw [fullNodeFirstRestriction_p, fullNodeConicParameterEquiv_base]
  rfl

/-- The other node coordinate vanishes on this original conic branch. -/
@[simp] theorem fullNodeConicRestriction_q :
    fullNodeConicRestriction a c ha (fullNodeQ a c) = 0 := by
  change fullNodeConicParameterEquiv a c ha
    (fullNodeFirstRestriction a c ha (fullNodeQ a c)) = _
  rw [fullNodeFirstRestriction_q, map_zero]

/-- The actual inverse denominator agrees with the original conic inverse denominator. -/
theorem fullNodeConicRestriction_inv :
    fullNodeConicRestriction a c ha (fullNodeInv a c) = conicParameterInv c := by
  have h := congrArg (fullNodeConicRestriction a c ha) (fullNode_mul_inv a c)
  simp only [map_mul, map_sub, map_one, map_pow, AlgHom.commutes,
    fullNodeConicRestriction_p] at h
  exact (IsUnit.of_mul_eq_one _ (conicParameter_mul_inv c)).mul_left_cancel
    (h.trans (conicParameter_mul_inv c).symm)

/-- Restriction retains the exact original rational incidence formula. -/
theorem fullNodeConicRestriction_inverseT :
    fullNodeConicRestriction a c ha (fullNodeInverseT a c) = conicInverseT a c := by
  simp only [fullNodeInverseT, map_mul, AlgHom.commutes, fullNodeConicRestriction_p,
    fullNodeConicRestriction_inv, conicInverseT]

/-- Restriction retains the exact original rational slope formula. -/
theorem fullNodeConicRestriction_inverseV :
    fullNodeConicRestriction a c ha (fullNodeInverseV a c) = conicInverseV a c := by
  simp only [fullNodeInverseV, map_add, map_mul, map_pow, AlgHom.commutes,
    fullNodeConicRestriction_p, fullNodeConicRestriction_q, fullNodeConicRestriction_inv,
    zero_add, conicInverseV]

end FLT.Mazur.WeierstrassModificationX
