/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedBranchParameters

/-!
# Factoring maps on the full middle node through its conic branch

A vanishing horizontal coordinate gives a factorization through the original
conic parameter ring. Inverting the recentered slope forces that vanishing,
which is the algebraic condition on the intersection of the two node opens.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (c : K)
local notation "N" => MiddleNodeOpen c
local notation "P" => ConicParameterOpen c

/-- The original slope annihilates the horizontal coordinate on the entire node. -/
theorem middleNode_slope_mul_horizontal (a : K) :
    middleNodeV a c * middleNodeU c = 0 := by
  simp only [middleNodeV, conicInverseV, map_mul, map_pow, AlgHom.commutes,
    conicParameterToMiddleNode_z]
  calc
    algebraMap K N a * algebraMap K N c * middleNodeZ c ^ 2 *
        conicParameterToMiddleNode c (conicParameterInv c) * middleNodeU c =
      (algebraMap K N a * algebraMap K N c * middleNodeZ c *
        conicParameterToMiddleNode c (conicParameterInv c)) *
          (middleNodeZ c * middleNodeU c) := by ring
    _ = 0 := by rw [middleNode_relation, mul_zero]

/-- A unit slope on any test algebra kills the actual horizontal coordinate. -/
theorem middleNode_horizontal_eq_zero_of_slope_isUnit {S : Type*} [CommRing S]
    (f : N →+* S) (a : K) (hv : IsUnit (f (middleNodeV a c))) :
    f (middleNodeU c) = 0 := by
  apply hv.mul_left_cancel
  rw [mul_zero, ← map_mul, middleNode_slope_mul_horizontal, map_zero]

/-- Every algebra map killing the horizontal coordinate factors through conic restriction. -/
theorem middleNode_conicFactor {S : Type*} [CommRing S] [Algebra K S]
    (f : N →ₐ[K] S) (hu : f (middleNodeU c) = 0) :
    (f.comp (conicParameterToMiddleNode c)).comp (middleLocalizedConicRestriction c) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middleNodeDenominator c))
  apply SuccessiveIncidence.hom_ext
  · change f (conicParameterToMiddleNode c
      (middleLocalizedConicRestriction c (middleNodeZ c))) = f (middleNodeZ c)
    rw [middleLocalizedConicRestriction_z, conicParameterToMiddleNode_z]
  · change f (conicParameterToMiddleNode c
      (middleLocalizedConicRestriction c (middleNodeU c))) = f (middleNodeU c)
    rw [middleLocalizedConicRestriction_u, map_zero, map_zero, hu]

/-- The same factorization works for test rings without a specified coefficient algebra. -/
theorem middleNode_conicFactor_ringHom {S : Type*} [CommRing S]
    (f : N →+* S) (hu : f (middleNodeU c) = 0) :
    (f.comp (conicParameterToMiddleNode c).toRingHom).comp
        (middleLocalizedConicRestriction c).toRingHom = f := by
  let _ : Algebra K S := (f.comp (algebraMap K N)).toAlgebra
  let F : N →ₐ[K] S := ⟨f, fun _ => rfl⟩
  exact congrArg AlgHom.toRingHom (middleNode_conicFactor c F hu)

/-- Unit slope supplies the full conic factorization on a node intersection. -/
theorem middleNode_conicFactor_of_slope_isUnit {S : Type*} [CommRing S]
    (f : N →+* S) (a : K) (hv : IsUnit (f (middleNodeV a c))) :
    (f.comp (conicParameterToMiddleNode c).toRingHom).comp
        (middleLocalizedConicRestriction c).toRingHom = f :=
  middleNode_conicFactor_ringHom c f (middleNode_horizontal_eq_zero_of_slope_isUnit c f a hv)

end FLT.Mazur.WeierstrassSuccessiveX
