/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodePushout
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# Original coordinates on the two full split attachment branches

Restriction to the first branch retains the conic parameter. Restriction to
the second retains the horizontal coordinate. Both use the proved comparison
with the original localized node ring.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (c : K) (hc : c = 0)
local notation "N" => MiddleNodeOpen c

/-- Restriction to the full original conic branch of a split attachment. -/
def middleSplitFirstRestriction : N →ₐ[K] K[X] :=
  PolygonNodeEqualizer.first.comp (middleNodeEquivOfZero c hc).toAlgHom

/-- Restriction to the full original horizontal branch of a split attachment. -/
def middleSplitSecondRestriction : N →ₐ[K] K[X] :=
  PolygonNodeEqualizer.second.comp (middleNodeEquivOfZero c hc).toAlgHom

@[simp] theorem middleSplitFirstRestriction_z :
    middleSplitFirstRestriction c hc (middleNodeZ c) = X := by
  change PolygonNodeEqualizer.first
    (middleNodeEquivOfZero c hc (middleNodeZ c)) = _
  rw [middleNodeEquivOfZero_z]
  rfl

@[simp] theorem middleSplitFirstRestriction_u :
    middleSplitFirstRestriction c hc (middleNodeU c) = 0 := by
  change PolygonNodeEqualizer.first
    (middleNodeEquivOfZero c hc (middleNodeU c)) = _
  rw [middleNodeEquivOfZero_u]
  rfl

@[simp] theorem middleSplitSecondRestriction_z :
    middleSplitSecondRestriction c hc (middleNodeZ c) = 0 := by
  change PolygonNodeEqualizer.second
    (middleNodeEquivOfZero c hc (middleNodeZ c)) = _
  rw [middleNodeEquivOfZero_z]
  rfl

@[simp] theorem middleSplitSecondRestriction_u :
    middleSplitSecondRestriction c hc (middleNodeU c) = X := by
  change PolygonNodeEqualizer.second
    (middleNodeEquivOfZero c hc (middleNodeU c)) = _
  rw [middleNodeEquivOfZero_u]
  rfl

/-- The entire original parameter map restricts to the original full affine parameter. -/
theorem middleSplitFirstRestriction_parameter :
    (middleSplitFirstRestriction c hc).comp (conicParameterToMiddleNode c) =
      (conicZeroAffineEquiv c hc).toAlgHom := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change middleSplitFirstRestriction c hc
    (conicParameterToMiddleNode c (conicParameterZ c)) =
      conicZeroAffineEquiv c hc (algebraMap K[X] (ConicParameterOpen c) X)
  rw [conicParameterToMiddleNode_z, middleSplitFirstRestriction_z, conicZeroAffineEquiv_base]

/-- The first branch is the spectrum of restriction on the original localized ring. -/
theorem middleNodeFirstBranch_eq_spec :
    middleNodeFirstBranch c hc = AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (middleSplitFirstRestriction c hc).toRingHom) := by
  change AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ = _
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

/-- The second branch is the spectrum of restriction on the same original localized ring. -/
theorem middleNodeSecondBranch_eq_spec :
    middleNodeSecondBranch c hc = AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (middleSplitSecondRestriction c hc).toRingHom) := by
  change AlgebraicGeometry.Spec.map _ ≫ AlgebraicGeometry.Spec.map _ = _
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
