/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedBranchCoordinates

/-!
# The original conic parameter and horizontal coordinate on the localized middle branches

The first branch is precisely the original conic parameter open. The second
is the whole affine line. Restriction preserves the original parameter map
and both inverse conic coordinates at arbitrary constant.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (c : K)
local notation "s" => middleNodePairDenominator c
local notation "L" => MiddleNodeOpen c
local notation "B₁" => Localization.Away (PolygonNodeEqualizer.first s)
local notation "B₂" => Localization.Away (PolygonNodeEqualizer.second s)
local notation "P" => ConicParameterOpen c

/-- The conic branch ring retains exactly its original denominator. -/
theorem middleLocalizedFirstBranch_isLocalization :
    IsLocalization.Away (conicParameterPolynomial c) B₁ := by
  rw [show conicParameterPolynomial c = PolygonNodeEqualizer.first s from
    (middleNodePairDenominator_first c).symm]
  infer_instance

/-- The first branch has exactly the original full conic parameter ring. -/
def middleLocalizedConicParameterEquiv : B₁ ≃ₐ[K] P := by
  let _ := middleLocalizedFirstBranch_isLocalization c
  exact AlgEquiv.restrictScalars K
    (IsLocalization.algEquiv (Submonoid.powers (conicParameterPolynomial c)) B₁ P)

/-- Every polynomial is unchanged by the parameter comparison. -/
theorem middleLocalizedConicParameterEquiv_base (p : K[X]) :
    middleLocalizedConicParameterEquiv c (algebraMap K[X] B₁ p) = algebraMap K[X] P p := by
  let _ := middleLocalizedFirstBranch_isLocalization c
  exact (IsLocalization.algEquiv (Submonoid.powers (conicParameterPolynomial c)) B₁ P).commutes p

/-- The entire horizontal branch is the original affine polynomial ring. -/
def middleLocalizedLineEquiv : B₂ ≃ₐ[K] K[X] :=
  (AlgEquiv.restrictScalars K (IsLocalization.atUnit K[X] B₂
    (PolygonNodeEqualizer.second s)
    (by rw [middleNodePairDenominator_second]; exact isUnit_one))).symm

/-- The horizontal coordinate comparison preserves every original polynomial. -/
theorem middleLocalizedLineEquiv_base (p : K[X]) :
    middleLocalizedLineEquiv c (algebraMap K[X] B₂ p) = p := by
  apply (middleLocalizedLineEquiv c).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact (IsLocalization.atUnit K[X] B₂ (PolygonNodeEqualizer.second s)
    (by rw [middleNodePairDenominator_second]; exact isUnit_one)).commutes p |>.symm

/-- First-branch restriction keeps the original coefficient field. -/
theorem middleLocalizedFirstRestriction_constant (k : K) :
    middleLocalizedFirstRestriction c (algebraMap K L k) = algebraMap K B₁ k := by
  have hc : NodalFiber.polygonNodeEquiv
      (algebraMap K (SuccessiveIncidence.Coordinate (0 : K)) k) =
      algebraMap K (PolygonNodeEqualizer.A (R := K)) k := NodalFiber.polygonNodeEquiv.commutes k
  rw [IsScalarTower.algebraMap_apply K (SuccessiveIncidence.Coordinate (0 : K)) L,
    middleLocalizedFirstRestriction_base, hc, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply K K[X] B₁]

/-- The first restriction regarded over the original residue field. -/
def middleLocalizedFirstRestrictionAlg : L →ₐ[K] B₁ where
  __ := middleLocalizedFirstRestriction c
  commutes' := middleLocalizedFirstRestriction_constant c

/-- The original full node restricted to its original conic parameter open. -/
def middleLocalizedConicRestriction : L →ₐ[K] P :=
  (middleLocalizedConicParameterEquiv c).toAlgHom.comp (middleLocalizedFirstRestrictionAlg c)

/-- The original node parameter remains the original conic parameter. -/
@[simp] theorem middleLocalizedConicRestriction_z :
    middleLocalizedConicRestriction c (middleNodeZ c) = conicParameterZ c := by
  change middleLocalizedConicParameterEquiv c
    (middleLocalizedFirstRestriction c (middleNodeZ c)) = _
  rw [middleLocalizedFirstRestriction_z, middleLocalizedConicParameterEquiv_base]
  rfl

/-- The original horizontal coordinate vanishes on the conic branch. -/
@[simp] theorem middleLocalizedConicRestriction_u :
    middleLocalizedConicRestriction c (middleNodeU c) = 0 := by
  change middleLocalizedConicParameterEquiv c
    (middleLocalizedFirstRestriction c (middleNodeU c)) = _
  rw [middleLocalizedFirstRestriction_u, map_zero]

/-- The entire original conic parameter map is a section of restriction. -/
theorem middleLocalizedConicRestriction_parameter :
    (middleLocalizedConicRestriction c).comp (conicParameterToMiddleNode c) = AlgHom.id K P := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change middleLocalizedConicRestriction c
    (conicParameterToMiddleNode c (conicParameterZ c)) = conicParameterZ c
  rw [conicParameterToMiddleNode_z, middleLocalizedConicRestriction_z]

/-- Restriction recovers the original rational incidence formula on the conic. -/
theorem middleLocalizedConicRestriction_t (a : K) :
    middleLocalizedConicRestriction c (middleNodeT a c) = conicInverseT a c :=
  DFunLike.congr_fun (middleLocalizedConicRestriction_parameter c) (conicInverseT a c)

/-- Restriction recovers the original rational slope formula on the conic. -/
theorem middleLocalizedConicRestriction_v (a : K) :
    middleLocalizedConicRestriction c (middleNodeV a c) = conicInverseV a c :=
  DFunLike.congr_fun (middleLocalizedConicRestriction_parameter c) (conicInverseV a c)

end FLT.Mazur.WeierstrassSuccessiveX
