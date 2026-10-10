/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedBranchParameters
public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeBranches

/-!
# Original conic and horizontal maps at arbitrary middle constant

Restriction retains the whole conic parameter open and both original horizontal
lines. No vanishing hypothesis is imposed on the divided constant.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (c : K)
local notation "L" => MiddleNodeOpen c
local notation "B₂" => Localization.Away (PolygonNodeEqualizer.second (middleNodePairDenominator c))

/-- The horizontal restriction preserves the original residue field. -/
theorem middleLocalizedSecondRestriction_constant (k : K) :
    middleLocalizedSecondRestriction c (algebraMap K L k) = algebraMap K B₂ k := by
  have hc : NodalFiber.polygonNodeEquiv
      (algebraMap K (SuccessiveIncidence.Coordinate (0 : K)) k) =
      algebraMap K (PolygonNodeEqualizer.A (R := K)) k := NodalFiber.polygonNodeEquiv.commutes k
  rw [IsScalarTower.algebraMap_apply K (SuccessiveIncidence.Coordinate (0 : K)) L,
    middleLocalizedSecondRestriction_base, hc, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply K K[X] B₂]

/-- Horizontal restriction as an algebra map over the residue field. -/
def middleLocalizedSecondRestrictionAlg : L →ₐ[K] B₂ where
  __ := middleLocalizedSecondRestriction c
  commutes' := middleLocalizedSecondRestriction_constant c

/-- Restriction to the entire original horizontal parameter line. -/
def middleLocalizedLineRestriction : L →ₐ[K] K[X] :=
  (middleLocalizedLineEquiv c).toAlgHom.comp (middleLocalizedSecondRestrictionAlg c)

/-- The conic parameter vanishes on the horizontal branch. -/
@[simp] theorem middleLocalizedLineRestriction_z :
    middleLocalizedLineRestriction c (middleNodeZ c) = 0 := by
  change middleLocalizedLineEquiv c (middleLocalizedSecondRestriction c (middleNodeZ c)) = _
  rw [middleLocalizedSecondRestriction_z, map_zero]

/-- The horizontal branch keeps the original horizontal coordinate. -/
@[simp] theorem middleLocalizedLineRestriction_u :
    middleLocalizedLineRestriction c (middleNodeU c) = X := by
  change middleLocalizedLineEquiv c (middleLocalizedSecondRestriction c (middleNodeU c)) = _
  rw [middleLocalizedSecondRestriction_u, middleLocalizedLineEquiv_base]

/-- The original incidence function vanishes on the horizontal line. -/
@[simp] theorem middleLocalizedLineRestriction_t (a : K) :
    middleLocalizedLineRestriction c (middleNodeT a c) = 0 := by
  simp only [middleNodeT, conicInverseT, map_mul, AlgHom.commutes,
    conicParameterToMiddleNode_z, middleLocalizedLineRestriction_z, mul_zero, zero_mul]

/-- The original recentered slope vanishes on the horizontal line. -/
@[simp] theorem middleLocalizedLineRestriction_v (a : K) :
    middleLocalizedLineRestriction c (middleNodeV a c) = 0 := by
  simp only [middleNodeV, conicInverseV, map_mul, map_pow, AlgHom.commutes,
    conicParameterToMiddleNode_z, middleLocalizedLineRestriction_z,
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

variable (W : WeierstrassCurve K) (h2 : W.a₂ = 0)

/-- The first branch is the entire original conic parameterization. -/
theorem middleLocalizedConicRestriction_conic :
    (middleLocalizedConicRestriction c).comp (middleFirstToNodeBase W c h2) =
      (conicToParameter W.a₁ c).comp (middleConicMap W c h2) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleFirstToNodeBase_coord, middleConicMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, conicToParameter_t, conicToParameter_v,
      middleLocalizedConicRestriction_t, middleLocalizedConicRestriction_v,
      middleLocalizedConicRestriction_u, map_zero]

/-- The other branch is the full original first horizontal component. -/
theorem middleLocalizedLineRestriction_line :
    (middleLocalizedLineRestriction c).comp (middleFirstToNodeBase W c h2) =
      middleLineMap W c h2 0 (middle_first_root W) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleFirstToNodeBase_coord, middleLineMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, middleLocalizedLineRestriction_t,
      middleLocalizedLineRestriction_v, middleLocalizedLineRestriction_u, map_zero]

/-- The actual tangent involution gives the original opposite horizontal line. -/
theorem middleLocalizedLineRestriction_opposite_line :
    ((middleLocalizedLineRestriction c).comp (middleFirstToNodeBase W c h2)).comp
        (middleTangentSwitch W c h2) =
      middleLineMap W c h2 (-W.a₁) (middle_second_root W) := by
  rw [middleLocalizedLineRestriction_line]
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleTangentSwitch_coord, middleLineMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      map_sub, map_neg, AlgHom.commutes, map_zero, neg_zero, zero_sub]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
