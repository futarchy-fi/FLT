/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleSplitBranchCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeBranches

/-!
# Original component restrictions on the split middle attachment

The first node's conic restriction is its original full parameterization.
The other branch is the original horizontal line; on the second node the
actual tangent involution preserves the opposite horizontal line.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c : K) (hc : c = 0)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "N" => MiddleNodeOpen c

/-- The entire first conic restriction keeps the original parameter coordinate. -/
theorem middleSplitFirstRestriction_conic :
    (middleSplitFirstRestriction c hc).comp (middleFirstToNodeBase W c h2) =
      ((conicZeroAffineEquiv c hc).toAlgHom.comp (conicToParameter W.a₁ c)).comp
        (middleConicMap W c h2) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleFirstToNodeBase_coord, middleConicMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      conicToParameter_t, conicToParameter_v, middleSplitFirstRestriction_u, map_zero]
  · exact DFunLike.congr_fun (middleSplitFirstRestriction_parameter c hc) (conicInverseT W.a₁ c)
  · exact DFunLike.congr_fun (middleSplitFirstRestriction_parameter c hc) (conicInverseV W.a₁ c)

/-- The horizontal branch sends the original incidence coordinate to zero. -/
theorem middleSplitSecondRestriction_t (a : K) :
    middleSplitSecondRestriction c hc (middleNodeT a c) = 0 := by
  simp only [middleNodeT, conicInverseT, map_mul, AlgHom.commutes,
    conicParameterToMiddleNode_z, middleSplitSecondRestriction_z, mul_zero, zero_mul]

/-- The horizontal branch sends the recentered slope to zero. -/
theorem middleSplitSecondRestriction_v (a : K) :
    middleSplitSecondRestriction c hc (middleNodeV a c) = 0 := by
  simp only [middleNodeV, conicInverseV, map_mul, map_pow, AlgHom.commutes,
    conicParameterToMiddleNode_z, middleSplitSecondRestriction_z,
    zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]

/-- The entire second branch restriction is the original first horizontal component. -/
theorem middleSplitSecondRestriction_line :
    (middleSplitSecondRestriction c hc).comp (middleFirstToNodeBase W c h2) =
      middleLineMap W c h2 0 (middle_first_root W) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleFirstToNodeBase_coord, middleLineMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      middleSplitSecondRestriction_t, middleSplitSecondRestriction_v,
      middleSplitSecondRestriction_u, map_zero]

/-- The tangent involution sends the original first line restriction to the second line. -/
theorem middleSplitSecondRestriction_opposite_line :
    ((middleSplitSecondRestriction c hc).comp (middleFirstToNodeBase W c h2)).comp
        (middleTangentSwitch W c h2) =
      middleLineMap W c h2 (-W.a₁) (middle_second_root W) := by
  rw [middleSplitSecondRestriction_line]
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleTangentSwitch_coord, middleLineMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      map_sub, map_neg, AlgHom.commutes, map_zero, neg_zero, zero_sub]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
