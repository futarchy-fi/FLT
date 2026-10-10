/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedBranchMaps
public import FLT.Mazur.WeierstrassModificationXConicParameterNegation
public import FLT.Mazur.WeierstrassModificationXConicSecondCoordinates

/-!
# The original opposite conic restriction at arbitrary divided constant

The full tangent involution is expressed in the original second parameter,
with its sign, denominator and slope translation preserved.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "F" => ConicCoordinate W.a₁ c

/-- The opposite node retains the negative of the original second conic parameter. -/
theorem middleLocalizedConicRestriction_opposite_conic :
    ((middleLocalizedConicRestriction c).comp (middleFirstToNodeBase W c h2)).comp
        (middleTangentSwitch W c h2) =
      (conicParameterNeg c).toAlgHom.comp
        (((conicSecondParameterEquiv W.a₁ c ha).symm.toAlgHom.comp
          (Algebra.algHom K F (ConicSecondOpen W.a₁ c))).comp (middleConicMap W c h2)) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleTangentSwitch_coord, middleConicMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_sub, map_neg, AlgHom.commutes, map_zero,
      middleFirstToNodeBase_coord]
  · rw [middleLocalizedConicRestriction_t]
    change _ = conicParameterNeg c
      ((conicSecondParameterEquiv W.a₁ c ha).symm (algebraMap F _ (conicT W.a₁ c)))
    rw [conicSecondParameterEquiv_symm_t, conicParameterNeg_inverseT]
    simp only [conicInverseT, map_neg, neg_mul, neg_neg]
  · rw [middleLocalizedConicRestriction_v]
    change _ = conicParameterNeg c
      ((conicSecondParameterEquiv W.a₁ c ha).symm (algebraMap F _ (conicV W.a₁ c)))
    rw [conicSecondParameterEquiv_symm_v, map_sub, AlgEquiv.commutes,
      conicParameterNeg_inverseV]
    simp only [conicInverseV, map_neg, neg_mul]
  · exact middleLocalizedConicRestriction_u c

end FLT.Mazur.WeierstrassSuccessiveX
