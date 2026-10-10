/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleSplitBranchMaps
public import FLT.Mazur.WeierstrassModificationXConicSecondCoordinates

/-!
# The signed original parameter on the opposite split attachment

The tangent involution fixes t and sends v to -v-a. Consequently its node
parameter is the negative of the original second conic parameter t/v.
The comparison below is on complete algebra maps, including the slope translation.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] (c : K) (hc : c = 0)

/-- The split conic denominator is one on the whole affine parameter. -/
theorem conicZeroAffineEquiv_inv :
    conicZeroAffineEquiv c hc (conicParameterInv c) = 1 := by
  have h := congrArg (conicZeroAffineEquiv c hc) (conicParameter_mul_inv c)
  simpa only [hc, map_mul, map_sub, map_one, map_pow, map_zero,
    zero_mul, sub_zero, one_mul] using h

/-- The first original incidence function is a times the affine parameter. -/
theorem conicZeroAffineEquiv_inverseT (a : K) :
    conicZeroAffineEquiv c hc (conicInverseT a c) = C a * X := by
  simp only [conicInverseT, map_mul, AlgEquiv.commutes,
    conicParameterZ, conicZeroAffineEquiv_base, conicZeroAffineEquiv_inv, mul_one]
  rfl

/-- The first original slope vanishes on the full split conic parameter. -/
theorem conicZeroAffineEquiv_inverseV (a : K) :
    conicZeroAffineEquiv c hc (conicInverseV a c) = 0 := by
  simp only [conicInverseV, hc, map_zero,
    mul_zero, zero_mul]

/-- The node conic branch retains the scaled incidence parameter. -/
theorem middleSplitFirstRestriction_t (a : K) :
    middleSplitFirstRestriction c hc (middleNodeT a c) = C a * X := by
  calc _ = conicZeroAffineEquiv c hc (conicInverseT a c) :=
        DFunLike.congr_fun (middleSplitFirstRestriction_parameter c hc) _
    _ = _ := conicZeroAffineEquiv_inverseT c hc a

/-- Its original recentered conic slope is zero. -/
theorem middleSplitFirstRestriction_v (a : K) :
    middleSplitFirstRestriction c hc (middleNodeV a c) = 0 := by
  calc _ = conicZeroAffineEquiv c hc (conicInverseV a c) :=
        DFunLike.congr_fun (middleSplitFirstRestriction_parameter c hc) _
    _ = _ := conicZeroAffineEquiv_inverseV c hc a

variable (W : WeierstrassCurve K) (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "F" => ConicCoordinate W.a₁ c

/-- The opposite conic branch uses exactly the negated original second parameter. -/
theorem middleSplitFirstRestriction_opposite_conic :
    ((middleSplitFirstRestriction c hc).comp (middleFirstToNodeBase W c h2)).comp
        (middleTangentSwitch W c h2) =
      ((aeval (-X : K[X])).comp (conicZeroAffineEquiv c hc).toAlgHom).comp
        (((conicSecondParameterEquiv W.a₁ c ha).symm.toAlgHom.comp
          (Algebra.algHom K F (ConicSecondOpen W.a₁ c))).comp (middleConicMap W c h2)) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, middleTangentSwitch_coord, middleConicMap_coord,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_sub, map_neg, AlgHom.commutes, map_zero,
      middleFirstToNodeBase_coord]
  · rw [middleSplitFirstRestriction_t]
    change _ = aeval (-X : K[X]) (conicZeroAffineEquiv c hc
      ((conicSecondParameterEquiv W.a₁ c ha).symm (algebraMap F _ (conicT W.a₁ c))))
    rw [conicSecondParameterEquiv_symm_t, conicZeroAffineEquiv_inverseT]
    simp only [map_mul, aeval_C, aeval_X, map_neg, neg_mul_neg]
    rfl
  · change -middleSplitFirstRestriction c hc (middleNodeV W.a₁ c) - C W.a₁ = _
    rw [middleSplitFirstRestriction_v]
    change _ = aeval (-X : K[X]) (conicZeroAffineEquiv c hc
      ((conicSecondParameterEquiv W.a₁ c ha).symm (algebraMap F _ (conicV W.a₁ c))))
    rw [conicSecondParameterEquiv_symm_v]
    simp only [map_sub, AlgEquiv.commutes, conicZeroAffineEquiv_inverseV,
      neg_zero, zero_sub, map_neg, AlgHom.commutes]
    rfl
  · exact middleSplitFirstRestriction_u c hc

end FLT.Mazur.WeierstrassSuccessiveX
