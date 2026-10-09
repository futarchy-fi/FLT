/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleFirstParameter
public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeCoordinates

/-!
# Both actual maps of the first attachment-node comparison

The retained conic formulas and the original horizontal generator define a
map to the full middle chart. Its inverse uses z=t/(v+a₁) and the same u.
Both maps extend to the actual principal localizations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "O" => MiddleFirstOpen W c
local notation "N" => MiddleNodeOpen c
local notation "B" => SuccessiveIncidence.Coordinate (0 : R)

/-- The node generators satisfy the complete original three-variable equation. -/
def middleFirstToNodeBase : A →ₐ[R] N :=
  evaluation W 0 0 0 0 c ![middleNodeT W.a₁ c, middleNodeV W.a₁ c, middleNodeU c]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h2, map_zero,
        zero_mul, zero_add, add_zero]
      linear_combination middleNode_conic W.a₁ c)
    (by
      change middleNodeT W.a₁ c * middleNodeU c = algebraMap R N 0
      rw [map_zero]; exact middleNode_incidence W.a₁ c)

/-- The map keeps all three original coordinates with their full inverse formulas. -/
@[simp] theorem middleFirstToNodeBase_coord (i : Fin 3) :
    middleFirstToNodeBase W c h2 (coord W 0 0 0 0 c i) =
      ![middleNodeT W.a₁ c, middleNodeV W.a₁ c, middleNodeU c] i :=
  evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- Extend the original inverse-coordinate map to the full first tangent open. -/
def middleFirstToNode : O →ₐ[R] N :=
  IsLocalization.Away.liftAlgHom (coord W 0 0 0 0 c 1 + algebraMap R A W.a₁)
    (f := middleFirstToNodeBase W c h2) (by
      simpa only [map_add, middleFirstToNodeBase_coord, Matrix.cons_val_one,
        Matrix.cons_val_zero, AlgHom.commutes] using middleNode_v_add_isUnit W.a₁ c ha)

/-- Restriction from the original middle chart retains the inverse-coordinate map. -/
@[simp] theorem middleFirstToNode_base (q : A) :
    middleFirstToNode W c h2 ha (algebraMap A O q) = middleFirstToNodeBase W c h2 q := by
  rw [middleFirstToNode, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- Extend the original rational-parameter map to the actual localized node. -/
def middleNodeToFirst : N →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (middleNodeDenominator c)
    (f := middleNodeToFirstBase W c) (by
      simpa only [middleNodeDenominator, map_sub, map_one, map_mul, map_pow,
        AlgHom.commutes, middleNodeToFirstBase, SuccessiveIncidence.evaluation_t] using
        middleFirstParameter_denominator_isUnit W c h2 ha)

/-- Restriction from the standard node retains its original evaluation map. -/
@[simp] theorem middleNodeToFirst_base (q : B) :
    middleNodeToFirst W c h2 ha (algebraMap B N q) = middleNodeToFirstBase W c q := by
  rw [middleNodeToFirst, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The node incidence parameter becomes exactly t/(v+a₁). -/
@[simp] theorem middleNodeToFirst_z :
    middleNodeToFirst W c h2 ha (middleNodeZ c) = middleFirstParameter W c := by
  rw [middleNodeZ, middleNodeToFirst_base, middleNodeToFirstBase,
    SuccessiveIncidence.evaluation_t]

/-- The original horizontal function is unchanged by the node chart. -/
@[simp] theorem middleNodeToFirst_u :
    middleNodeToFirst W c h2 ha (middleNodeU c) =
      algebraMap A O (coord W 0 0 0 0 c 2) := by
  rw [middleNodeU, middleNodeToFirst_base, middleNodeToFirstBase,
    SuccessiveIncidence.evaluation_u]

/-- The inverse map recovers the original localized node parameter. -/
@[simp] theorem middleFirstToNode_parameter :
    middleFirstToNode W c h2 ha (middleFirstParameter W c) = middleNodeZ c := by
  apply (middleNode_v_add_isUnit W.a₁ c ha).mul_right_cancel
  have h := congrArg (middleFirstToNode W c h2 ha) (middleFirstParameter_mul W c)
  simpa only [map_mul, middleFirstToNode_base, map_add,
    middleFirstToNodeBase_coord, Matrix.cons_val_zero, Matrix.cons_val_one,
    AlgHom.commutes, middleNode_parameter_mul] using h

end FLT.Mazur.WeierstrassSuccessiveX
