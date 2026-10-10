/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleSecondNode
public import FLT.Mazur.WeierstrassSuccessiveXMiddleLines

/-!
# Original component ideals in both ordered middle node charts

The conic ideal becomes (u), and each original horizontal boundary line
becomes (z) in its ordered node neighborhood. These retain the complete
scheme structure of the attachments.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "N" => MiddleNodeOpen c
local notation "O" => MiddleFirstOpen W c
local notation "P" => MiddleSecondOpen W c
local notation "F" => RingHom.comp
  (middleFirstNodeEquiv W c h2 ha : O →+* N) (algebraMap A O)
local notation "G" => RingHom.comp
  (middleSecondNodeEquiv W c h2 ha : P →+* N) (algebraMap A P)

/-- The actual first node map keeps every original middle generator. -/
theorem middleFirstNodeEquiv_coord (i : Fin 3) :
    middleFirstNodeEquiv W c h2 ha (algebraMap A O (coord W 0 0 0 0 c i)) =
      ![middleNodeT W.a₁ c, middleNodeV W.a₁ c, middleNodeU c] i := by
  change middleFirstToNode W c h2 ha _ = _
  rw [middleFirstToNode_base, middleFirstToNodeBase_coord]

/-- The second node map keeps the actual tangent involution on every original function. -/
theorem middleSecondNodeEquiv_base (q : A) :
    middleSecondNodeEquiv W c h2 ha (algebraMap A P q) =
      middleFirstNodeEquiv W c h2 ha
        (algebraMap A O (middleTangentSwitch W c h2 q)) := by
  simp only [middleSecondNodeEquiv, AlgEquiv.trans_apply, middleTangentOpenEquiv,
    PrincipalOpenTransport.equiv_symm_base]
  rfl

/-- The conic equation becomes exactly the retained u-zero branch in the first node. -/
theorem middleFirstNode_conicIdeal :
    Ideal.map F (Ideal.span {coord W 0 0 0 0 c 2}) = Ideal.span {middleNodeU c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {middleFirstNodeEquiv W c h2 ha (algebraMap A O _)} = _
  rw [middleFirstNodeEquiv_u]

/-- The same original conic equation becomes the u-zero branch in the second node. -/
theorem middleSecondNode_conicIdeal :
    Ideal.map G (Ideal.span {coord W 0 0 0 0 c 2}) = Ideal.span {middleNodeU c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {middleSecondNodeEquiv W c h2 ha (algebraMap A P _)} = _
  rw [middleSecondNodeEquiv_u]

include ha in
/-- The displayed inverse incidence coordinate generates exactly the node z ideal. -/
theorem middleNode_tIdeal : Ideal.span {middleNodeT W.a₁ c} =
    Ideal.span {middleNodeZ c} := by
  rw [middleNodeT, conicInverseT, map_mul, map_mul, AlgHom.commutes,
    conicParameterToMiddleNode_z,
    Ideal.span_singleton_mul_right_unit
      ((conicParameterInv_isUnit c).map (conicParameterToMiddleNode c)),
    Ideal.span_singleton_mul_left_unit (ha.map (algebraMap R N))]

/-- The node slope remains an actual multiple of the original incidence coordinate. -/
theorem middleNode_v_multiple : middleNodeV W.a₁ c =
    middleNodeT W.a₁ c * (algebraMap R N c * middleNodeZ c) := by
  simp only [middleNodeV, middleNodeT, conicInverseV, conicInverseT,
    map_mul, map_pow, AlgHom.commutes, conicParameterToMiddleNode_z]
  ring

/-- The first original horizontal line is exactly the node z-zero branch. -/
theorem middleFirstNode_lineIdeal :
    Ideal.map F (middleLineIdeal W c 0) = Ideal.span {middleNodeZ c} := by
  rw [middleLineIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {middleFirstNodeEquiv W c h2 ha (algebraMap A O _),
    middleFirstNodeEquiv W c h2 ha (algebraMap A O _)} = _
  rw [map_zero, sub_zero, middleFirstNodeEquiv_coord, middleFirstNodeEquiv_coord]
  change Ideal.span {middleNodeT W.a₁ c, middleNodeV W.a₁ c} = _
  rw [Ideal.span_pair_eq_span_left_iff_dvd.mpr
    ⟨algebraMap R N c * middleNodeZ c, middleNode_v_multiple W c⟩,
    middleNode_tIdeal W c ha]

/-- The second original horizontal line is exactly the opposite node z-zero branch. -/
theorem middleSecondNode_lineIdeal :
    Ideal.map G (middleLineIdeal W c (-W.a₁)) = Ideal.span {middleNodeZ c} := by
  rw [middleLineIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {middleSecondNodeEquiv W c h2 ha (algebraMap A P _),
    middleSecondNodeEquiv W c h2 ha (algebraMap A P _)} = _
  rw [middleSecondNodeEquiv_base, middleSecondNodeEquiv_base]
  rw [map_neg, sub_neg_eq_add]
  have hs : middleTangentSwitch W c h2
      (coord W 0 0 0 0 c 1 + algebraMap R A W.a₁) = -coord W 0 0 0 0 c 1 :=
    middleTangentEquiv_first W c h2
  rw [hs, middleTangentSwitch_coord, Matrix.cons_val_zero]
  rw [map_neg, map_neg, middleFirstNodeEquiv_coord, middleFirstNodeEquiv_coord]
  change Ideal.span {middleNodeT W.a₁ c, -middleNodeV W.a₁ c} = _
  rw [Ideal.span_pair_neg, Ideal.span_pair_eq_span_left_iff_dvd.mpr
    ⟨algebraMap R N c * middleNodeZ c, middleNode_v_multiple W c⟩,
    middleNode_tIdeal W c ha]

end FLT.Mazur.WeierstrassSuccessiveX
