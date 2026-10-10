/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOrigin
public import FLT.Mazur.WeierstrassModificationXFullSecondNode

/-!
# Original component ideals at the second full node

The second chart preserves the same incidence and conic components. Its
intersection quotient is R, with original slope -a rather than zero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "O" => FullSecondFiberOpen a c
local notation "L" => FullNodeOpen (-a) c
local notation "E" => fullSecondNodeEquiv a c ha
local notation "V" => fullNodeInverseV (-a) c
local notation "T" => fullNodeInverseT (-a) c
local notation "A" => algebraMap R L a
local notation "C" => algebraMap R L c

/-- The original conic factor retains the second node's orientation. -/
theorem fullSecondNodeEquiv_conic : E (algebraMap F O (fiberConicFactor a c)) =
    fullNodeQ (-a) c * (V + algebraMap R L (-a)) := by
  simp only [fiberConicFactor, map_sub, map_mul, map_add, map_pow,
    ← IsScalarTower.algebraMap_apply R F O, AlgEquiv.commutes,
    fullSecondNodeEquiv_t, fullSecondNodeEquiv_v]
  calc (V - A) * (V - A + A) - C * T ^ 2 =
      V * (V + algebraMap R L (-a)) - C * T ^ 2 := by rw [map_neg]; ring
    _ = _ := fullNodeInverse_conic (-a) c

/-- The second chart's p-zero branch is the original incidence line. -/
theorem fullSecondNodeEquiv_incidenceIdeal :
    Ideal.map (E).toRingHom (Ideal.span {algebraMap F O (fiberT a c)}) =
      Ideal.span {fullNodeP (-a) c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {E (algebraMap F O (fiberT a c))} = _
  rw [fullSecondNodeEquiv_t, fullNodeInverseT,
    Ideal.span_singleton_mul_right_unit (fullNodeInv_isUnit (-a) c),
    Ideal.span_singleton_mul_left_unit (ha.neg.map (algebraMap R L))]

/-- The second chart's q-zero branch is the original conic component. -/
theorem fullSecondNodeEquiv_conicIdeal :
    Ideal.map (E).toRingHom (Ideal.span {algebraMap F O (fiberConicFactor a c)}) =
      Ideal.span {fullNodeQ (-a) c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {E (algebraMap F O (fiberConicFactor a c))} = _
  rw [fullSecondNodeEquiv_conic,
    Ideal.span_singleton_mul_right_unit (fullNodeInverseV_add_isUnit (-a) c)]

/-- The second ambient chart preserves the scheme-theoretic component intersection. -/
theorem fullSecondNodeEquiv_intersectionIdeal :
    Ideal.map (E).toRingHom
      (Ideal.span {algebraMap F O (fiberT a c)} ⊔
        Ideal.span {algebraMap F O (fiberConicFactor a c)}) = fullNodeOriginIdeal (-a) c := by
  rw [Ideal.map_sup, fullSecondNodeEquiv_incidenceIdeal, fullSecondNodeEquiv_conicIdeal]
  rfl

/-- The second original component intersection quotient is the coefficient ring. -/
def fullSecondIncidenceEquiv :
    (O ⧸ (Ideal.span {algebraMap F O (fiberT a c)} ⊔
      Ideal.span {algebraMap F O (fiberConicFactor a c)})) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlg _ _ E
    (fullSecondNodeEquiv_intersectionIdeal a c ha).symm).trans
      (fullNodeOriginEquiv (-a) c ha.neg)

/-- The first quotient map is evaluation at the origin of its actual ambient node chart. -/
theorem fullFirstIncidenceEquiv_mk (x : FullFirstFiberOpen a c) :
    fullFirstIncidenceEquiv a c ha (Ideal.Quotient.mk _ x) =
      fullNodeOrigin a c ha (fullFirstNodeEquiv a c ha x) := by
  rw [fullFirstIncidenceEquiv, fullFirstNodeIntersectionEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlg_mk, fullNodeOriginEquiv_mk]

/-- The second quotient map is evaluation at the oppositely oriented node origin. -/
theorem fullSecondIncidenceEquiv_mk (x : O) :
    fullSecondIncidenceEquiv a c ha (Ideal.Quotient.mk _ x) =
      fullNodeOrigin (-a) c ha.neg (E x) := by
  rw [fullSecondIncidenceEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    fullNodeOriginEquiv_mk]

end FLT.Mazur.WeierstrassModificationX
