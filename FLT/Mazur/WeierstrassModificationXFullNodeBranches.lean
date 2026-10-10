/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeEquiv

/-!
# The original component ideals in the full node chart

The incidence line t=0 becomes p=0 and the original conic equation becomes
q=0. These are equalities of ideals under the actual ambient equivalence,
so their scheme-theoretic intersection becomes the node origin.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "O" => FullFirstFiberOpen a c
local notation "L" => FullNodeOpen a c
local notation "E" => fullFirstNodeEquiv a c ha

/-- The first chart retains the original incidence formula. -/
theorem fullFirstNodeEquiv_t : E (algebraMap F O (fiberT a c)) = fullNodeInverseT a c := by
  change fullFiberToNode a c _ = _
  rw [fullFiberToNode_base, fullFiberToNodeBase_t]

/-- The first chart retains the original slope formula. -/
theorem fullFirstNodeEquiv_v : E (algebraMap F O (fiberV a c)) = fullNodeInverseV a c := by
  change fullFiberToNode a c _ = _
  rw [fullFiberToNode_base, fullFiberToNodeBase_v]

/-- The original conic equation becomes q times the invertible opposite tangent factor. -/
theorem fullFirstNodeEquiv_conic : E (algebraMap F O (fiberConicFactor a c)) =
    fullNodeQ a c * (fullNodeInverseV a c + algebraMap R L a) := by
  simp only [fiberConicFactor, map_sub, map_mul, map_add, map_pow,
    ← IsScalarTower.algebraMap_apply R F O, AlgEquiv.commutes,
    fullFirstNodeEquiv_t, fullFirstNodeEquiv_v]
  exact fullNodeInverse_conic a c

/-- The original incidence line is exactly the p-zero branch. -/
theorem fullFirstNodeEquiv_incidenceIdeal :
    Ideal.map (E).toRingHom (Ideal.span {algebraMap F O (fiberT a c)}) =
      Ideal.span {fullNodeP a c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {E (algebraMap F O (fiberT a c))} = _
  rw [fullFirstNodeEquiv_t, fullNodeInverseT,
    Ideal.span_singleton_mul_right_unit (fullNodeInv_isUnit a c),
    Ideal.span_singleton_mul_left_unit (ha.map (algebraMap R L))]

/-- The original conic component is exactly the q-zero branch. -/
theorem fullFirstNodeEquiv_conicIdeal :
    Ideal.map (E).toRingHom (Ideal.span {algebraMap F O (fiberConicFactor a c)}) =
      Ideal.span {fullNodeQ a c} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {E (algebraMap F O (fiberConicFactor a c))} = _
  rw [fullFirstNodeEquiv_conic,
    Ideal.span_singleton_mul_right_unit (fullNodeInverseV_add_isUnit a c)]

/-- The ideal of the scheme-theoretic origin on the actual node open. -/
def fullNodeOriginIdeal : Ideal L :=
  Ideal.span {fullNodeP a c} ⊔ Ideal.span {fullNodeQ a c}

/-- The full ambient comparison retains the scheme-theoretic component intersection. -/
theorem fullFirstNodeEquiv_intersectionIdeal :
    Ideal.map (E).toRingHom
      (Ideal.span {algebraMap F O (fiberT a c)} ⊔
        Ideal.span {algebraMap F O (fiberConicFactor a c)}) = fullNodeOriginIdeal a c := by
  rw [Ideal.map_sup, fullFirstNodeEquiv_incidenceIdeal, fullFirstNodeEquiv_conicIdeal]
  rfl

/-- The original component intersection quotient is the actual node-origin quotient. -/
def fullFirstNodeIntersectionEquiv :
    (O ⧸ (Ideal.span {algebraMap F O (fiberT a c)} ⊔
      Ideal.span {algebraMap F O (fiberConicFactor a c)})) ≃ₐ[R]
      (L ⧸ fullNodeOriginIdeal a c) :=
  Ideal.quotientEquivAlg _ _ E (fullFirstNodeEquiv_intersectionIdeal a c ha).symm

end FLT.Mazur.WeierstrassModificationX
