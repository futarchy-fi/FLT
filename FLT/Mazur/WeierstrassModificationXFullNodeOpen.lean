/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra
public import FLT.Mazur.WeierstrassModificationXFiberConicNodeParameter

/-!
# The product-zero node open for the full conic fiber

Invert the product (q+a)(1-c*p²) in the actual algebra pq=0. Both factors
are then units. The full fiber's rational coordinates define a map from
this localization, retaining the arbitrary coefficient c.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "N" => NodalFiber.Coordinate (0 : R)

/-- The product of the two denominators for the ambient node comparison. -/
def fullNodeDenominator : N :=
  (NodalFiber.q 0 + algebraMap R N a) * (1 - algebraMap R N c * NodalFiber.p 0 ^ 2)
/-- The actual node with both required denominators inverted. -/
abbrev FullNodeOpen := Localization.Away (fullNodeDenominator a c)
/-- First coordinate of the localized product-zero node. -/
def fullNodeP : FullNodeOpen a c := algebraMap N _ (NodalFiber.p 0)
/-- Second coordinate of the localized product-zero node. -/
def fullNodeQ : FullNodeOpen a c := algebraMap N _ (NodalFiber.q 0)
local notation "L" => FullNodeOpen a c
local notation "P" => fullNodeP a c
local notation "Q" => fullNodeQ a c
local notation "A" => algebraMap R L a
local notation "C" => algebraMap R L c

/-- The localized coordinates still have product zero. -/
theorem fullNode_relation : P * Q = 0 := by
  rw [fullNodeP, fullNodeQ, ← map_mul, NodalFiber.relation, map_zero, map_zero]

/-- The image of the inverted element is the displayed product of factors. -/
theorem fullNodeDenominator_map :
    algebraMap N L (fullNodeDenominator a c) = (Q + A) * (1 - C * P ^ 2) := by
  simp only [fullNodeDenominator, map_mul, map_add, map_sub, map_one, map_pow,
    ← IsScalarTower.algebraMap_apply R N L, fullNodeP, fullNodeQ]

/-- The opposite tangent factor is a unit on the node open. -/
theorem fullNode_tangent_isUnit : IsUnit (Q + A) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := L) (fullNodeDenominator a c)
  rw [fullNodeDenominator_map] at h
  exact isUnit_of_mul_isUnit_left h

/-- The rational parameter denominator is a unit on the node open. -/
theorem fullNode_parameter_isUnit : IsUnit (1 - C * P ^ 2) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := L) (fullNodeDenominator a c)
  rw [fullNodeDenominator_map] at h
  exact isUnit_of_mul_isUnit_right h

/-- Evaluate the original node at the full fiber's proved rational coordinates. -/
def fullNodeToFiberBase : N →ₐ[R] FullFirstFiberOpen a c :=
  NodalFiber.evaluation 0 (fullFirstFiberParameter a c) (fullFirstFiberNodeSlope a c)
    (by simpa only [map_zero] using fullFirstFiber_node_relation a c)

/-- Evaluation retains the rational incidence parameter. -/
@[simp] theorem fullNodeToFiberBase_p :
    fullNodeToFiberBase a c (NodalFiber.p 0) = fullFirstFiberParameter a c :=
  NodalFiber.evaluation_p _ _ _ _
/-- Evaluation retains the corrected conic slope. -/
@[simp] theorem fullNodeToFiberBase_q :
    fullNodeToFiberBase a c (NodalFiber.q 0) = fullFirstFiberNodeSlope a c :=
  NodalFiber.evaluation_q _ _ _ _

/-- The two proved unit identities extend evaluation to the actual node open. -/
def fullNodeToFiber (ha : IsUnit a) : L →ₐ[R] FullFirstFiberOpen a c :=
  IsLocalization.Away.liftAlgHom (f := fullNodeToFiberBase a c)
    (fullNodeDenominator a c) (by
      simp only [fullNodeDenominator, map_mul, map_add, map_sub, map_one, map_pow,
        fullNodeToFiberBase_p, fullNodeToFiberBase_q, AlgHom.commutes]
      exact (fullFirstFiber_nodeDenominator_isUnit a c ha).mul
        (fullFirstFiber_denominator_isUnit a c ha))

/-- The localized map agrees with the original node evaluation. -/
theorem fullNodeToFiber_base (ha : IsUnit a) (x : N) :
    fullNodeToFiber a c ha (algebraMap N L x) = fullNodeToFiberBase a c x := by
  rw [fullNodeToFiber, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The first localized coordinate is the original rational parameter. -/
theorem fullNodeToFiber_p (ha : IsUnit a) :
    fullNodeToFiber a c ha P = fullFirstFiberParameter a c := by
  rw [fullNodeP, fullNodeToFiber_base, fullNodeToFiberBase_p]
/-- The second localized coordinate is the original corrected slope. -/
theorem fullNodeToFiber_q (ha : IsUnit a) :
    fullNodeToFiber a c ha Q = fullFirstFiberNodeSlope a c := by
  rw [fullNodeQ, fullNodeToFiber_base, fullNodeToFiberBase_q]

end FLT.Mazur.WeierstrassModificationX
