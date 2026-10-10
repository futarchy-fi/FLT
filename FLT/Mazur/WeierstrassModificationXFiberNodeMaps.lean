/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberBranches
public import FLT.Mazur.NodalFiberAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Actual maps near the first horizontal fiber node

Inverting v+a removes the second tangent component. The remaining equation
is t*v=0, with the same incidence and slope coordinates. Both substitutions
below extend to the corresponding principal opens of the actual algebras.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a : R)

/-- The full fiber with the other tangent branch removed. -/
abbrev FirstFiberOpen := Localization.Away (fiberV a 0 + algebraMap R _ a)

/-- The corresponding open in the existing product-zero node algebra. -/
abbrev FirstNodeOpen :=
  Localization.Away (NodalFiber.q (0 : R) + algebraMap R _ a)

/-- On the actual first open, the incidence and slope multiply to zero. -/
theorem firstFiberOpen_relation :
    algebraMap (FiberCoordinate a 0) (FirstFiberOpen a) (fiberT a 0) *
      algebraMap _ _ (fiberV a 0) = 0 := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := FirstFiberOpen a)
    (fiberV a 0 + algebraMap R _ a)
  apply hu.mul_right_cancel
  rw [zero_mul, ← map_mul, ← map_mul, fiber_lines_relation, map_zero]

/-- The full three-line fiber maps to the first node open with its original coordinates. -/
def fiberToFirstNode : FiberCoordinate a 0 →ₐ[R] FirstNodeOpen a :=
  fiberEvaluation a 0
    (algebraMap (NodalFiber.Coordinate (0 : R)) _ (NodalFiber.p (0 : R)))
    (algebraMap _ _ (NodalFiber.q (0 : R))) (by
      have h : algebraMap (NodalFiber.Coordinate (0 : R)) (FirstNodeOpen a)
          (NodalFiber.p (0 : R)) * algebraMap _ _ (NodalFiber.q (0 : R)) = 0 := by
        rw [← map_mul, NodalFiber.relation, map_zero, map_zero]
      simp only [map_zero, zero_mul, sub_zero, ← mul_assoc, h])

/-- The node maps to the actual fiber open, including its exceptional intersection. -/
def nodeToFirstFiber : NodalFiber.Coordinate (0 : R) →ₐ[R] FirstFiberOpen a :=
  NodalFiber.evaluation 0 (algebraMap _ _ (fiberT a 0))
    (algebraMap _ _ (fiberV a 0)) (by simpa only [map_zero] using firstFiberOpen_relation a)

/-- The forward substitution preserves t. -/
@[simp] theorem fiberToFirstNode_t : fiberToFirstNode a (fiberT a 0) =
    algebraMap _ _ (NodalFiber.p (0 : R)) := fiberEvaluation_t _ _ _ _ _

/-- The forward substitution preserves v. -/
@[simp] theorem fiberToFirstNode_v : fiberToFirstNode a (fiberV a 0) =
    algebraMap _ _ (NodalFiber.q (0 : R)) := fiberEvaluation_v _ _ _ _ _

/-- The inverse substitution preserves the first node coordinate. -/
@[simp] theorem nodeToFirstFiber_p : nodeToFirstFiber a (NodalFiber.p (0 : R)) =
    algebraMap _ _ (fiberT a 0) := NodalFiber.evaluation_p _ _ _ _

/-- The inverse substitution preserves the second node coordinate. -/
@[simp] theorem nodeToFirstFiber_q : nodeToFirstFiber a (NodalFiber.q (0 : R)) =
    algebraMap _ _ (fiberV a 0) := NodalFiber.evaluation_q _ _ _ _

/-- The original discarded factor is invertible on the first node open. -/
theorem fiberToFirstNode_isUnit :
    IsUnit (fiberToFirstNode a (fiberV a 0 + algebraMap R _ a)) := by
  simpa only [map_add, fiberToFirstNode_v, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R (NodalFiber.Coordinate (0 : R)) (FirstNodeOpen a)] using
    IsLocalization.Away.algebraMap_isUnit (S := FirstNodeOpen a)
      (NodalFiber.q (0 : R) + algebraMap R _ a)

/-- The discarded node factor is invertible on the actual first fiber open. -/
theorem nodeToFirstFiber_isUnit :
    IsUnit (nodeToFirstFiber a (NodalFiber.q (0 : R) + algebraMap R _ a)) := by
  simpa only [map_add, nodeToFirstFiber_q, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R (FiberCoordinate a 0) (FirstFiberOpen a)] using
    IsLocalization.Away.algebraMap_isUnit (S := FirstFiberOpen a)
      (fiberV a 0 + algebraMap R _ a)

/-- The actual forward substitution on the first principal opens. -/
def firstNodeForward : FirstFiberOpen a →ₐ[R] FirstNodeOpen a :=
  IsLocalization.Away.liftAlgHom _ (fiberToFirstNode_isUnit a)

/-- The actual inverse substitution on the first principal opens. -/
def firstNodeBackward : FirstNodeOpen a →ₐ[R] FirstFiberOpen a :=
  IsLocalization.Away.liftAlgHom _ (nodeToFirstFiber_isUnit a)

/-- Forward localization agrees with the original fiber substitution. -/
@[simp] theorem firstNodeForward_base (z : FiberCoordinate a 0) :
    firstNodeForward a (algebraMap _ _ z) = fiberToFirstNode a z := by
  rw [firstNodeForward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- Reverse localization agrees with the original node substitution. -/
@[simp] theorem firstNodeBackward_base (z : NodalFiber.Coordinate (0 : R)) :
    firstNodeBackward a (algebraMap _ _ z) = nodeToFirstFiber a z := by
  rw [firstNodeBackward, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
