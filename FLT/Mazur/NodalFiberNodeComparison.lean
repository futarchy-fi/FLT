/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra
public import FLT.Mazur.PolygonNodeEvaluation

/-!
# Product-zero fibers are the existing two-branch polygon node

The comparison is an explicit algebra equivalence, preserving both tangent
coordinates and both polynomial branches. It lets divided residue fibers use
the existing node geometry without replacing their actual coordinate algebra.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.NodalFiber

open PolygonNodeEqualizer

variable {R : Type*} [CommRing R]

/-- Map the product-zero equation to the existing polynomial-pair node. -/
def toPolygonNode : Coordinate (0 : R) →ₐ[R] A (R := R) :=
  evaluation 0 PolygonNodeLocalization.x PolygonNodeLocalization.y
    (by simpa only [map_zero] using PolygonNodeLocalization.x_mul_y (R := R))

/-- Evaluate the two existing branches at the actual product-zero coordinates. -/
def fromPolygonNode : A (R := R) →ₐ[R] Coordinate (0 : R) :=
  PolygonNodeEvaluation.evaluation (p 0) (q 0) (by simpa using relation (0 : R))

/-- The first tangent coordinate is the first branch coordinate. -/
@[simp] theorem toPolygonNode_p : toPolygonNode (p (0 : R)) = PolygonNodeLocalization.x :=
  evaluation_p _ _ _ _

/-- The second tangent coordinate is the second branch coordinate. -/
@[simp] theorem toPolygonNode_q : toPolygonNode (q (0 : R)) = PolygonNodeLocalization.y :=
  evaluation_q _ _ _ _

/-- The first polynomial-pair generator returns to its actual tangent coordinate. -/
@[simp] theorem fromPolygonNode_x :
    fromPolygonNode (PolygonNodeLocalization.x (R := R)) = p 0 :=
  PolygonNodeEvaluation.evaluation_x _ _ _

/-- The second polynomial-pair generator returns to its actual tangent coordinate. -/
@[simp] theorem fromPolygonNode_y :
    fromPolygonNode (PolygonNodeLocalization.y (R := R)) = q 0 :=
  PolygonNodeEvaluation.evaluation_y _ _ _

/-- The explicit two-branch node is the entire product-zero coordinate algebra. -/
def polygonNodeEquiv : Coordinate (0 : R) ≃ₐ[R] A (R := R) := by
  apply AlgEquiv.ofAlgHom toPolygonNode fromPolygonNode
  · apply AlgHom.ext
    intro z
    change toPolygonNode (fromPolygonNode z) = z
    rw [fromPolygonNode, PolygonNodeEvaluation.evaluation_apply, map_sub, map_add,
      ← aeval_algHom_apply, ← aeval_algHom_apply, AlgHom.commutes,
      toPolygonNode_p, toPolygonNode_q]
    exact PolygonNodeScalarExtension.reconstruct z
  · apply hom_ext <;> simp

/-- The actual comparison retains the first tangent orientation. -/
@[simp] theorem polygonNodeEquiv_p :
    polygonNodeEquiv (p (0 : R)) = PolygonNodeLocalization.x := toPolygonNode_p

/-- The actual comparison retains the second tangent orientation. -/
@[simp] theorem polygonNodeEquiv_q :
    polygonNodeEquiv (q (0 : R)) = PolygonNodeLocalization.y := toPolygonNode_q

end FLT.Mazur.NodalFiber
