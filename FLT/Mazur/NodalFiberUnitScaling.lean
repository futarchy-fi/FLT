/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberSmoothingComparison

/-!
# Explicit unit scaling of a full node

A unit multiplying the smoothing parameter is absorbed in the first coordinate.
Both directions retain the second coordinate and the entire nonreduced node.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (c t : R) (u : Rˣ) (hc : c = t * ↑u)

/-- A specified scalar comparison of product constants scales the first generator. -/
def scalarNodeMap (c d a : R) (ha : a * d = c) : Coordinate c →ₐ[R] Coordinate d :=
  evaluation c (algebraMap R (Coordinate d) a * p d) (q d) (by
    rw [mul_assoc, relation, ← map_mul, ha])

@[simp] theorem scalarNodeMap_p (c d a : R) (ha : a * d = c) :
    scalarNodeMap c d a ha (p c) = algebraMap R (Coordinate d) a * p d := evaluation_p ..

@[simp] theorem scalarNodeMap_q (c d a : R) (ha : a * d = c) :
    scalarNodeMap c d a ha (q c) = q d := evaluation_q ..

attribute [local irreducible] scalarNodeMap

/-- Scale the first factor to turn product t into product t*u. -/
def scaleToNode : Coordinate c →ₐ[R] Coordinate t :=
  scalarNodeMap c t (↑u : R) ((mul_comm _ _).trans hc.symm)

/-- The inverse scaling divides the first factor by the specified unit. -/
def scaleFromNode : Coordinate t →ₐ[R] Coordinate c :=
  scalarNodeMap t c (↑u⁻¹ : R) (by
    rw [hc]
    rw [mul_left_comm, Units.inv_mul, mul_one])

@[simp] theorem scaleToNode_p :
    scaleToNode c t u hc (p c) = algebraMap R (Coordinate t) (↑u : R) * p t :=
  scalarNodeMap_p ..

@[simp] theorem scaleToNode_q : scaleToNode c t u hc (q c) = q t := scalarNodeMap_q ..

@[simp] theorem scaleFromNode_p :
    scaleFromNode c t u hc (p t) = algebraMap R (Coordinate c) (↑u⁻¹ : R) * p c :=
  scalarNodeMap_p ..

@[simp] theorem scaleFromNode_q : scaleFromNode c t u hc (q t) = q c := scalarNodeMap_q ..

/-- An actual unit factor gives an isomorphism of the full smoothing nodes. -/
def unitScaleEquiv : Coordinate c ≃ₐ[R] Coordinate t := by
  apply AlgEquiv.ofAlgHom (scaleToNode c t u hc) (scaleFromNode c t u hc)
  · apply hom_ext
    · simp only [AlgHom.comp_apply, scaleFromNode_p, map_mul, AlgHom.commutes,
        scaleToNode_p, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · simp
  · apply hom_ext
    · simp only [AlgHom.comp_apply, scaleToNode_p, map_mul, AlgHom.commutes,
        scaleFromNode_p, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    · simp

/-- The full unit-scaled node has the polygon's specified smoothing parameter. -/
def unitSmoothingEquiv : Coordinate c ≃ₐ[R] PolygonSmoothing.ChartRing t :=
  (unitScaleEquiv c t u hc).trans (smoothingEquiv t)

/-- The original first node coordinate includes exactly the specified unit correction. -/
@[simp] theorem unitSmoothingEquiv_p :
    unitSmoothingEquiv c t u hc (p c) =
      algebraMap R _ (↑u : R) * PolygonSmoothing.leftCoordinate t := by
  change toSmoothing t (scaleToNode c t u hc _) = _
  rw [scaleToNode_p, map_mul, AlgHom.commutes, toSmoothing_p]

/-- The second coordinate survives the parameter normalization unchanged. -/
@[simp] theorem unitSmoothingEquiv_q :
    unitSmoothingEquiv c t u hc (q c) = PolygonSmoothing.rightCoordinate t := by
  change toSmoothing t (scaleToNode c t u hc _) = _
  rw [scaleToNode_q, toSmoothing_q]

end FLT.Mazur.NodalFiber
