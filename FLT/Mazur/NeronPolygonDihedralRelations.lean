/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NeronPolygonReflection
public import FLT.Mazur.NeronPolygonRotationAction

/-!
# Reflection conjugates the original polygon rotations to their inverses

The relation holds on the original normalization coordinates and node labels,
and therefore on the entire realized polygon. This supplies the finite-index
part of the orientation reversal required for nonsplit descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {n : ℕ} [NeZero n]

/-- Reflection reverses cyclic translation on the original component indices. -/
theorem reflectIndex_rotateIndex (a : ZMod n) (i : Fin n) :
    reflectIndex (rotateIndex a i) = rotateIndex (-a) (reflectIndex i) := by
  apply (ZMod.finEquiv n).injective
  simp [reflectIndex, rotateIndex, add_comm]

/-- The same reversed translation retains the original reflected node indexing. -/
theorem reflectNodeIndex_rotateIndex (a : ZMod n) (i : Fin n) :
    reflectNodeIndex (rotateIndex a i) = rotateIndex (-a) (reflectNodeIndex i) := by
  apply (ZMod.finEquiv n).injective
  simp [reflectNodeIndex, rotateIndex, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

variable (K : Type u) [Field K]

/-- Reversing the normalization conjugates rotation, including every projective coordinate. -/
theorem componentsRotation_reflection (a : ZMod n) :
    componentsRotation K a ≫ componentsReflection K =
      componentsReflection K ≫ componentsRotation K (-a) := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp [reflectIndex_rotateIndex]

/-- Reversing the node coproduct conjugates its original rotation. -/
theorem nodesRotation_reflection (a : ZMod n) :
    nodesRotation K a ≫ nodesReflection K = nodesReflection K ≫ nodesRotation K (-a) := by
  apply Sigma.hom_ext
  intro i
  change nodeι K n i ≫ _ = nodeι K n i ≫ _
  simp [reflectNodeIndex_rotateIndex]

variable (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The whole marked polygon satisfies the dihedral reflection-rotation relation. -/
theorem polygonRotation_reflection (a : ZMod n) :
    polygonRotation K hn p q h a ≫ polygonReflection K hn p q h =
      polygonReflection K hn p q h ≫ polygonRotation K hn p q h (-a) := by
  apply h.hom_ext
  · simp only [components_polygonRotation_assoc, components_polygonReflection,
      components_polygonReflection_assoc, components_polygonRotation]
    rw [← Category.assoc, ← Category.assoc, componentsRotation_reflection]
  · simp only [nodes_polygonRotation_assoc, nodes_polygonReflection,
      nodes_polygonReflection_assoc, nodes_polygonRotation]
    rw [← Category.assoc, ← Category.assoc, nodesRotation_reflection]

/-- Conjugating a whole-polygon rotation by reflection gives its inverse rotation. -/
theorem polygonReflection_conjugate_rotation (a : ZMod n) :
    polygonReflection K hn p q h ≫ polygonRotation K hn p q h a ≫
        polygonReflection K hn p q h = polygonRotation K hn p q h (-a) := by
  rw [polygonRotation_reflection, polygonReflection_involutive_assoc]

end FLT.Mazur.PolygonPinching
