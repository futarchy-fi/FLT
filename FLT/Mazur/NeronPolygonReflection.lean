/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CyclicPinchingReflection
public import FLT.Mazur.NeronPolygonPredicate

/-!
# The reflection automorphism of a realized polygon

The reflected pinching span descends through the actual pushout. The resulting
involution preserves the original markings, reverses the cyclic orientation,
and fixes the identity component while inverting its projective coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] {n : ℕ} [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "r" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

/-- Descend reflection of the original normalization and node coproducts. -/
def polygonReflection : C ⟶ C :=
  h.desc (componentsReflection K ≫ p) (nodesReflection K ≫ q) (by
    rw [← Category.assoc, ← reflection_toComponents, Category.assoc, h.w,
      ← Category.assoc, reflection_toNodes, Category.assoc])

/-- Reflection keeps the entire original normalization with its reversed coordinates. -/
@[reassoc (attr := simp)] theorem components_polygonReflection :
    p ≫ polygonReflection K hn p q h = componentsReflection K ≫ p := by
  simp [polygonReflection]

/-- Reflection keeps the entire original node coproduct with its reflected indices. -/
@[reassoc (attr := simp)] theorem nodes_polygonReflection :
    q ≫ polygonReflection K hn p q h = nodesReflection K ≫ q := by
  simp [polygonReflection]

/-- Each complete component has its index negated and its two endpoints exchanged. -/
@[reassoc] theorem componentι_polygonReflection (i : Fin n) :
    componentι K n i ≫ p ≫ polygonReflection K hn p q h =
      r ≫ componentι K n (reflectIndex i) ≫ p := by simp

/-- Each node has the original reflected incidence index. -/
@[reassoc] theorem nodeι_polygonReflection (i : Fin n) :
    nodeι K n i ≫ q ≫ polygonReflection K hn p q h =
      nodeι K n (reflectNodeIndex i) ≫ q := by simp

/-- The whole descended reflection is involutive, including all pinched nodes. -/
@[reassoc] theorem polygonReflection_involutive :
    polygonReflection K hn p q h ≫ polygonReflection K hn p q h = 𝟙 C := by
  apply h.hom_ext
  · simp only [components_polygonReflection_assoc, components_polygonReflection,
      componentsReflection_involutive_assoc, Category.comp_id]
  · simp only [nodes_polygonReflection_assoc, nodes_polygonReflection,
      nodesReflection_involutive_assoc, Category.comp_id]

/-- The original realized polygon carries its marked reflection automorphism. -/
def polygonReflectionIso : C ≅ C where
  hom := polygonReflection K hn p q h
  inv := polygonReflection K hn p q h
  hom_inv_id := polygonReflection_involutive K hn p q h
  inv_hom_id := polygonReflection_involutive K hn p q h

/-- The component of the identity is preserved with its original coordinate inverted. -/
theorem component_zero_polygonReflection :
    componentι K n 0 ≫ p ≫ polygonReflection K hn p q h =
      r ≫ componentι K n 0 ≫ p := by
  rw [componentι_polygonReflection, reflectIndex_zero]

end FLT.Mazur.PolygonPinching
