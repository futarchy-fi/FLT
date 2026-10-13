/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContraction
public import FLT.Mazur.NeronPolygonDihedralRelations

/-!
# Rotation and reflection coherence of the original contraction

Rotating the retained component leaves the target contraction unchanged.
Reflecting it induces the original reflection of the one-gon. These are
identities on the complete pinched schemes, retaining every original node.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The reflection on the actual standard target one-gon. -/
abbrev targetReflection : PolygonAtlas.polygon K 1 ⟶ PolygonAtlas.polygon K 1 :=
  polygonReflection K (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide))

/-- The target reflection retains its original normalization coordinate reversal. -/
@[reassoc] theorem retainedComponent_reflection :
    retainedComponent K ≫ targetReflection K =
      (ProjectiveLine.endpointReversalOverIso K).hom ≫ retainedComponent K := by
  change (componentι K 1 0 ≫ PolygonAtlas.normalization K 1) ≫ _ = _
  rw [Category.assoc, componentι_polygonReflection, reflectIndex_zero]
  rfl

/-- The original target node is fixed as a morphism, not merely as a geometric point. -/
@[reassoc] theorem targetNode_reflection : targetNode K ≫ targetReflection K = targetNode K := by
  change (nodeι K 1 0 ≫ PolygonAtlas.nodes K 1) ≫ _ = _
  rw [Category.assoc, nodeι_polygonReflection]
  have he : reflectNodeIndex (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [he]
  rfl

/-- Coordinate reversal does not alter the coefficient map of a collapsed component. -/
@[reassoc] theorem reversal_componentToPoint :
    (ProjectiveLine.endpointReversalOverIso K).hom ≫ componentToPoint K =
      componentToPoint K := by
  apply Over.OverMorphism.ext
  exact (ProjectiveLine.endpointReversalOverIso K).hom.w

variable (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- Rotation transports the retained component with the original contraction unchanged. -/
@[reassoc] theorem rotation_contraction (b : ZMod n) :
    polygonRotation K hn p q h b ≫ contraction K n hn p q h (rotateIndex b i) =
      contraction K n hn p q h i := by
  apply h.hom_ext
  · apply Sigma.hom_ext
    intro j
    change componentι K n j ≫ p ≫ _ = componentι K n j ≫ p ≫ _
    rw [componentι_polygonRotation_assoc]
    by_cases hj : j = i
    · subst j
      rw [retained_contraction, retained_contraction]
    · have hij : rotateIndex b j ≠ rotateIndex b i := by
        intro he
        apply hj
        apply (ZMod.finEquiv n).injective
        have he' := congrArg (ZMod.finEquiv n) he
        simpa only [rotateIndex, RingEquiv.apply_symm_apply, add_right_cancel_iff] using he'
      rw [omitted_contraction K n hn p q h _ hij, omitted_contraction K n hn p q h i hj]
  · apply Sigma.hom_ext
    intro j
    change nodeι K n j ≫ q ≫ _ = nodeι K n j ≫ q ≫ _
    rw [nodeι_polygonRotation_assoc, node_contraction, node_contraction]

/-- Reflecting the retained component induces the actual reflection of the target one-gon. -/
@[reassoc] theorem reflection_contraction :
    polygonReflection K hn p q h ≫ contraction K n hn p q h (reflectIndex i) =
      contraction K n hn p q h i ≫ targetReflection K := by
  apply h.hom_ext
  · apply Sigma.hom_ext
    intro j
    change componentι K n j ≫ p ≫ _ = componentι K n j ≫ p ≫ _
    rw [componentι_polygonReflection_assoc]
    by_cases hj : j = i
    · subst j
      rw [retained_contraction, retained_contraction_assoc, retainedComponent_reflection]
    · have hij : reflectIndex j ≠ reflectIndex i := by
        intro he
        have he' := congrArg reflectIndex he
        exact hj (by simpa only [reflectIndex_reflectIndex] using he')
      rw [omitted_contraction K n hn p q h _ hij,
        omitted_contraction_assoc K n hn p q h i hj,
        targetNode_reflection, reversal_componentToPoint_assoc]
  · apply Sigma.hom_ext
    intro j
    change nodeι K n j ≫ q ≫ _ = nodeι K n j ≫ q ≫ _
    rw [nodeι_polygonReflection_assoc, node_contraction, node_contraction_assoc,
      targetNode_reflection]

end FLT.Mazur.PolygonOneGonContraction
