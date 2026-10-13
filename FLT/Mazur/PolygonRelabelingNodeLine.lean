/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.PolygonMarkingNodeLine
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# Relabeling coherence at every original polygon node

The canonical empty-divisor comparisons at nodes commute with the actual
full-polygon scalar, cyclic, translation and reflection comparisons.
Every equation propagates to all tensor powers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonScaling polygonRotation
  polygonReflection PolygonActionTranslation.translation tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

omit [NeZero n] in
/-- The original scaling identifies the underlying node maps. -/
theorem node_scaling_left (c : Kˣ) (i : Fin n) :
    (nodeι K n i ≫ q).left ≫ (polygonScaling K hn p q h c).left =
      (nodeι K n (i) ≫ q).left :=
  congrArg Over.Hom.left (nodeι_polygonScaling K hn p q h c i)

/-- The original scaling comparison preserves the canonical frame at each node. -/
theorem scalingLineIso_node (c : Kˣ) (a : Kˣ) (j i : Fin n) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (polygonScaling K hn p q h c).left (nodeι K n (i) ≫ q).left
      (node_scaling_left K n hn p q h c i)
      (scalingLineIso K n hn p q h c a j) (nodeLineIso K n hn p q h a j i)
      (nodeLineIso K n hn p q h (c * a) (j) (i)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (scalingLineIso_section K n hn p q h c a j)
    (nodeLineIso_section K n hn p q h a j i)
    (nodeLineIso_section K n hn p q h (c * a) (j) (i))

/-- All tensor powers retain the same scaling equation in the original node frames. -/
theorem scalingLineIso_node_power (c : Kˣ) (a : Kˣ) (j i : Fin n) (d : ℕ) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (polygonScaling K hn p q h c).left (nodeι K n (i) ≫ q).left
      (node_scaling_left K n hn p q h c i)
      (tensorPowerPullbackComparison _ (scalingLineIso K n hn p q h c a j) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (nodeLineIso K n hn p q h (c * a) (j) (i)) d) :=
  (scalingLineIso_node K n hn p q h c a j i).tensorPower d

/-- The original rotation identifies the underlying node maps. -/
theorem node_rotation_left (b : ZMod n) (i : Fin n) :
    (nodeι K n i ≫ q).left ≫ (polygonRotation K hn p q h b).left =
      (nodeι K n (rotateIndex b i) ≫ q).left :=
  congrArg Over.Hom.left (nodeι_polygonRotation K hn p q h b i)

/-- The original rotation comparison preserves the canonical frame at each node. -/
theorem rotationLineIso_node (b : ZMod n) (a : Kˣ) (j i : Fin n) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (polygonRotation K hn p q h b).left (nodeι K n (rotateIndex b i) ≫ q).left
      (node_rotation_left K n hn p q h b i)
      (rotationLineIso K n hn p q h b a j) (nodeLineIso K n hn p q h a j i)
      (nodeLineIso K n hn p q h (a) (rotateIndex b j) (rotateIndex b i)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (rotationLineIso_section K n hn p q h b a j)
    (nodeLineIso_section K n hn p q h a j i)
    (nodeLineIso_section K n hn p q h (a) (rotateIndex b j) (rotateIndex b i))

/-- All tensor powers retain the same rotation equation in the original node frames. -/
theorem rotationLineIso_node_power (b : ZMod n) (a : Kˣ) (j i : Fin n) (d : ℕ) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (polygonRotation K hn p q h b).left (nodeι K n (rotateIndex b i) ≫ q).left
      (node_rotation_left K n hn p q h b i)
      (tensorPowerPullbackComparison _ (rotationLineIso K n hn p q h b a j) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (nodeLineIso K n hn p q h (a) (rotateIndex b j) (rotateIndex b i)) d) :=
  (rotationLineIso_node K n hn p q h b a j i).tensorPower d

/-- The original translation identifies the underlying node maps. -/
theorem node_translation_left (c : Kˣ) (b : ZMod n) (i : Fin n) :
    (nodeι K n i ≫ q).left ≫ (PolygonActionTranslation.translation K n hn p q h c b).left =
      (nodeι K n (rotateIndex b i) ≫ q).left :=
  congrArg Over.Hom.left (PolygonActionTranslation.node_translation K n hn p q h c b i)

/-- The original translation comparison preserves the canonical frame at each node. -/
theorem translationLineIso_node (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (nodeι K n (rotateIndex b i) ≫ q).left
      (node_translation_left K n hn p q h c b i)
      (translationLineIso K n hn p q h c b a j) (nodeLineIso K n hn p q h a j i)
      (nodeLineIso K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (translationLineIso_section K n hn p q h c b a j)
    (nodeLineIso_section K n hn p q h a j i)
    (nodeLineIso_section K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i))

/-- All tensor powers retain the same translation equation in the original node frames. -/
theorem translationLineIso_node_power (c : Kˣ) (b : ZMod n) (a : Kˣ) (j i : Fin n) (d : ℕ) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (nodeι K n (rotateIndex b i) ≫ q).left
      (node_translation_left K n hn p q h c b i)
      (tensorPowerPullbackComparison _ (translationLineIso K n hn p q h c b a j) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (nodeLineIso K n hn p q h (c * a) (rotateIndex b j) (rotateIndex b i)) d) :=
  (translationLineIso_node K n hn p q h c b a j i).tensorPower d

/-- The original reflection identifies the underlying node maps. -/
theorem node_reflection_left (i : Fin n) :
    (nodeι K n i ≫ q).left ≫ (polygonReflection K hn p q h).left =
      (nodeι K n (reflectNodeIndex i) ≫ q).left :=
  congrArg Over.Hom.left (nodeι_polygonReflection K hn p q h i)

/-- The original reflection comparison preserves the canonical frame at each node. -/
theorem reflectionLineIso_node (a : Kˣ) (j i : Fin n) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (polygonReflection K hn p q h).left (nodeι K n (reflectNodeIndex i) ≫ q).left
      (node_reflection_left K n hn p q h i)
      (reflectionLineIso K n hn p q h a j) (nodeLineIso K n hn p q h a j i)
      (nodeLineIso K n hn p q h (a⁻¹) (reflectIndex j) (reflectNodeIndex i)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (reflectionLineIso_section K n hn p q h a j)
    (nodeLineIso_section K n hn p q h a j i)
    (nodeLineIso_section K n hn p q h (a⁻¹) (reflectIndex j) (reflectNodeIndex i))

/-- All tensor powers retain the same reflection equation in the original node frames. -/
theorem reflectionLineIso_node_power (a : Kˣ) (j i : Fin n) (d : ℕ) :
    LinePullbackTriangle (nodeι K n i ≫ q).left
      (polygonReflection K hn p q h).left (nodeι K n (reflectNodeIndex i) ≫ q).left
      (node_reflection_left K n hn p q h i)
      (tensorPowerPullbackComparison _ (reflectionLineIso K n hn p q h a j) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (nodeLineIso K n hn p q h (a⁻¹) (reflectIndex j) (reflectNodeIndex i)) d) :=
  (reflectionLineIso_node K n hn p q h a j i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
