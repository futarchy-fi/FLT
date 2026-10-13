/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# The translation marking comparison is the scalar-rotation composite

The direct Cartier pullback comparison agrees with the two successive
comparisons, including the pullback compositor, in every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonScaling polygonRotation
  PolygonActionTranslation.translation tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The universal action specialization equals scalar multiplication followed by rotation. -/
theorem scaling_rotation_translation_left (c : Kˣ) (b : ZMod n) :
    (polygonScaling K hn p q h c).left ≫ (polygonRotation K hn p q h b).left =
      (PolygonActionTranslation.translation K n hn p q h c b).left :=
  congrArg Over.Hom.left (PolygonActionTranslation.translation_eq K n hn p q h c b).symm

/-- The direct translation comparison is the actual composite of scalar and cyclic ones. -/
theorem translationLineIso_scaling_rotation (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) :
    LinePullbackTriangle (polygonScaling K hn p q h c).left
      (polygonRotation K hn p q h b).left
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (scaling_rotation_translation_left K n hn p q h c b)
      (rotationLineIso K n hn p q h b (c * a) i)
      (scalingLineIso K n hn p q h c a i) (translationLineIso K n hn p q h c b a i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (rotationLineIso_section K n hn p q h b (c * a) i)
    (scalingLineIso_section K n hn p q h c a i)
    (translationLineIso_section K n hn p q h c b a i)

/-- The translation decomposition retains every actual marking-line tensor power. -/
theorem translationLineIso_scaling_rotation_power
    (c : Kˣ) (b : ZMod n) (a : Kˣ) (i : Fin n) (d : ℕ) :
    LinePullbackTriangle (polygonScaling K hn p q h c).left
      (polygonRotation K hn p q h b).left
      (PolygonActionTranslation.translation K n hn p q h c b).left
      (scaling_rotation_translation_left K n hn p q h c b)
      (tensorPowerPullbackComparison _ (rotationLineIso K n hn p q h b (c * a) i) d)
      (tensorPowerPullbackComparison _ (scalingLineIso K n hn p q h c a i) d)
      (tensorPowerPullbackComparison _ (translationLineIso K n hn p q h c b a i) d) :=
  (translationLineIso_scaling_rotation K n hn p q h c b a i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
