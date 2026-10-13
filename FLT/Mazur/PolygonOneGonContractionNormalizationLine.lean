/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionMarkingSection
public import FLT.Mazur.DivisorLineSectionTriangle
public import FLT.Mazur.PolygonNormalizationSectionCompatibility

/-!
# Retained normalization coherence of the actual contraction line

The canonical marking-line comparison restricts on the retained original
normalization component to the target one-gon normalization comparison.
The equality holds for actual line isomorphisms and all tensor powers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction tensorPowerPullbackComparison ownComponentIso
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

omit [NeZero n] in
/-- The actual retained normalization map factors through the original contraction. -/
theorem retained_contraction_left :
    (componentι K n i ≫ p).left ≫ (contraction K n hn p q h i).left =
      (retainedComponent K).left :=
  congrArg Over.Hom.left (retained_contraction K n hn p q h i)

/-- The actual marking-line contraction comparison agrees with retained normalization. -/
theorem markingLineIso_normalization (a : Kˣ) :
    LinePullbackTriangle (componentι K n i ≫ p).left
      (contraction K n hn p q h i).left (retainedComponent K).left
      (retained_contraction_left K n hn p q h i)
      (markingLineIso K n hn p q h i a) (ownComponentIso K n hn p q h a i)
      (ownComponentIso K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (markingLineIso_section K n hn p q h i a)
    (ownComponentIso_compatible K n hn p q h a i)
    (ownComponentIso_compatible K 1 (by decide) (PolygonAtlas.normalization K 1)
      (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0)

/-- Retained normalization and contraction agree on every actual marking-line tensor power. -/
theorem markingLineIso_normalization_power (a : Kˣ) (d : ℕ) :
    LinePullbackTriangle (componentι K n i ≫ p).left
      (contraction K n hn p q h i).left (retainedComponent K).left
      (retained_contraction_left K n hn p q h i)
      (tensorPowerPullbackComparison _ (markingLineIso K n hn p q h i a) d)
      (tensorPowerPullbackComparison _ (ownComponentIso K n hn p q h a i) d)
      (tensorPowerPullbackComparison _ (ownComponentIso K 1 (by decide)
        (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
        (PolygonAtlas.isPushout K 1 (by decide)) a 0) d) :=
  (markingLineIso_normalization K n hn p q h i a).tensorPower d

end FLT.Mazur.PolygonOneGonContraction
