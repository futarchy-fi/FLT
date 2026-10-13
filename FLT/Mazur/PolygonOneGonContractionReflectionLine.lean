/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionMarkingSection
public import FLT.Mazur.PolygonOneGonContractionSymmetry
public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.DivisorLineSectionSquare

/-!
# Reflection coherence of the actual contraction marking line

The canonical contraction and reflection comparisons commute on the actual
positive marking lines. Both sides retain the original vanishing section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction polygonReflection
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- The original reflection-contraction square on underlying complete schemes. -/
theorem reflection_contraction_left :
    (polygonReflection K hn p q h).left ≫ (contraction K n hn p q h (reflectIndex i)).left =
      (contraction K n hn p q h i).left ≫ (targetReflection K).left :=
  congrArg Over.Hom.left (reflection_contraction K n hn p q h i)

/-- The actual marking-line comparisons commute with the full-curve reflection square. -/
theorem markingLineIso_reflection (a : Kˣ) :
    LinePullbackSquare (polygonReflection K hn p q h).left
      (contraction K n hn p q h (reflectIndex i)).left
      (contraction K n hn p q h i).left (targetReflection K).left
      (reflection_contraction_left K n hn p q h i)
      (markingLineIso K n hn p q h (reflectIndex i) a⁻¹)
      (reflectionLineIso K n hn p q h a i)
      (reflectionLineIso K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0)
      (markingLineIso K n hn p q h i a) := by
  exact divisorLineSectionCompatible_square _ _ _ _ _
    (markingLineIso_section K n hn p q h (reflectIndex i) a⁻¹)
    (reflectionLineIso_section K n hn p q h a i)
    (reflectionLineIso_section K 1 (by decide) (PolygonAtlas.normalization K 1)
      (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0)
    (markingLineIso_section K n hn p q h i a)

end FLT.Mazur.PolygonOneGonContraction
