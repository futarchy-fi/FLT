/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionMarkingLine
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# The actual retained Cartier line under polygon contraction

The full positive divisor line pulls back canonically along the non-flat
contraction. The comparison preserves its original vanishing section; it
uses the proved Cartier inverse image, without imposing a flatness hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- The original canonical vanishing section is preserved by the full contraction comparison. -/
theorem markingLineIso_section (a : Kˣ) :
    DivisorLineSectionCompatible (contraction K n hn p q h i).left
      (section_cartier K 1 (PolygonAtlas.normalization K 1) (by decide)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0).1
      (section_cartier K n p hn q h a i).1 (markingLineIso K n hn p q h i a) := by
  let _ := markingIdealComparison_isIso K n hn p q h i a
  rw [markingLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonOneGonContraction
