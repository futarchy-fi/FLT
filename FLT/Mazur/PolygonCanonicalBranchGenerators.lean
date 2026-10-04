/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleComparedSectionRatio
public import FLT.Mazur.ProjectiveLineRightCanonicalRatios
public import FLT.Mazur.PolygonCubicTorusRatios

/-!
# Canonical generators on both normalization branches

The canonical cubic section generates after restriction to either affine
normalization chart with its marked point removed. Both maps are the actual
composites through the supplied polygon normalization.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveLineMarkedHZero
open ProjectiveLineMarkedSectionTransition
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The canonical section is preserved by the actual component-section comparison. -/
lemma componentSection_canonical (i : Fin n) :
    componentSection K n hn p q h a
      (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤) i =
        divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow 3) ⊤ :=
  PolygonDirectPowerComparison.lineIso_section K n hn p q h a i 3

/-- The punctured affine normalization branch, with its node endpoint retained. -/
irreducible_def canonicalLeftBranch (i : Fin n) :
    Spec (.of (ProjectiveLineCanonicalRatios.ring K (a i))) ⟶ C.left :=
  (ProjectiveLineCanonicalRatios.toLine K (a i)) ≫
    (componentι K n i ≫ p).left

/-- The actual canonical section generates after pullback to this normalization branch. -/
lemma canonicalSection_isIso_leftBranch (i : Fin n) :
    IsIso (globalSectionHom _ (pullGlobal (canonicalLeftBranch K n p a i)
      (polygonLine K n hn p q h a 3)
      (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤))) := by
  rw [canonicalLeftBranch_def]
  have hc := ProjectiveLineCanonicalRatios.toLine_canonical_isIso K (a i) 3
  exact comparedSection_isIso _ _ _ _
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3) _ _
    (componentSection_canonical K n hn p q h a i)

/-- The right normalization branch minus its reciprocal marked point. -/
irreducible_def canonicalRightBranch (i : Fin n) :
    Spec (.of (ProjectiveLineCanonicalRatios.ring K (a i)⁻¹)) ⟶ C.left :=
  (ProjectiveLineRightCanonicalRatios.toLine K (a i)) ≫
    (componentι K n i ≫ p).left

/-- The actual canonical section generates on the right normalization branch. -/
lemma canonicalSection_isIso_rightBranch (i : Fin n) :
    IsIso (globalSectionHom _ (pullGlobal (canonicalRightBranch K n p a i)
      (polygonLine K n hn p q h a 3)
      (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow 3) ⊤))) := by
  rw [canonicalRightBranch_def]
  have hc := ProjectiveLineRightCanonicalRatios.toLine_canonical_isIso K (a i) 3
  exact comparedSection_isIso _ _ _ _
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3) _ _
    (componentSection_canonical K n hn p q h a i)

end FLT.Mazur.PolygonCubicSections
