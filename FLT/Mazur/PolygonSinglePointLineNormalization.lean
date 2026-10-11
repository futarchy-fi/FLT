/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonDivisorNormalizationPullback
public import FLT.Mazur.ProjectiveLineMarkedCharts
public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.DivisorCanonicalOperations

/-!
# Normalization of a single marked polygon line

The line of one original smooth marking restricts to O(P) on its own component
and to the canonically trivial line on every other component. Both comparisons
preserve the original divisor section. These are the coefficients needed for
the single-point normalization sequence, not the sum of all marked points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonSinglePointLineNormalization

open FCurve PolygonPinching PolygonMarkedSections PolygonDivisorNormalizationPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual positive line of one original polygon marking. -/
def pointLine (a : Kˣ) (j : Fin n) : C.left.Modules :=
  divisorLineBundle (sectionMap K n p a j).ker (section_cartier K n p hn q h a j).1

include h in
/-- Each component has an invertible canonical ideal comparison for the single point. -/
theorem pointIdealComparison_isIso (a : Kˣ) (i j : Fin n) :
    IsIso (idealModulePullbackHom (sectionMap K n p a j).ker (componentι K n i ≫ p).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (section_cartier K n p hn q h a j).1
  by_cases hij : i = j
  · subst j
    rw [section_ideal K n hn p q h a i]
    exact (ProjectiveLineMarkedCharts.relativeCartier K a).1
  · rw [other_section_ideal K n hn p q h a hij]
    exact effectiveCartier_top

/-- On its own normalization component the original point line is O(P). -/
def ownComponentIso (a : Kˣ) (j : Fin n) :
    (Scheme.Modules.pullback (componentι K n j ≫ p).left).obj (pointLine K n hn p q h a j) ≅
      divisorLineBundle (markedPoint K a).ker
        (ProjectiveLineMarkedCharts.relativeCartier K a).1 := by
  let _ := pointIdealComparison_isIso K n hn p q h a j j
  exact divisorLinePullbackIsoOfEq _ (section_cartier K n p hn q h a j).1
    (ProjectiveLineMarkedCharts.relativeCartier K a).1 (section_ideal K n hn p q h a j)

/-- The comparison on the marked component retains the canonical vanishing section. -/
@[reassoc] theorem ownComponentIso_section (a : Kˣ) (j : Fin n) :
    (Scheme.Modules.pullback (componentι K n j ≫ p).left).map
        (divisorSectionMap (section_cartier K n p hn q h a j).1) ≫
      (ownComponentIso K n hn p q h a j).hom =
        (modulePullbackUnitIso (componentι K n j ≫ p).left).hom ≫
          divisorSectionMap (ProjectiveLineMarkedCharts.relativeCartier K a).1 := by
  let _ := pointIdealComparison_isIso K n hn p q h a j j
  exact divisorLinePullbackIsoOfEq_section _ (section_cartier K n p hn q h a j).1
    (ProjectiveLineMarkedCharts.relativeCartier K a).1 (section_ideal K n hn p q h a j)

/-- Every other normalization component has its canonical trivialization. -/
def otherComponentIso (a : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj (pointLine K n hn p q h a j) ≅
      structureModule (ProjectiveLine.scheme K) := by
  let _ := pointIdealComparison_isIso K n hn p q h a i j
  exact divisorLinePullbackIsoOfEq _ (section_cartier K n p hn q h a j).1
    effectiveCartier_top (other_section_ideal K n hn p q h a hij) ≪≫
      divisorLineBundleTopIso effectiveCartier_top

/-- Off the marked component the original section becomes the unit section map. -/
@[reassoc] theorem otherComponentIso_section (a : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).map
        (divisorSectionMap (section_cartier K n p hn q h a j).1) ≫
      (otherComponentIso K n hn p q h a hij).hom =
        (modulePullbackUnitIso (componentι K n i ≫ p).left).hom := by
  let _ := pointIdealComparison_isIso K n hn p q h a i j
  change _ ≫ (divisorLinePullbackIsoOfEq _ _ _ _).hom ≫
    (divisorLineBundleTopIso effectiveCartier_top).hom = _
  rw [← Category.assoc, divisorLinePullbackIsoOfEq_section, Category.assoc,
    divisorSection_top_map, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.PolygonSinglePointLineNormalization
