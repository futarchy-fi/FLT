/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationSectionCompatibility
public import FLT.Mazur.DivisorLineSectionIdealTransport
public import FLT.Mazur.DivisorLineSectionComposition

/-!
# Uniform canonical comparisons on every normalization component

The pulled marking ideal is Cartier on every original projective component.
Its canonical line comparison recovers both the marked O(P) comparison and
the empty-divisor comparison on every unmarked component.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonSinglePointLineNormalization
open PolygonPinching PolygonMarkedSections PolygonDivisorNormalizationPullback FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq ownComponentIso
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- Every original normalization component retains a Cartier marking ideal. -/
theorem normalizationIdeal_cartier (a : Kˣ) (j i : Fin n) :
    EffectiveCartier ((sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left) := by
  by_cases hij : i = j
  · subst i
    rw [section_ideal K n hn p q h a j]
    exact (ProjectiveLineMarkedCharts.relativeCartier K a).1
  · rw [other_section_ideal K n hn p q h a hij]
    exact effectiveCartier_top

/-- The comparison with the actual pulled marking ideal, uniform in the component label. -/
irreducible_def normalizationLineIso (a : Kˣ) (j i : Fin n) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj (pointLine K n hn p q h a j) ≅
      divisorLineBundle _ (normalizationIdeal_cartier K n hn p q h a j i) := by
  let _ := pointIdealComparison_isIso K n hn p q h a i j
  exact divisorLinePullbackIsoOfEq _ (section_cartier K n p hn q h a j).1
    (normalizationIdeal_cartier K n hn p q h a j i) rfl

/-- Every component comparison preserves the original canonical section. -/
theorem normalizationLineIso_section (a : Kˣ) (j i : Fin n) :
    DivisorLineSectionCompatible (componentι K n i ≫ p).left
      (section_cartier K n p hn q h a j).1
      (normalizationIdeal_cartier K n hn p q h a j i)
      (normalizationLineIso K n hn p q h a j i) := by
  let _ := pointIdealComparison_isIso K n hn p q h a i j
  rw [normalizationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- On the marked component the uniform comparison is the original O(P) comparison. -/
theorem normalizationLineIso_own (a : Kˣ) (j : Fin n) :
    normalizationLineIso K n hn p q h a j j ≪≫
      divisorLineBundleEqIso (section_ideal K n hn p q h a j)
        (normalizationIdeal_cartier K n hn p q h a j j)
        (ProjectiveLineMarkedCharts.relativeCartier K a).1 =
          ownComponentIso K n hn p q h a j :=
  ((normalizationLineIso_section K n hn p q h a j j).targetIdealEq
    (section_ideal K n hn p q h a j)).ext (ownComponentIso_compatible K n hn p q h a j)

/-- On an unmarked component the uniform comparison gives the original unit frame. -/
theorem normalizationLineIso_other (a : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    (normalizationLineIso K n hn p q h a j i ≪≫
      divisorLineBundleEqIso (other_section_ideal K n hn p q h a hij)
        (normalizationIdeal_cartier K n hn p q h a j i) effectiveCartier_top) ≪≫
          divisorLineBundleTopIso effectiveCartier_top = otherComponentIso K n hn p q h a hij := by
  let _ := pointIdealComparison_isIso K n hn p q h a i j
  have he := ((normalizationLineIso_section K n hn p q h a j i).targetIdealEq
    (other_section_ideal K n hn p q h a hij)).ext
      (divisorLinePullbackIsoOfEq_compatible _ (section_cartier K n p hn q h a j).1
        effectiveCartier_top (other_section_ideal K n hn p q h a hij))
  rw [he]
  rfl

end FLT.Mazur.PolygonSinglePointLineNormalization
