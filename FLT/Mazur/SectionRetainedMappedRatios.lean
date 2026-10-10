/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjMapPullbackSections
public import FLT.Mazur.SectionRetainedCoordinateRatios
public import FLT.Mazur.SectionRetainedSheafEvaluation

/-!
# Ratios under maps to retained section rings

A graded map whose coordinates evaluate to specified sections pulls their
ratios back to the original section ratio through the retained Proj map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedMappedRatios

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] toProj toFunctions Proj.map Proj.awayToSection
  GradedProjMapChartSections.fractionMap

variable {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme}
  (L : X.Modules) [Fact (LocallyFreeRankOne L)] (q : ℕ)
  [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  (h : PositivePowerGenerated L q)
  (φ : 𝒜 →+*ᵍ RetainedSubringGrading.grade (grade L ⊤) q)
  (hφ : HomogeneousIdeal.irrelevant (RetainedSubringGrading.grade (grade L ⊤) q) ≤
    (HomogeneousIdeal.irrelevant 𝒜).map φ)
  (d : ℕ) (hd : 0 < d) (s t : A) (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 d)
  (a b : Γ(tensorPower L (q * d), ⊤))
  (ha : φ s = insertion L q d a) (hb : φ t = insertion L q d b)
  (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) a)

include hd ha hb in
/-- The actual composite Proj map evaluates coordinates as original section ratios. -/
theorem coordinate_ratio
    (hp : U ≤ (toProj L q h ≫ Proj.map φ hφ) ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    (toProj L q h ≫ Proj.map φ hφ).appLE (Proj.basicOpen 𝒜 s) U hp
        (Proj.awayToSection 𝒜 s
          (Away.mk 𝒜 hs 1 t (by simpa only [one_smul] using ht))) =
      sectionRatioOn (tensorPower L (q * d)) a U hU b := by
  rw [GradedProjMapPullbackSections.fraction_evaluation 𝒜 _ φ hφ s
    (insertion L q d a) ha (toProj L q h) U
    (SectionRetainedSheafEvaluation.le_preimage L q h d hd a U hU) hs]
  rw [GradedProjMapChartSections.fractionMap_ratio 𝒜 _ φ s (insertion L q d a) ha
    hs (insertion_mem L q d a) t ht (insertion L q d b) (insertion_mem L q d b) hb]
  rw [SectionRetainedSheafEvaluation.awayToSection_appLE_apply L q h d hd a U hU]
  exact SectionRetainedCoordinateRatios.toFunctions_ratio L q d a b U hU

end FLT.Mazur.SectionRetainedMappedRatios
