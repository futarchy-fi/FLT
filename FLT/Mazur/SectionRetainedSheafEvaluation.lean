/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjChartSections
public import FLT.Mazur.SectionRetainedChartMorphism
public import FLT.Mazur.SectionRetainedProjOpens

/-!
# Actual sheaf evaluation under the retained Proj morphism

The intrinsic fraction comparison is the structure-sheaf map of the
constructed retained Proj morphism on every original generator subopen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedSheafEvaluation

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  (h : PositivePowerGenerated L q) (d : ℕ) (hd : 0 < d)
  (s : Γ(tensorPower L (q * d), ⊤)) (U : X.Opens)
  (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s)

include hd hU in
/-- Original generator subopens lie over the corresponding retained basic open. -/
theorem le_preimage : U ≤ toProj L q h ⁻¹ᵁ
    Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d s) := by
  rw [SectionRetainedProjOpens.toProj_preimage_basicOpen L q h s hd]
  exact hU

/-- Sheaf pullback along the actual retained morphism is its intrinsic fraction evaluation. -/
theorem awayToSection_appLE :
    Proj.awayToSection _ (insertion L q d s) ≫
        (toProj L q h).appLE
          (Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d s))
          U (le_preimage L q h d hd s U hU) =
      CommRingCat.ofHom (toFunctions L q d s U hU) := by
  apply GradedProjChartSections.chartSection_evaluation _ _ (insertion_mem L q d s) hd
  rw [← SectionRetainedChartMorphism.toProjOn_eq L q d s hd h U hU]
  simp only [SectionRetainedChartMorphism.toProjOn, Scheme.Opens.toSpecΓ,
    Category.assoc]
  rw [← Spec.map_comp_assoc]
  rfl

/-- Pointwise fraction evaluation retains the original sheaf pullback. -/
theorem awayToSection_appLE_apply
    (z : Away (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d s)) :
    (toProj L q h).appLE _ U (le_preimage L q h d hd s U hU)
        (Proj.awayToSection _ (insertion L q d s) z) =
      toFunctions L q d s U hU z :=
  ConcreteCategory.congr_hom (awayToSection_appLE L q h d hd s U hU) z

end FLT.Mazur.SectionRetainedSheafEvaluation
