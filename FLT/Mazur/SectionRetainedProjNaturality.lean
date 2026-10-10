/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedLineEvaluation
public import FLT.Mazur.SectionRetainedProjConstruction

/-!
# Naturality of the retained canonical morphism

Actual pullback followed by a specified line comparison commutes with the
canonical retained Proj maps whenever the original graded map is globally defined.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousIdeal

namespace FLT.Mazur.SectionRetainedProjNaturality

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedProjConstruction SectionRetainedChartComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme} (p : Y ⟶ X) (L : X.Modules) (M : Y.Modules)
  [Fact (LocallyFreeRankOne L)] [Fact (LocallyFreeRankOne M)]
  (e : (pullback p).obj L ≅ M) (q : ℕ)
  [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  [GradedRing (RetainedSubringGrading.grade (grade M ⊤) q)]

/-- The canonical maps retain the original line pullback and the original retained-ring map. -/
@[reassoc]
theorem toProj_map (hL : PositivePowerGenerated L q) (hM : PositivePowerGenerated M q)
    (hφ : (RetainedSubringGrading.grade (grade M ⊤) q)₊ ≤
      (RetainedSubringGrading.grade (grade L ⊤) q)₊.map
        (SectionRetainedLineEvaluation.map p L M e q)) :
    toProj M q hM ≫ Proj.map (SectionRetainedLineEvaluation.map p L M e q) hφ =
      p ≫ toProj L q hL := by
  obtain ⟨𝒰, c, d, s, hd, hs⟩ := exists_generating_cover L q hL
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ p)
  intro i
  let k := CategoryTheory.Limits.pullback.fst p (𝒰.f i)
  let l := CategoryTheory.Limits.pullback.snd p (𝒰.f i)
  have hc : k ≫ p = l ≫ 𝒰.f i := CategoryTheory.Limits.pullback.condition
  let c' : (pullback (k ≫ p)).obj L ≅ structureModule _ := by
    rw [hc]
    exact SectionGradedProjChart.pullTrivialization (𝒰.f i) L (c i) l
  let c'' := (pullback k).mapIso e.symm ≪≫ (pullbackComp k p).app L ≪≫ c'
  have hi : IsIso (globalSectionHom _ (pullGlobal (k ≫ p)
      (tensorPower L (q * d i)) (s i))) := by
    rw [hc]
    exact SectionGradedProjChart.pullGenerator_isIso_of_ringHom _ L _ (s i)
      (SectionGradedProjChart.ringHom_isUnit_pullback (𝒰.f i) L (c i) l
        (SectionGradedProjChart.pullTrivialization (𝒰.f i) L (c i) l) (s i) (hs i))
  have hu := SectionGradedProjChart.ringHom_isUnit_of_pullGenerator (k ≫ p) L c' (s i)
  have hv := SectionLinePullbackFraction.ringHom_isUnit_section p k L M e c'' c' (s i) hu
  change k ≫ (toProj M q hM ≫ _) = k ≫ (p ≫ toProj L q hL)
  rw [← Category.assoc, toProj_comp M q hM k c'' _ (hd i) hv,
    ← Category.assoc, toProj_comp L q hL (k ≫ p) c' (s i) (hd i) hu]
  have hv' : IsUnit (SectionRetainedProjChart.ringHom k M c'' q
      (SectionRetainedLineEvaluation.map p L M e q (insertion L q (d i) (s i)))) := by
    rw [SectionRetainedLineEvaluation.map_insertion]
    exact hv
  simpa only [SectionRetainedLineEvaluation.map_insertion] using
    SectionRetainedLineEvaluation.toProj_map p L M e q k c'' c' hφ (s i) (hd i) hv' hu

end FLT.Mazur.SectionRetainedProjNaturality
