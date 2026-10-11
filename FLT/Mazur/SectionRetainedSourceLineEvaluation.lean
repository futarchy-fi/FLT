/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedLineEvaluation
public import FLT.Mazur.GradedProjUnitChartMap

/-!
# Retained line evaluation from an arbitrary graded source

Actual line pullback preserves fraction evaluations even when the original
homogeneous coordinates come from a different graded ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SectionRetainedSourceLineEvaluation
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y Z : Scheme} (p : Y ⟶ X) (L : X.Modules) (M : Y.Modules)
  [Fact (LocallyFreeRankOne L)] [Fact (LocallyFreeRankOne M)]
  (e : (pullback p).obj L ≅ M) (q : ℕ)
  [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  [GradedRing (RetainedSubringGrading.grade (grade M ⊤) q)]
  (k : Z ⟶ Y) (c : (pullback k).obj M ≅ structureModule Z)
  (c' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
  {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (φ : 𝒜 →+*ᵍ RetainedSubringGrading.grade (grade L ⊤) q)

/-- Fractions in the original source keep their value under the specified line pullback. -/
theorem evaluation_source (s : A)
    (hu : IsUnit (SectionRetainedProjChart.ringHom k M c q
      (SectionRetainedLineEvaluation.map p L M e q (φ s))))
    (hv : IsUnit (SectionRetainedProjChart.ringHom (k ≫ p) L c' q (φ s))) :
    GradedProjUnitChart.evaluation 𝒜
        (((SectionRetainedProjChart.ringHom k M c q).comp
          (SectionRetainedLineEvaluation.map p L M e q).toRingHom).comp φ.toRingHom) s hu =
      GradedProjUnitChart.evaluation 𝒜
        ((SectionRetainedProjChart.ringHom (k ≫ p) L c' q).comp φ.toRingHom) s hv := by
  rw [← GradedProjUnitChartMap.evaluation_map,
    ← GradedProjUnitChartMap.evaluation_map]
  rw [SectionRetainedLineEvaluation.evaluation_map p L M e q k c c' (φ s) hu hv,
    GradedProjUnitChartMap.evaluation_map]

/-- The original source Proj chart is independent of coordinates after actual line pullback. -/
theorem toProj_source {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d)
    (hu : IsUnit (SectionRetainedProjChart.ringHom k M c q
      (SectionRetainedLineEvaluation.map p L M e q (φ s))))
    (hv : IsUnit (SectionRetainedProjChart.ringHom (k ≫ p) L c' q (φ s))) :
    GradedProjUnitChart.toProj 𝒜
        (((SectionRetainedProjChart.ringHom k M c q).comp
          (SectionRetainedLineEvaluation.map p L M e q).toRingHom).comp φ.toRingHom)
        s hu hs hd =
      GradedProjUnitChart.toProj 𝒜
        ((SectionRetainedProjChart.ringHom (k ≫ p) L c' q).comp φ.toRingHom) s hv hs hd := by
  unfold GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  rw [evaluation_source p L M e q k c c' 𝒜 φ s hu hv]

end FLT.Mazur.SectionRetainedSourceLineEvaluation
