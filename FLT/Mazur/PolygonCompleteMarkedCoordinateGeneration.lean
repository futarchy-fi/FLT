/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedCoordinateOpens
public import FLT.Mazur.PolygonCompleteClosedSpecialization
public import FLT.Mazur.GlobalEvaluationSpan

/-!
# Reconstructed coordinates generate the complete marked power

The original closed-stage coordinate charts cover the polygon. Every point
of the proper complete family specializes into that polygon, so the actual
reconstructed generator opens cover the total family as well.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules TopologicalSpace

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family originalStageToCompatibleProj
  completeCoefficientCoordinates completeCoefficientBoundaryExponent

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original closed-stage restrictions detect whether a family of opens covers the total space. -/
theorem completeOpenCover_of_originalZero {ι : Type*}
    (U : ι → (exactVeroneseProj K n h).Opens)
    (hU : (⨆ i, originalStageToCompatibleProj K n h 0 ⁻¹ᵁ U i) = ⊤) :
    iSup U = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, hy⟩ := exists_completeClosedFiber_specialization K n h y
  have hx : specialFiberInclusion K 0 n h x ∈
      ⨆ i, originalStageToCompatibleProj K n h 0 ⁻¹ᵁ U i := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  apply Opens.mem_iSup.mpr
  exact ⟨i, hy.mem_open (U i).isOpen hi⟩

/-- The uniquely lifted original coordinates generate the actual complete marked power. -/
theorem completeMarkedModelCoordinate_cover :
    (⨆ i, sectionGeneratorOpen
      (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
      (completeMarkedModelCoordinate K n h i)) = ⊤ := by
  apply completeOpenCover_of_originalZero K n h
  simp_rw [completeMarkedModelCoordinate_generatorOpen_preimage]
  rw [← Scheme.Hom.preimage_iSup]
  change originalStageToCompatibleProj K n h 0 ⁻¹ᵁ
    (⨆ i, Proj.basicOpen _ ((completeCoefficientCoordinates K n h).coordinate i)) = ⊤
  rw [(completeCoefficientCoordinates K n h).covers, Scheme.Hom.preimage_top]

/-- Evaluation by the original reconstructed coordinates is an epimorphism. -/
theorem completeMarkedModelCoordinate_evaluation_epi :
    Epi (ProjectiveSpace.globalEvaluation
      (completeMarkedPowerModel K n h (completeCoefficientBoundaryExponent K n h))
      (completeMarkedModelCoordinate K n h)) := by
  exact globalEvaluation_epi_of_sectionHom_isIso (completeMarkedModelCoordinate K n h)
    (fun i ↦ sectionGeneratorOpen _ (completeMarkedModelCoordinate K n h i))
    (completeMarkedModelCoordinate_cover K n h) id
    (fun i ↦ sectionHom_generatorOpen_isIso _ (completeMarkedModelCoordinate K n h i))

end FLT.Mazur.PolygonInfinitesimalStages
