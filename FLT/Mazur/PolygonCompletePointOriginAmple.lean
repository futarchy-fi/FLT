/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicSections
public import FLT.Mazur.SectionGradedProjOfAmple

/-!
# Ampleness of the original complete-base cubic origin line

The descended normalized cubic coordinates exhibit an affine generator cover
of the intrinsic origin cube. This proves ampleness of the original line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
open SectionGradedProjConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "A" => originDivisorLine (W) 1

local instance originLineFact : Fact (LocallyFreeRankOne (A)) :=
  ⟨completePointOriginLine_rankOne K n h i 1⟩

/-- The original cubic-origin line is ample over the full complete base. -/
theorem completePointOriginLine_ample : AmpleLineBundle (A) := by
  refine ⟨inferInstance, completePointOriginLine_rankOne K n h i 1, fun x ↦ ?_⟩
  have hx : x ∈ ⨆ j, sectionGeneratorOpen (tensorPower (A) 3)
      (completePointCubicSections K n h i j) := by
    rw [completePointCubicSections_cover]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨3, by decide, completePointCubicSections K n h i j, hj,
    completePointCubicSections_affine K n h i j⟩

/-- The original origin line has positive-power generation without additional assumptions. -/
theorem completePointOriginLine_positivePowerGenerated : PositivePowerGenerated (A) :=
  positivePowerGenerated_of_ample (A) (completePointOriginLine_ample K n h i)

/-- The canonical full section-ring map is an open immersion for the actual cubic. -/
theorem completePointOrigin_toProj_isOpenImmersion :
    IsOpenImmersion (toProj (A) (completePointOriginLine_positivePowerGenerated K n h i)) :=
  SectionGradedProjOfAmple.isOpenImmersion (A) (completePointOriginLine_ample K n h i)
    (completePointOriginLine_positivePowerGenerated K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
