/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicResidualSource
public import FLT.Mazur.PolygonInfinitesimalNodeChartUnique

/-!
# The residual graph has a unique original source-node label

Every point outside the actual section belongs to precisely one source node
chart. Its target misses that same chart entirely, not just a chosen chart pair.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h (m + 1)
local notation "l" => completeIdentityActionGraphStageOriginalLift K n h (m + 1)

/-- Each residual graph point has exactly one original source-node chart label. -/
theorem completeIdentityAdicResidual_unique_source_label
    (x : completeIdentityActionGraphStage K n h (m + 1))
    (hx : x ∉ completeIdentityAdicSectionOpen K n h m) :
    ∃! i : Fin n, (p) x ∈
      Set.range (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i) := by
  obtain ⟨i, z, hz⟩ := charts_cover (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h ((p) x)
  refine ⟨i, ⟨z, hz⟩, ?_⟩
  rintro j ⟨w, hw⟩
  exact (node_chart_label_unique (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h z w
    (completeIdentityAdicResidual_source_ideal K n h m x hx i z hz) (hz.trans hw.symm)).symm

/-- The target of a residual point misses its original source-node chart completely. -/
theorem completeIdentityAdicResidual_target_avoids_source_label
    (x : completeIdentityActionGraphStage K n h (m + 1))
    (hx : x ∉ completeIdentityAdicSectionOpen K n h m) (i : Fin n)
    (hi : (p) x ∈ Set.range (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i)) :
    (l) x ∉ Set.range (chart (A) (t) n h i) := by
  intro ht
  apply hx
  apply (completeIdentityAdicSectionOpen_mem_iff K n h m x).mpr
  exact ⟨i, (completeIdentityActionGraphAdicChart_mem_range K n h (m + 1) i i x).mpr
    ⟨hi, ht⟩⟩

end FLT.Mazur.PolygonInfinitesimalStages
