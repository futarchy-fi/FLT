/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicSectionEdges
public import FLT.Mazur.PolygonSmoothingCoordinateIdeal

/-!
# The remaining graph complement has original node inputs

Every source chart of a point outside the actual section contains both original
branch coordinates in its prime ideal. The conclusion concerns the unchanged graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "q" => LaurentPolynomial.C (t)
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h (m + 1)

/-- Outside the section, both original source coordinates lie in the point's prime ideal. -/
theorem completeIdentityAdicResidual_source_coordinates
    (x : completeIdentityActionGraphStage K n h (m + 1))
    (hx : x ∉ completeIdentityAdicSectionOpen K n h m) (i : Fin n)
    (z : PolygonSmoothing.chart (A)[T;T⁻¹] (q))
    (hz : PolygonInfinitesimal.chart (A)[T;T⁻¹] (q) n h i z = (p) x) :
    leftCoordinate (q) ∈ z.asIdeal ∧ rightCoordinate (q) ∈ z.asIdeal := by
  constructor
  · by_contra hn
    have hz' : z ∈ Set.range (leftBranchOpen (A)[T;T⁻¹] (q)) := by
      rw [leftBranchOpen_range]
      exact hn
    obtain ⟨w, rfl⟩ := hz'
    apply hx
    apply completeIdentityAdicSectionOpen_of_edge K n h m i
    exact ⟨w, hz⟩
  · by_contra hn
    have hz' : z ∈ Set.range (precedingBranch (A)[T;T⁻¹] (q)) := by
      rw [precedingBranch_range, rightBranchOpen_range]
      exact hn
    obtain ⟨w, rfl⟩ := hz'
    have ho : precedingBranch (A)[T;T⁻¹] (q) ≫
        PolygonInfinitesimal.chart (A)[T;T⁻¹] (q) n h i =
        edge (A)[T;T⁻¹] (q) n h (finRotate n i) := by
      simpa only [Equiv.symm_apply_apply, edge] using
        (overlap (A)[T;T⁻¹] (q) n h (finRotate n i)).symm
    apply hx
    apply completeIdentityAdicSectionOpen_of_edge K n h m (finRotate n i)
    refine ⟨w, ?_⟩
    rw [← ho]
    exact hz

/-- The entire explicit original node ideal vanishes at every residual source point. -/
theorem completeIdentityAdicResidual_source_ideal
    (x : completeIdentityActionGraphStage K n h (m + 1))
    (hx : x ∉ completeIdentityAdicSectionOpen K n h m) (i : Fin n)
    (z : PolygonSmoothing.chart (A)[T;T⁻¹] (q))
    (hz : PolygonInfinitesimal.chart (A)[T;T⁻¹] (q) n h i z = (p) x) :
    coordinateIdeal (q) ≤ z.asIdeal := by
  have hc := completeIdentityAdicResidual_source_coordinates K n h m x hx i z hz
  rw [coordinateIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact hc

/-- In each original graph chart, the residual locus lies over the original source node. -/
theorem completeIdentityAdicResidual_chart_source_ideal (i j : Fin n)
    (z : completeIdentityActionGraphAdicChart K n h (m + 1) i j)
    (hz : completeIdentityActionGraphAdicChartInclusion K n h (m + 1) i j z ∉
      completeIdentityAdicSectionOpen K n h m) :
    coordinateIdeal (q) ≤
      (completeIdentityActionGraphAdicChartSource K n h (m + 1) i j z).asIdeal := by
  apply completeIdentityAdicResidual_source_ideal K n h m _ hz i
  exact congrArg (fun f ↦ f z)
    (completeIdentityActionGraphAdicChartSource_inclusion K n h (m + 1) i j)

end FLT.Mazur.PolygonInfinitesimalStages
