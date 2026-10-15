/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# A finite original-node affine cover of the actual adic graph

All pairs of source and target node charts cover the literal graph. The
range formula records exactly which original inputs and outputs a chart
contains. It does not discard off-diagonal charts or assert node preservation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "l" => completeIdentityActionGraphStageOriginalLift K n h m
local notation "F" => completeIdentityFiniteInput K n h 0 m ≫
  completeIdentityActionTarget K n h 0
local notation "G" => originalStageToCompatibleProj K n h m ≫
  completePointToIntegralCubic K n h 0

/-- The original two-node relation has precisely the specified source and target range. -/
theorem completeIdentityActionAdicChartSpaceMap_range (i j : Fin n) :
    Set.range (completeIdentityActionAdicChartSpaceMap K n h m i j) =
      (pullback.fst (F) (G) ⁻¹' Set.range (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i)) ∩
      (pullback.snd (F) (G) ⁻¹' Set.range (chart (A) (t) n h j)) := by
  rw [completeIdentityActionAdicChartSpaceMap, Scheme.Pullback.range_map]
  rfl

/-- Actual graph-chart membership retains both original node coordinates exactly. -/
theorem completeIdentityActionGraphAdicChart_mem_range (i j : Fin n)
    (x : completeIdentityActionGraphStage K n h m) :
    x ∈ Set.range (completeIdentityActionGraphAdicChartInclusion K n h m i j) ↔
      (p) x ∈ Set.range (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i) ∧
      (l) x ∈ Set.range (chart (A) (t) n h j) := by
  rw [completeIdentityActionGraphAdicChartInclusion, Scheme.Pullback.range_fst,
    completeIdentityActionAdicChartSpaceMap_range]
  change ((e) ≫ pullback.fst (F) (G)) x ∈
      Set.range (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i) ∧
    ((e) ≫ pullback.snd (F) (G)) x ∈ Set.range (chart (A) (t) n h j) ↔ _
  rw [completeIdentityActionGraphAdicEmbedding_fst, completeIdentityActionGraphAdicEmbedding_snd]

/-- Every point of the literal graph lies in an actual affine original-node chart pair. -/
theorem completeIdentityActionGraphAdicChart_covers
    (x : completeIdentityActionGraphStage K n h m) :
    ∃ i j, x ∈ Set.range (completeIdentityActionGraphAdicChartInclusion K n h m i j) := by
  obtain ⟨i, u, hu⟩ := charts_cover (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h ((p) x)
  obtain ⟨j, v, hv⟩ := charts_cover (A) (t) n h ((l) x)
  exact ⟨i, j, (completeIdentityActionGraphAdicChart_mem_range K n h m i j x).mpr
    ⟨⟨u, hu⟩, ⟨v, hv⟩⟩⟩

/-- The finite affine open cover uses all original source-target node pairs. -/
def completeIdentityActionGraphAdicChartCover :
    (completeIdentityActionGraphStage K n h m).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n × Fin n)
    (fun ij ↦ completeIdentityActionGraphAdicChart K n h m ij.1 ij.2)
    (fun ij ↦ completeIdentityActionGraphAdicChartInclusion K n h m ij.1 ij.2)
    (fun x ↦ by
      obtain ⟨i, j, y, hy⟩ := completeIdentityActionGraphAdicChart_covers K n h m x
      exact ⟨(i, j), y, hy⟩) (fun _ ↦ inferInstance)

end FLT.Mazur.PolygonInfinitesimalStages
