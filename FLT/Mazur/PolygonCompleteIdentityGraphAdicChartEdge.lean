/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicEdge
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart

/-!
# An original punctured edge in the actual affine node-pair graph chart

The entire original finite identity edge lies in the diagonal node-pair
chart of the literal adic graph. Both node coordinates are computed using
the unchanged original multiplication; no whole-chart identification follows.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "M" => completeIdentityFiniteMulCoordinates K n h 0 m
local notation "l" => leftBranchOpen (A)[T;T⁻¹] (LaurentPolynomial.C (t))
local notation "r" => leftBranchOpen (A) (t)
local notation "s" => PolygonInfinitesimal.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h 0
local notation "d" => PolygonInfinitesimal.chart (A) (t) n h 0
local notation "f" => completeIdentityFiniteEdgeToAdicGraph K n h m
local notation "v" => completeIdentityActionAdicChartSpaceMap K n h m 0 0
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m

/-- The finite original edge satisfies the full original node-pair cubic relation. -/
def completeIdentityFiniteEdgeToChartSpace :
    branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionAdicChartSpace K n h m 0 0 :=
  pullback.lift (l) ((M) ≫ (r)) (by
    have he := completeIdentityFiniteOriginalMul_cubic K n h 0 m
    rw [← completeIdentityFiniteMulCoordinates_original,
      Category.assoc, completeIdentityStageTorus_inclusion_assoc] at he
    simpa only [edge, Category.assoc] using he.symm)

/-- The node-pair point is exactly the image of the already constructed actual adic graph point. -/
@[reassoc] theorem completeIdentityFiniteEdgeToChartSpace_graph :
    completeIdentityFiniteEdgeToChartSpace K n h m ≫ (v) = (f) ≫ (e) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityActionAdicChartSpaceMap_fst,
      completeIdentityFiniteEdgeToChartSpace, pullback.lift_fst_assoc,
      completeIdentityActionGraphAdicEmbedding_fst,
      completeIdentityFiniteEdgeToAdicGraph_source]
    rfl
  · simp only [Category.assoc, completeIdentityActionAdicChartSpaceMap_snd,
      completeIdentityFiniteEdgeToChartSpace, pullback.lift_snd_assoc,
      completeIdentityActionGraphAdicEmbedding_snd,
      completeIdentityFiniteEdgeToAdicGraph_target]
    rfl

/-- The original finite edge lies in the actual closed affine diagonal graph chart. -/
def completeIdentityFiniteEdgeToGraphChart :
    branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionGraphAdicChart K n h m 0 0 :=
  pullback.lift (f) (completeIdentityFiniteEdgeToChartSpace K n h m)
    (completeIdentityFiniteEdgeToChartSpace_graph K n h m).symm

/-- Its inclusion is the already constructed literal adic graph edge map. -/
@[reassoc] theorem completeIdentityFiniteEdgeToGraphChart_inclusion :
    completeIdentityFiniteEdgeToGraphChart K n h m ≫
      completeIdentityActionGraphAdicChartInclusion K n h m 0 0 = (f) :=
  pullback.lift_fst _ _ _

/-- Its original source node coordinate is exactly the original left puncture. -/
@[reassoc] theorem completeIdentityFiniteEdgeToGraphChart_source :
    completeIdentityFiniteEdgeToGraphChart K n h m ≫
      completeIdentityActionGraphAdicChartSource K n h m 0 0 = (l) := by
  rw [completeIdentityActionGraphAdicChartSource, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.fst _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_fst _ _ _

/-- Its original target node coordinate is the unchanged original multiplication puncture. -/
@[reassoc] theorem completeIdentityFiniteEdgeToGraphChart_target :
    completeIdentityFiniteEdgeToGraphChart K n h m ≫
      completeIdentityActionGraphAdicChartTarget K n h m 0 0 = (M) ≫ (r) := by
  rw [completeIdentityActionGraphAdicChartTarget, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_snd _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
