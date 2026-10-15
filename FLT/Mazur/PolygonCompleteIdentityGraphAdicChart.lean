/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChartSpace
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicIdeal

/-!
# Actual affine charts of the literal adic cubic graph

Pull back the full original graph ideal to the original two-node lifting
spaces. The resulting affine schemes are open in the actual adic graph
and hence flat over its truncated base. No flatness is transferred to a
branch-image quotient, and no target node is claimed to contain all outputs.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i
local notation "d" => chart (A) (t) n h j
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m
local notation "v" => completeIdentityActionAdicChartSpaceMap K n h m i j

/-- The full closed graph restricted to both specified original node charts. -/
abbrev completeIdentityActionGraphAdicChart : Scheme := pullback (e) (v)

/-- The chart is an actual open of the literal adic graph. -/
abbrev completeIdentityActionGraphAdicChartInclusion := pullback.fst (e) (v)

/-- Its closed inclusion retains the entire graph ideal in the original node relation. -/
abbrev completeIdentityActionGraphAdicChartEmbedding := pullback.snd (e) (v)

instance completeIdentityActionGraphAdicChartInclusion_open :
    IsOpenImmersion (completeIdentityActionGraphAdicChartInclusion K n h m i j) :=
  inferInstance

instance completeIdentityActionGraphAdicChartEmbedding_closed :
    IsClosedImmersion (completeIdentityActionGraphAdicChartEmbedding K n h m i j) :=
  inferInstance

/-- These are affine charts of the actual graph, not of its reduction or a branch image. -/
instance completeIdentityActionGraphAdicChart_affine :
    IsAffine (completeIdentityActionGraphAdicChart K n h m i j) :=
  isAffine_of_isAffineHom (completeIdentityActionGraphAdicChartEmbedding K n h m i j)

/-- The original source node coordinate on the actual graph chart. -/
def completeIdentityActionGraphAdicChartSource :=
  completeIdentityActionGraphAdicChartEmbedding K n h m i j ≫ pullback.fst _ _

/-- The original target node coordinate on the actual graph chart. -/
def completeIdentityActionGraphAdicChartTarget :=
  completeIdentityActionGraphAdicChartEmbedding K n h m i j ≫ pullback.snd _ _

/-- The source coordinate recovers the original whole-graph projection. -/
@[reassoc] theorem completeIdentityActionGraphAdicChartSource_inclusion :
    completeIdentityActionGraphAdicChartSource K n h m i j ≫ (s) =
      completeIdentityActionGraphAdicChartInclusion K n h m i j ≫
        completeIdentityActionGraphStageOriginalProjection K n h m := by
  rw [completeIdentityActionGraphAdicChartSource, Category.assoc,
    ← completeIdentityActionAdicChartSpaceMap_fst,
    ← pullback.condition_assoc, completeIdentityActionGraphAdicEmbedding_fst]

/-- The target coordinate is exactly the constructed original-stage lift. -/
@[reassoc] theorem completeIdentityActionGraphAdicChartTarget_inclusion :
    completeIdentityActionGraphAdicChartTarget K n h m i j ≫ (d) =
      completeIdentityActionGraphAdicChartInclusion K n h m i j ≫
        completeIdentityActionGraphStageOriginalLift K n h m := by
  rw [completeIdentityActionGraphAdicChartTarget, Category.assoc,
    ← completeIdentityActionAdicChartSpaceMap_snd,
    ← pullback.condition_assoc, completeIdentityActionGraphAdicEmbedding_snd]

/-- Its flat structure is over the unchanged original truncated base. -/
def completeIdentityActionGraphAdicChartStructure :=
  completeIdentityActionGraphAdicChartInclusion K n h m i j ≫
    completeIdentityActionGraphStageStructure K n h m

instance completeIdentityActionGraphAdicChartStructure_flat :
    Flat (completeIdentityActionGraphAdicChartStructure K n h m i j) := by
  unfold completeIdentityActionGraphAdicChartStructure
  infer_instance

/-- The full chart kernel is precisely the restricted original stage graph ideal. -/
theorem completeIdentityActionGraphAdicChart_ideal :
    (e).ker.comap (v) = (completeIdentityActionGraphAdicChartEmbedding K n h m i j).ker := by
  have H := (IsPullback.of_hasPullback (e) (v)).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- The affine chart still uses the unchanged full complete cubic-graph kernel. -/
theorem completeIdentityActionGraphAdicChart_completeIdeal :
    (completeIdentityActionGraphInclusion K n h).ker.comap
        ((v) ≫ completeIdentityActionAdicLiftSpaceMap K n h m) =
      (completeIdentityActionGraphAdicChartEmbedding K n h m i j).ker := by
  rw [Scheme.IdealSheafData.comap_comp,
    completeIdentityActionGraphAdicEmbedding_ideal, completeIdentityActionGraphAdicChart_ideal]

end FLT.Mazur.PolygonInfinitesimalStages
