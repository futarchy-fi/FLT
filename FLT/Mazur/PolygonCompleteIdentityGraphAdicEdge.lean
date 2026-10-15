/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphFiniteEdge
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicInput
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicLift
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoordinates

/-!
# The original finite edge lies in the literal adic cubic graph

Base change the constructed complete-graph edge map to the original stage.
Both projections are computed: the source is the original finite edge and
the target is the unchanged original finite multiplication coordinate.
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
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (0 : Fin n)
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "v" => completeIdentityFiniteEdgeToGraph K n h m

/-- The original finite identity edge maps into the literal adic base change of the graph. -/
def completeIdentityFiniteEdgeToAdicGraph :
    PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionGraphStage K n h m :=
  pullback.lift (v) ((j) ≫ (o).hom) (by
    rw [completeIdentityFiniteEdgeToGraph_source, Category.assoc,
      completeIdentityActionInputStageOriginalIso_inclusion])

/-- The adic map is exactly the specified base change of the complete graph edge map. -/
@[reassoc] theorem completeIdentityFiniteEdgeToAdicGraph_complete :
    completeIdentityFiniteEdgeToAdicGraph K n h m ≫
      completeIdentityActionGraphStageInclusion K n h m = (v) := pullback.lift_fst _ _ _

/-- Its actual original source projection is the full original finite identity edge. -/
@[reassoc] theorem completeIdentityFiniteEdgeToAdicGraph_source :
    completeIdentityFiniteEdgeToAdicGraph K n h m ≫
      completeIdentityActionGraphStageOriginalProjection K n h m = (j) := by
  rw [completeIdentityActionGraphStageOriginalProjection, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ (o).inv = _
  rw [pullback.lift_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Its original complete target is the actual original group product. -/
@[reassoc] theorem completeIdentityFiniteEdgeToAdicGraph_realization :
    completeIdentityFiniteEdgeToAdicGraph K n h m ≫
        completeIdentityActionGraphStageOriginalLift K n h m ≫
          originalStageToCompatibleProj K n h m =
      completeIdentityFiniteOriginalMul K n h 0 m ≫ (completePointIdentityOpen K n h 0).ι := by
  rw [completeIdentityActionGraphStageOriginalLift_realization]
  change _ ≫ completeIdentityActionGraphStageInclusion K n h m ≫
    completeIdentityActionGraphLift K n h = _
  rw [completeIdentityFiniteEdgeToAdicGraph_complete_assoc,
    completeIdentityFiniteEdgeToGraph_target]

/-- The actual original-stage target is precisely the original multiplication coordinate. -/
@[reassoc] theorem completeIdentityFiniteEdgeToAdicGraph_target :
    completeIdentityFiniteEdgeToAdicGraph K n h m ≫
        completeIdentityActionGraphStageOriginalLift K n h m =
      completeIdentityFiniteMulCoordinates K n h 0 m ≫ edge (A) (t) n h 0 := by
  apply (cancel_mono (originalStageToCompatibleProj K n h m)).mp
  rw [Category.assoc, completeIdentityFiniteEdgeToAdicGraph_realization,
    Category.assoc, ← completeIdentityStageTorus_inclusion,
    completeIdentityFiniteMulCoordinates_original_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
