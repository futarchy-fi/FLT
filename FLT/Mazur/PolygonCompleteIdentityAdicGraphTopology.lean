/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicGraphCoherence
public import FLT.Mazur.PolygonStageClosedImmersion

/-!
# Adjacent literal adic graphs have the same underlying space

The original graph transition is the actual base change of the nilpotent
coefficient restriction. In particular no graph points appear at higher order.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "r" => completeIdentityAdicGraphRestriction K n h m
local notation "s" => completeIdentityActionGraphStageStructure K n h
local notation "j" => completeIdentityActionGraphStageInclusion K n h

/-- The graph restriction retains the actual adjacent coefficient map. -/
@[reassoc] theorem completeIdentityAdicGraphRestriction_structure :
    (r) ≫ s (m + 1) = s m ≫ baseRestriction K m := by
  rw [← completeIdentityActionGraphStageOriginalLift_structure,
    completeIdentityAdicGraphRestriction_target_assoc, stageRestriction_base,
    completeIdentityActionGraphStageOriginalLift_structure_assoc]

/-- The unchanged graph transition is Cartesian over the original coefficient restriction. -/
theorem completeIdentityAdicGraphRestriction_isPullback :
    IsPullback (r) (s m) (s (m + 1)) (baseRestriction K m) := by
  have hp : IsPullback ((r) ≫ j (m + 1)) (s m)
      (completeIdentityActionGraphProjection K n h ≫ completeIdentityActionSecond K n h ≫
        exactVeroneseProjToBase K n h) (baseRestriction K m ≫ baseToSeries K (m + 1)) := by
    rw [completeIdentityAdicGraphRestriction_complete, baseRestriction_toSeries]
    exact completeIdentityActionGraphStage_isPullback K n h m
  exact hp.of_right (completeIdentityAdicGraphRestriction_structure K n h m)
    (completeIdentityActionGraphStage_isPullback K n h (m + 1))

/-- Every adjacent graph transition is a closed immersion of the full original schemes. -/
instance completeIdentityAdicGraphRestriction_closed : IsClosedImmersion (r) :=
  MorphismProperty.of_isPullback
    (completeIdentityAdicGraphRestriction_isPullback K n h m).flip inferInstance

/-- The transition covers every point, including any residual graph points. -/
instance completeIdentityAdicGraphRestriction_surjective : Surjective (r) :=
  MorphismProperty.of_isPullback
    (completeIdentityAdicGraphRestriction_isPullback K n h m).flip inferInstance

/-- All adjacent literal adic graphs have the same topological space. -/
def completeIdentityAdicGraphRestrictionHomeomorph :
    completeIdentityActionGraphStage K n h m ≃ₜ
      completeIdentityActionGraphStage K n h (m + 1) :=
  (r).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective (r).surjective

/-- This homeomorphism is the specified original graph restriction on points. -/
theorem completeIdentityAdicGraphRestrictionHomeomorph_apply
    (x : completeIdentityActionGraphStage K n h m) :
    completeIdentityAdicGraphRestrictionHomeomorph K n h m x = (r) x := rfl

end FLT.Mazur.PolygonInfinitesimalStages
