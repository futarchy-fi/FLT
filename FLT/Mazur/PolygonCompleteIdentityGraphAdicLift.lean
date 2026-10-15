/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicStage

/-!
# Original polygon-valued maps on every literal adic graph

The cartesian original-stage realization turns the complete polygon map
on the graph into a map to the actual infinitesimal polygon. Its original
contraction and all pulled-back cubic ideals are retained as scheme data.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "r" => originalStageToCompatibleProj K n h m
local notation "l" => completeIdentityActionGraphStageLift K n h m
local notation "t" => completeIdentityActionGraphStageStructure K n h m
local notation "p" => completeIdentityActionGraphStageProjection K n h m
local notation "v" => completeIdentityActionInputStageInclusion K n h m
local notation "a" => completeIdentityActionTarget K n h 0
local notation "c" => completePointToIntegralCubic K n h 0

/-- The complete graph's original polygon map lands in the actual original adic polygon. -/
def completeIdentityActionGraphStageOriginalLift :
    completeIdentityActionGraphStage K n h m ⟶ (family K m n h).left :=
  (originalStageToCompatibleProj_isPullback K n h m).lift (l) (t)
    (completeIdentityActionGraphStageLift_structure K n h m)

/-- The original stage map retains the complete polygon map on every function. -/
@[reassoc] theorem completeIdentityActionGraphStageOriginalLift_realization :
    completeIdentityActionGraphStageOriginalLift K n h m ≫ (r) = (l) :=
  IsPullback.lift_fst _ _ _ _

/-- Its coefficient structure is exactly that of the literal adic graph. -/
@[reassoc] theorem completeIdentityActionGraphStageOriginalLift_structure :
    completeIdentityActionGraphStageOriginalLift K n h m ≫ (family K m n h).hom = (t) :=
  IsPullback.lift_snd _ _ _ _

/-- The actual original stage lift satisfies the unchanged cubic contraction square. -/
@[reassoc] theorem completeIdentityActionGraphStageOriginalLift_contraction :
    completeIdentityActionGraphStageOriginalLift K n h m ≫ (r) ≫ (c) =
      (p) ≫ (v) ≫ (a) := by
  rw [completeIdentityActionGraphStageOriginalLift_realization_assoc,
    completeIdentityActionGraphStageLift_contraction]

/-- The construction retains every full cubic ideal, including its nilpotent structure. -/
theorem completeIdentityActionGraphStageOriginalLift_ideal
    (I : (WeierstrassIntegralChart.integralCurve
      (completePointWeierstrassCurve K n h 0)).IdealSheafData) :
    ((I.comap (c)).comap (r)).comap
        (completeIdentityActionGraphStageOriginalLift K n h m) =
      ((I.comap (a)).comap (v)).comap (p) := by
  simp only [← Scheme.IdealSheafData.comap_comp]
  rw [completeIdentityActionGraphStageOriginalLift_contraction]

/-- The two unchanged projections uniquely determine this original-stage lift. -/
theorem completeIdentityActionGraphStageOriginalLift_unique
    (f : completeIdentityActionGraphStage K n h m ⟶ (family K m n h).left)
    (hr : f ≫ (r) = (l)) (ht : f ≫ (family K m n h).hom = (t)) :
    f = completeIdentityActionGraphStageOriginalLift K n h m := by
  apply (originalStageToCompatibleProj_isPullback K n h m).hom_ext
  · exact hr.trans (completeIdentityActionGraphStageOriginalLift_realization K n h m).symm
  · exact ht.trans (completeIdentityActionGraphStageOriginalLift_structure K n h m).symm

end FLT.Mazur.PolygonInfinitesimalStages
