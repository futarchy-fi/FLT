/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphFlat
public import FLT.Mazur.PolygonCompleteIdentityStageTorus

/-!
# Literal adic base changes of the original cubic action graph

Base change the entire complete graph, rather than taking a new schematic
image after reduction. Each stage retains its proper surjective projection,
flat coefficient structure, and unchanged original cubic contraction square.
No identification with the finite branch-image graph is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "P" => completeIdentityActionProduct K n h 0
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "b" => baseToSeries K m

/-- The entire original action input at its literal adic stage. -/
abbrev completeIdentityActionInputStage : Scheme := pullback ((s) ≫ (π)) (b)

/-- The unchanged map from the adic input to the complete input. -/
abbrev completeIdentityActionInputStageInclusion :
    completeIdentityActionInputStage K n h m ⟶ (P) := pullback.fst ((s) ≫ (π)) (b)

/-- The whole complete cubic graph pulled back to this actual adic input. -/
abbrev completeIdentityActionGraphStage : Scheme :=
  pullback (p) (completeIdentityActionInputStageInclusion K n h m)

/-- The actual adic graph projection, before any schematic-image operation. -/
abbrev completeIdentityActionGraphStageProjection :
    completeIdentityActionGraphStage K n h m ⟶ completeIdentityActionInputStage K n h m :=
  pullback.snd (p) (completeIdentityActionInputStageInclusion K n h m)

/-- The adic graph still maps to the original complete graph. -/
abbrev completeIdentityActionGraphStageInclusion :
    completeIdentityActionGraphStage K n h m ⟶ completeIdentityActionGraphClosure K n h :=
  pullback.fst (p) (completeIdentityActionInputStageInclusion K n h m)

/-- The coefficient map of the literal adic graph. -/
def completeIdentityActionGraphStageStructure :
    completeIdentityActionGraphStage K n h m ⟶ Spec (.of (Ring K m)) :=
  completeIdentityActionGraphStageProjection K n h m ≫ pullback.snd ((s) ≫ (π)) (b)

/-- This is the actual base change of the original complete graph over its coefficient base. -/
theorem completeIdentityActionGraphStage_isPullback :
    IsPullback (completeIdentityActionGraphStageInclusion K n h m)
      (completeIdentityActionGraphStageStructure K n h m) ((p) ≫ (s) ≫ (π)) (b) :=
  (IsPullback.of_hasPullback (p) _).paste_vert (IsPullback.of_hasPullback ((s) ≫ (π)) (b))

instance completeIdentityActionGraphStageProjection_proper :
    IsProper (completeIdentityActionGraphStageProjection K n h m) := inferInstance

instance completeIdentityActionGraphStageProjection_surjective :
    Surjective (completeIdentityActionGraphStageProjection K n h m) := inferInstance

/-- Flatness belongs to the literal base-changed complete graph. -/
instance completeIdentityActionGraphStageStructure_flat :
    Flat (completeIdentityActionGraphStageStructure K n h m) :=
  MorphismProperty.of_isPullback (completeIdentityActionGraphStage_isPullback K n h m)
    (inferInstanceAs (Flat ((p) ≫ (s) ≫ (π))))

/-- The actual stage graph retains its original complete-polygon-valued map. -/
def completeIdentityActionGraphStageLift :
    completeIdentityActionGraphStage K n h m ⟶ exactVeroneseProj K n h :=
  completeIdentityActionGraphStageInclusion K n h m ≫ (l)

/-- All original contraction equations survive the nonflat adic base change. -/
@[reassoc] theorem completeIdentityActionGraphStageLift_contraction :
    completeIdentityActionGraphStageLift K n h m ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityActionGraphStageProjection K n h m ≫
        completeIdentityActionInputStageInclusion K n h m ≫
          completeIdentityActionTarget K n h 0 := by
  rw [completeIdentityActionGraphStageLift, Category.assoc,
    completeIdentityActionGraphLift_contraction, pullback.condition_assoc]

/-- The graph's original polygon map has exactly its constructed stage coefficient map. -/
@[reassoc] theorem completeIdentityActionGraphStageLift_structure :
    completeIdentityActionGraphStageLift K n h m ≫ (π) =
      completeIdentityActionGraphStageStructure K n h m ≫ (b) := by
  rw [completeIdentityActionGraphStageLift, Category.assoc,
    completeIdentityActionGraphLift_structure]
  exact (completeIdentityActionGraphStage_isPullback K n h m).w

end FLT.Mazur.PolygonInfinitesimalStages
