/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicStage
public import FLT.Mazur.PolygonCompleteIdentityFiniteScaling

/-!
# The literal adic graph has the original variable-parameter polygon as input

Identify the actual adic input with the previously constructed original
finite input. This retains its whole polygon, original Laurent parameter,
and full nilpotent coefficient structure, including all node charts.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => completeIdentityActionSecond K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "b" => baseToSeries K m
local notation "f" => completeIdentityFiniteInput K n h 0 m
local notation "r" => scalingParameterProjection (A) (t) n h

/-- The whole original variable-parameter polygon is the actual adic action input. -/
def completeIdentityActionInputStageOriginalIso :
    scalingParameterFamily (A) (t) n h ≅ completeIdentityActionInputStage K n h m :=
  (completeIdentityFiniteInput_base_isPullback K n h 0 m).isoPullback

/-- The input identification retains the actual complete original input map. -/
@[reassoc] theorem completeIdentityActionInputStageOriginalIso_inclusion :
    (completeIdentityActionInputStageOriginalIso K n h m).hom ≫
      completeIdentityActionInputStageInclusion K n h m = (f) :=
  (completeIdentityFiniteInput_base_isPullback K n h 0 m).isoPullback_hom_fst

/-- The same identification retains the actual coefficient structure of the original polygon. -/
@[reassoc] theorem completeIdentityActionInputStageOriginalIso_structure :
    (completeIdentityActionInputStageOriginalIso K n h m).hom ≫
      pullback.snd ((s) ≫ (π)) (b) = (r) ≫ (family K m n h).hom :=
  (completeIdentityFiniteInput_base_isPullback K n h 0 m).isoPullback_hom_snd

/-- The literal adic graph projects to the whole original variable-parameter polygon. -/
def completeIdentityActionGraphStageOriginalProjection :
    completeIdentityActionGraphStage K n h m ⟶ scalingParameterFamily (A) (t) n h :=
  completeIdentityActionGraphStageProjection K n h m ≫
    (completeIdentityActionInputStageOriginalIso K n h m).inv

instance completeIdentityActionGraphStageOriginalProjection_proper :
    IsProper (completeIdentityActionGraphStageOriginalProjection K n h m) := by
  unfold completeIdentityActionGraphStageOriginalProjection
  infer_instance

instance completeIdentityActionGraphStageOriginalProjection_surjective :
    Surjective (completeIdentityActionGraphStageOriginalProjection K n h m) := by
  unfold completeIdentityActionGraphStageOriginalProjection
  infer_instance

/-- This projection is above the original unchanged finite input on every node. -/
@[reassoc] theorem completeIdentityActionGraphStageOriginalProjection_input :
    completeIdentityActionGraphStageOriginalProjection K n h m ≫ (f) =
      completeIdentityActionGraphStageProjection K n h m ≫
        completeIdentityActionInputStageInclusion K n h m := by
  rw [completeIdentityActionGraphStageOriginalProjection, Category.assoc,
    ← completeIdentityActionInputStageOriginalIso_inclusion, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
