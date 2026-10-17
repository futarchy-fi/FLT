/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeAction
public import FLT.Mazur.PolygonCompleteIdentityWholeActionFinite

/-!
# The full action recovers every original finite rotated action

The glued action retains the already proved finite identity action on its
zero parameter chart. Every other chart adds exactly the original rotation,
including all nilpotents and singular inputs at every finite order.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h

/-- The zero original parameter chart recovers the constructed whole identity action. -/
@[reassoc] theorem completeWholeAction_identityChart :
    (completeIdentityChart K n h 0 0 ⊗ₘ 𝟙 (X)) ≫ completeWholeAction K n h =
      completeIdentityWholeActionOver K n h := by
  rw [completeWholeAction_chart, completeWholeActionChart]
  have hz : completeWholeRotationOver K n h 0 = 𝟙 (X) := by
    apply Over.OverMorphism.ext
    exact completeRotation_zero K n h
  rw [hz, Category.comp_id]

/-- The actual original finite scaling input on any full smooth parameter chart. -/
def completeWholeFiniteInput (m : ℕ) (b : ZMod n) :
    PolygonInfinitesimal.scalingParameterFamily (Ring K m) (parameter K m) n h ⟶
      ((M) ⊗ (X)).left :=
  completeIdentityFiniteInput K n h 0 m ≫
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left

/-- Every finite-order rotated original action is recovered by the full global action. -/
@[reassoc] theorem completeWholeAction_finite_rotated (m : ℕ) (b : ZMod n) :
    completeWholeFiniteInput K n h m b ≫ (completeWholeAction K n h).left =
      completeIdentityFiniteScaling K n h m ≫ completeRotation K n h b := by
  change (completeIdentityFiniteInput K n h 0 m ≫
    (completeIdentityChart K n h 0 b ⊗ₘ 𝟙 (X)).left) ≫ completeWholeActionMap K n h = _
  rw [Category.assoc, completeWholeActionMap_chart]
  change completeIdentityFiniteInput K n h 0 m ≫
    completeIdentityWholeAction K n h ≫ completeRotation K n h b = _
  rw [completeIdentityWholeAction_finite_assoc]

/-- In particular the full action retains every unchanged original finite scaling. -/
@[reassoc] theorem completeWholeAction_finite (m : ℕ) :
    completeWholeFiniteInput K n h m 0 ≫ (completeWholeAction K n h).left =
      completeIdentityFiniteScaling K n h m := by
  rw [completeWholeAction_finite_rotated, completeRotation_zero, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
