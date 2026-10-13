/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCyclicSchemeAction
public import FLT.Mazur.PolygonCompleteClosedRotation
public import FLT.Mazur.PolygonActionTranslation

/-!
# Original complete rotations specialize to the full polygon action

On the original closed square the lifted rotations agree with the specified
pinching rotations. Thus their normalization components and nodes retain the
original cyclic incidence, and they are actual full-group translations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonCyclicAtlas
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "b" => completeClosedBase K
local notation "j" => completeClosedFiberInclusion K n h
local notation "q" => PolygonCyclicAtlas.toBase K n h
local notation "hb" => completeClosedFiber_isPullback K n h

/-- The lifted rotation is exactly the original chart rotation on the original closed square. -/
theorem completeCartesianRotation_closed (a : ZMod n) :
    completeCartesianRotation K n h b j q hb a = closedRotation K n h a := by
  apply (cancel_mono j).mp
  rw [completeCartesianRotation_fst, closedRotation_completeClosedFiberInclusion]

/-- The original complete rotation carries each entire normalization component to its successor. -/
@[reassoc] theorem componentMap_completeCartesianRotation_closed (a : ZMod n) (i : Fin n) :
    componentMap K n h i ≫ completeCartesianRotation K n h b j q hb a =
      componentMap K n h (rotateIndex a i) := by
  rw [completeCartesianRotation_closed]
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ componentMap K n h i ≫ _ =
      ProjectiveLine.left K ≫ componentMap K n h (rotateIndex a i)
    rw [left_componentMap_assoc, chart_closedRotation, left_componentMap]
  · change ProjectiveLine.right K ≫ componentMap K n h i ≫ _ =
      ProjectiveLine.right K ≫ componentMap K n h (rotateIndex a i)
    rw [right_componentMap_assoc, chart_closedRotation, right_componentMap,
      PolygonInfinitesimal.rotateIndex_preceding]

/-- The actual complete action specializes to the pinching rotation over the original field. -/
theorem completeCartesianRotationOver_closed (a : ZMod n) :
    completeCartesianRotationOver K n h b j q hb a = polygonRotation K hn P Q hp a := by
  let _ : Epi P := PolygonActionUnit.normalization_epi K n hn P Q hp
  apply (cancel_epi P).mp
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ P ≫ _ = componentι K n i ≫ P ≫ _
  rw [components_polygonRotation, componentι_rotation_assoc]
  rw [← Category.assoc, componentι_normalization, componentι_normalization]
  apply Over.OverMorphism.ext
  exact componentMap_completeCartesianRotation_closed K n h a i

/-- Original nodes are carried to the node with the same translated cyclic index. -/
@[reassoc] theorem node_completeCartesianRotation_closed (a : ZMod n) (i : Fin n) :
    nodeι K n i ≫ Q ≫ completeCartesianRotationOver K n h b j q hb a =
      nodeι K n (rotateIndex a i) ≫ Q := by
  rw [completeCartesianRotationOver_closed, nodes_polygonRotation, nodeι_rotation_assoc]

/-- The actual closed rotation is translation by the all-one point in its cyclic component. -/
theorem completeCartesianRotationOver_closed_translation (a : ZMod n) :
    completeCartesianRotationOver K n h b j q hb a =
      PolygonActionTranslation.translation K n hn P Q hp 1 a := by
  rw [PolygonActionTranslation.translation_eq, polygonScaling_one, Category.id_comp,
    completeCartesianRotationOver_closed]

end FLT.Mazur.PolygonInfinitesimalStages
