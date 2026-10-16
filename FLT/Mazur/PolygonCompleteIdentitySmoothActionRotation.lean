/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothAction

/-!
# Rotation commutes with the original smooth identity action

Translation in the constructed commutative smooth group rotates the second
input and output by the same original cyclic label.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "j" => completeIdentityChart K n h 0 0
local notation "a" => completeIdentitySmoothAction K n h

/-- Evaluation of the smooth action retains the two original group inputs. -/
theorem completeIdentitySmoothAction_evaluation {T : Over (Spec (.of (PowerSeries K)))}
    (x : T ⟶ (G).X) (y : T ⟶ (M)) :
    lift x y ≫ (a) = (x ≫ (j)) * y := by
  rw [completeIdentitySmoothAction, ← Category.assoc, lift_map,
    Category.comp_id]
  rfl

/-- Every test object sees equivariance for the actual original cyclic translation. -/
theorem completeIdentitySmoothAction_rotation_evaluation (b : ZMod n)
    {T : Over (Spec (.of (PowerSeries K)))} (x : T ⟶ (G).X) (y : T ⟶ (M)) :
    lift x (y ≫ translation (completeOriginalSmoothCyclicPoint K n h b)) ≫ (a) =
      lift x y ≫ (a) ≫ translation (completeOriginalSmoothCyclicPoint K n h b) := by
  rw [completeIdentitySmoothAction_evaluation, ← Category.assoc,
    completeIdentitySmoothAction_evaluation, comp_translation, comp_translation]
  exact mul_left_comm _ _ _

/-- Rotation of the second smooth input rotates the output by the same label. -/
@[reassoc] theorem completeIdentitySmoothAction_rotation (b : ZMod n) :
    (𝟙 (G).X ⊗ₘ translation (completeOriginalSmoothCyclicPoint K n h b)) ≫ (a) =
      (a) ≫ translation (completeOriginalSmoothCyclicPoint K n h b) := by
  have he := completeIdentitySmoothAction_rotation_evaluation K n h b
    (fst (G).X (M)) (snd (G).X (M))
  rw [← lift_fst_comp_snd_comp]
  simpa only [Category.comp_id, Category.id_comp, lift_fst_snd] using he

/-- The equivariance equation retains the whole-family rotation after smooth inclusion. -/
@[reassoc] theorem completeIdentitySmoothAction_rotation_inclusion (b : ZMod n) :
    (𝟙 (G).X ⊗ₘ translation (completeOriginalSmoothCyclicPoint K n h b)).left ≫
      (a).left ≫ (exactVeroneseProjToBase K n h).smoothLocus.ι =
        (a).left ≫ (exactVeroneseProjToBase K n h).smoothLocus.ι ≫
          completeRotation K n h b := by
  rw [← Category.assoc]
  have he := congrArg Over.Hom.left (completeIdentitySmoothAction_rotation K n h b)
  rw [Over.comp_left, Over.comp_left] at he
  rw [he, Category.assoc, completeOriginalSmooth_translation_rotation]

end FLT.Mazur.PolygonInfinitesimalStages
