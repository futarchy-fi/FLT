/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteWholeActionEvaluation

/-!
# Cyclic translations of the whole original polygon

The full action recovers the unchanged original cyclic rotations on every
input, including nodes. Consequently the original marking labels are retained.
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
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "j" => completeWholeSmoothInclusion K n h

/-- A cyclic marking translates the entire original polygon by its original rotation. -/
theorem completeWholeTranslation_cyclic (b : ZMod n) :
    completeWholeTranslation K n h (completeOriginalSmoothCyclicPoint K n h b) =
      completeWholeRotationOver K n h b := by
  let _ : Flat (X).hom := exactVeroneseProjToBase_flat K n h
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated (X).hom := inferInstanceAs
    (IsSeparated (exactVeroneseProjToBase K n h))
  have hr : translation (completeOriginalSmoothCyclicPoint K n h b) ≫ (j) =
      (j) ≫ completeWholeRotationOver K n h b := by
    apply Over.OverMorphism.ext
    exact completeOriginalSmooth_translation_rotation K n h b
  apply completeRelative_smooth_ext K n h (𝟙 (X))
  intro U u y hy
  simp only [Category.comp_id] at hy
  rw [completeWholeTranslation_evaluation, hy, completeWholeAction_smooth_evaluation,
    Category.assoc y, ← hr, ← Category.assoc]
  congr 1
  exact (comp_translation y (completeOriginalSmoothCyclicPoint K n h b)).symm

/-- Cyclic action retains every original complete marking, with its actual rotated label. -/
@[reassoc] theorem completeWholeTranslation_cyclic_marking (b : ZMod n) (i : Fin n) :
    completeBaseMarking K n h i ≫
      (completeWholeTranslation K n h (completeOriginalSmoothCyclicPoint K n h b)).left =
        completeBaseMarking K n h (PolygonPinching.rotateIndex b i) := by
  rw [completeWholeTranslation_cyclic]
  exact completeBaseMarking_rotation K n h b i

end FLT.Mazur.PolygonInfinitesimalStages
