/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRotation
public import FLT.Mazur.PolygonOriginalStageAdicSquare
public import FLT.Mazur.PolygonRetainedSectionRotation

/-!
# Complete rotation retains the original stage embeddings

The actual evaluation square of graded rings gives the projective square.
Canonical retained recovery then identifies it with the original stage action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryRetainedRotation compatibleVeroneseRotation
  boundaryStageRetainedIso compatibleEval compatibleVeroneseEval

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original graded evaluation square commutes with the canonical retained rotation. -/
theorem boundaryVeroneseEvaluation_rotation (m : ℕ) (a : ZMod n) :
    (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m).comp
        (completeRotationGradedMap K n h a) =
      (boundaryRetainedRotation K n h m a).comp
        (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m) := by
  apply GradedRingHom.ext
  intro s
  apply Subtype.ext
  change compatibleVeroneseEval K n h (exactVeroneseStep K n h) m
    (compatibleVeroneseRotation K n h (exactVeroneseStep K n h) a s) =
      (boundaryRetainedRotation K n h m a
        (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m s)).val
  rw [boundaryRetainedRotation_val]
  exact compatibleVeroneseRotation_eval K n h (exactVeroneseStep K n h) a m s

/-- The stage-to-complete Proj map intertwines the actual constructed projective actions. -/
@[reassoc] theorem boundaryVeroneseProjToCompatible_rotation (m : ℕ) (a : ZMod n) :
    boundaryVeroneseProjToCompatible K n h m ≫ completeRotation K n h a =
      Proj.map (boundaryRetainedRotation K n h m a)
        (boundaryRetainedRotation_irrelevant K n h m a) ≫
          boundaryVeroneseProjToCompatible K n h m := by
  change Proj.map (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m) _ ≫
      Proj.map (completeRotationGradedMap K n h a) _ = _
  unfold boundaryVeroneseProjToCompatible
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [boundaryVeroneseEvaluation_rotation]

/-- The complete cyclic action restricts to the actual rotation of every original stage. -/
@[reassoc] theorem originalStageToCompatibleProj_rotation (m : ℕ) (a : ZMod n) :
    originalStageToCompatibleProj K n h m ≫ completeRotation K n h a =
      stageRotation K n h m a ≫ originalStageToCompatibleProj K n h m := by
  rw [originalStageToCompatibleProj, Category.assoc,
    boundaryVeroneseProjToCompatible_rotation,
    boundaryStageRetainedIso_rotation_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
