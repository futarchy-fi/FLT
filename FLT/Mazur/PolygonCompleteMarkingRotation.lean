/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteStageRotation
public import FLT.Mazur.PowerSeriesSchemePointExt

/-!
# Complete rotation carries the reconstructed original markings

The geometric stage square and uniqueness over the power-series base lift
all original labeled marking equations to the complete projective family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj completeBaseMarking

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every original finite-stage marking is carried to its actual cyclically shifted label. -/
@[reassoc] theorem stageMarking_rotation (m : ℕ) (a : ZMod n) (i : Fin n) :
    marking K m n h i ≫ stageRotation K n h m a =
      marking K m n h (rotateIndex a i) :=
  PolygonInfinitesimal.marking_rotation (Ring K m) (parameter K m) n h a i 1

/-- The constructed complete automorphism rotates every reconstructed original marking. -/
@[reassoc] theorem completeBaseMarking_rotation (a : ZMod n) (i : Fin n) :
    completeBaseMarking K n h i ≫ completeRotation K n h a =
      completeBaseMarking K n h (rotateIndex a i) := by
  apply powerSeriesPoint_ext K
  intro m
  rw [baseToSeries_completeBaseMarking_assoc, originalStageToCompatibleProj_rotation,
    stageMarking_rotation_assoc, baseToSeries_completeBaseMarking]

end FLT.Mazur.PolygonInfinitesimalStages
