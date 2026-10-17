/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphChartRotation

/-!
# Isomorphisms between the actual rotated graph charts

The inverse is the original negative rotation. Both coordinates of each
chart isomorphism are the identity on the unchanged node schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
  (b : ZMod n) (i j k l : Fin n) (hi : rotateIndex b i = k) (hj : rotateIndex b j = l)

include hi in
/-- Negative rotation restores an original label from its specified rotated label. -/
theorem completeIdentityGraphChartRotation_inverseLabel : rotateIndex (-b) k = i := by
  rw [← hi, ← rotateIndex_add, add_neg_cancel, rotateIndex_zero]

/-- The original graph chart and its simultaneous relabeling are isomorphic. -/
def completeIdentityGraphChartRotationIso :
    completeIdentityActionGraphAdicChart K n h m i j ≅
      completeIdentityActionGraphAdicChart K n h m k l where
  hom := completeIdentityGraphChartRotation K n h m b i j k l hi hj
  inv := completeIdentityGraphChartRotation K n h m (-b) k l i j
    (completeIdentityGraphChartRotation_inverseLabel n b i k hi)
    (completeIdentityGraphChartRotation_inverseLabel n b j l hj)
  hom_inv_id := by
    apply (cancel_mono (completeIdentityActionGraphAdicChartInclusion K n h m i j)).mp
    rw [Category.assoc, completeIdentityGraphChartRotation_inclusion,
      completeIdentityGraphChartRotation_inclusion_assoc,
      ← completeIdentityAdicGraphRotation_add, add_neg_cancel,
      completeIdentityAdicGraphRotation_zero, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (completeIdentityActionGraphAdicChartInclusion K n h m k l)).mp
    rw [Category.assoc, completeIdentityGraphChartRotation_inclusion,
      completeIdentityGraphChartRotation_inclusion_assoc,
      ← completeIdentityAdicGraphRotation_add, neg_add_cancel,
      completeIdentityAdicGraphRotation_zero, Category.comp_id, Category.id_comp]

instance completeIdentityGraphChartRotation_isIso :
    IsIso (completeIdentityGraphChartRotation K n h m b i j k l hi hj) :=
  (completeIdentityGraphChartRotationIso K n h m b i j k l hi hj).isIso_hom

include hi hj in
/-- Rotation transports source invertibility between literal original graph charts. -/
theorem completeIdentityGraphChartSource_isIso_of_rotation
    [IsIso (completeIdentityActionGraphAdicChartSource K n h m i j)] :
    IsIso (completeIdentityActionGraphAdicChartSource K n h m k l) := by
  have : IsIso (completeIdentityGraphChartRotation K n h m b i j k l hi hj ≫
      completeIdentityActionGraphAdicChartSource K n h m k l) := by
    rw [completeIdentityGraphChartRotation_source]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (completeIdentityGraphChartRotation K n h m b i j k l hi hj) _

end FLT.Mazur.PolygonInfinitesimalStages
