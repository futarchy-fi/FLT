/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicNodeSourceIso
public import FLT.Mazur.PolygonCompleteIdentityGraphChartRotationIso

/-!
# Every positive-order same-label node chart has its original source inverse

Rotation transports the identity-node inverse to every original node label.
The inverse is the constructed whole-node section, and its target is the
full original reciprocal scaling, retaining all nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i : Fin n)

/-- Every literal positive-order same-label graph chart projects isomorphically to its node. -/
theorem completeIdentityActionGraphAdicNodeSource_isIso :
    IsIso (completeIdentityActionGraphAdicChartSource K n h (m + 1) i i) := by
  let _ := completeIdentityActionGraphAdicIdentitySource_isIso K n h m
  have hi : rotateIndex (ZMod.finEquiv n i) (0 : Fin n) = i := by
    simp only [rotateIndex, map_zero, zero_add, RingEquiv.symm_apply_apply]
  exact completeIdentityGraphChartSource_isIso_of_rotation K n h (m + 1)
    (ZMod.finEquiv n i) 0 0 i i hi hi

/-- Each full original source node has a flat same-label graph projection. -/
theorem completeIdentityActionGraphAdicNodeSource_flat :
    Flat (completeIdentityActionGraphAdicChartSource K n h (m + 1) i i) := by
  let _ := completeIdentityActionGraphAdicNodeSource_isIso K n h m i
  infer_instance

/-- The actual original node section is the inverse at every node label. -/
@[reassoc] theorem completeIdentityAdicNodeSection_inverse :
    completeIdentityActionGraphAdicChartSource K n h (m + 1) i i ≫
      completeIdentityAdicNodeSection K n h (m + 1) i = 𝟙 _ := by
  let _ := completeIdentityActionGraphAdicNodeSource_isIso K n h m i
  apply (cancel_mono (completeIdentityActionGraphAdicChartSource K n h (m + 1) i i)).mp
  rw [Category.assoc, completeIdentityAdicNodeSection_source, Category.comp_id,
    Category.id_comp]

/-- Every target function on every same-label graph chart is the original universal scaling. -/
@[reassoc] theorem completeIdentityAdicNode_target :
    completeIdentityActionGraphAdicChartTarget K n h (m + 1) i i =
      completeIdentityActionGraphAdicChartSource K n h (m + 1) i i ≫
        Spec.map (CommRingCat.ofHom
          (PolygonSmoothing.universalReciprocalScale (parameter K (m + 1)))) := by
  rw [← completeIdentityAdicNodeSection_target K n h (m + 1) i,
    ← Category.assoc, completeIdentityAdicNodeSection_inverse, Category.id_comp]

/-- The section is an isomorphism onto the entire literal same-label graph chart. -/
theorem completeIdentityAdicNodeSection_isIso :
    IsIso (completeIdentityAdicNodeSection K n h (m + 1) i) := by
  let _ := completeIdentityActionGraphAdicNodeSource_isIso K n h m i
  have : IsIso (completeIdentityAdicNodeSection K n h (m + 1) i ≫
      completeIdentityActionGraphAdicChartSource K n h (m + 1) i i) := by
    rw [completeIdentityAdicNodeSection_source]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (completeIdentityActionGraphAdicChartSource K n h (m + 1) i i)

end FLT.Mazur.PolygonInfinitesimalStages
