/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAllPositiveLaws
public import FLT.Mazur.PolygonCompleteIdentityAdicNodeSections
public import FLT.Mazur.PolygonTopNodeGraphSourceIso

/-!
# The literal positive-order identity node graph projects isomorphically to its input

The all-order original law gives preservation by the full node action.
Together with the proved comparison with the entire literal graph chart,
this identifies its projection to the full source node, not merely its
coefficient-base map. Other complete graph charts are not covered here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)

/-- The actual finite branch graph has an inverse over its entire unchanged original node. -/
theorem completeIdentityTopGraphSchemeSource_isIso :
    IsIso (completeIdentityTopGraphSchemeSource K n h 0 m) := by
  apply topNodeGraphSchemeSource_isIso_of_preserves
  exact completeIdentityTopGraphOriginalFlat_preserves K n h 0 m
    (completeIdentityFiniteMulDefect_all K n h m)
    (completeIdentityTopGraphOriginalScalars_flat K n h m
      (completeIdentityFiniteMulDefect_all K n h m))

/-- The literal identity-node chart projects isomorphically onto the full original input node. -/
theorem completeIdentityActionGraphAdicIdentitySource_isIso :
    IsIso (completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0) := by
  let _ := completeIdentityTopGraphSchemeSource_isIso K n h m
  let _ := completeIdentityTopGraphToChart_isIso K n h m
    (completeIdentityFiniteMulDefect_all K n h m)
  have : IsIso (completeIdentityTopGraphToChart K n h m ≫
      completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0) := by
    rw [completeIdentityTopGraphToChart_source]
    infer_instance
  exact IsIso.of_isIso_comp_left (completeIdentityTopGraphToChart K n h m) _

/-- In particular this is flatness over the whole original input node at every positive order. -/
theorem completeIdentityActionGraphAdicIdentitySource_flat :
    Flat (completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0) := by
  let _ := completeIdentityActionGraphAdicIdentitySource_isIso K n h m
  infer_instance

/-- The actual node section is the inverse on the full literal identity graph chart. -/
@[reassoc] theorem completeIdentityAdicIdentityNodeSection_inverse :
    completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 ≫
      completeIdentityAdicNodeSection K n h (m + 1) 0 = 𝟙 _ := by
  let _ := completeIdentityActionGraphAdicIdentitySource_isIso K n h m
  apply (cancel_mono (completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0)).mp
  rw [Category.assoc, completeIdentityAdicNodeSection_source, Category.comp_id,
    Category.id_comp]

/-- Every target function on the literal graph chart is the original reciprocal scaling. -/
@[reassoc] theorem completeIdentityAdicIdentityNode_target :
    completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 =
      completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 ≫
        Spec.map (CommRingCat.ofHom
          (PolygonSmoothing.universalReciprocalScale (parameter K (m + 1)))) := by
  rw [← completeIdentityAdicNodeSection_target K n h (m + 1) 0,
    ← Category.assoc, completeIdentityAdicIdentityNodeSection_inverse, Category.id_comp]

end FLT.Mazur.PolygonInfinitesimalStages
