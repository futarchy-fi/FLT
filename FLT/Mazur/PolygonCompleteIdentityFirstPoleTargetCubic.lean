/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchGeometry
public import FLT.Mazur.PolygonCompletePointNodeCubicChart
public import FLT.Mazur.PolygonCompleteIdentityAdicCubicChartMap

/-!
# The original target pole map is the specialized complete cubic map

On the common pole neighborhood of a Z-chart-compatible affine patch,
the target pole map and the original specialized complete action are the
same morphism to the actual cubic chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h 2)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "M" => completeIdentityFirstPolePatchMap K n h U
local notation "c" => completeIdentityAdicCubicChartMap K n h 1 0 0 U 2 hC

/-- The unchanged target poles give exactly the actual specialized complete action chart. -/
theorem completeIdentityFirstPoleTarget_cubicChart :
    Spec.map (CommRingCat.ofHom (Q)) ≫ completePointNodeToCubicChart K n h 1 0 0 =
      (M) ≫ (c) := by
  apply (cancel_mono (integralCurveChart (E) 2)).mp
  rw [Category.assoc, completePointNodeToCubicChart_inclusion,
    Category.assoc, completeIdentityAdicCubicChartMap_target]
  simp only [Category.assoc, completeIdentityActionAdicLiftSpaceMap,
    pullback.lift_snd_assoc, completeIdentityActionAdicChartSpaceMap_snd_assoc]
  rw [completeIdentityFirstPolePatchMap_target_assoc]

/-- The original target pole homomorphism is the specialized complete cubic homomorphism. -/
theorem completeIdentityFirstPoleTarget_cubicFunctions :
    (Q).comp (completePointNodeCubicFunctions K n h 1 0 0) =
      (ι).comp (completeIdentityAdicCubicFunctions K n h 1 0 0 U 2 hC) := by
  have he := congrArg (fun f ↦ (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv ≫
    f.appTop ≫ (Scheme.ΓSpecIso (.of (Z))).hom)
    (completeIdentityFirstPoleTarget_cubicChart K n h U hC)
  simp only [Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, completeIdentityFirstPolePatchMap_appTop,
    Iso.inv_hom_id, Category.comp_id] at he
  have hf := completeIdentityAdicCubicChartMap_functions K n h 1 0 0 U 2 hC
  rw [← hf]
  exact congrArg CommRingCat.Hom.hom he

end FLT.Mazur.PolygonInfinitesimalStages
