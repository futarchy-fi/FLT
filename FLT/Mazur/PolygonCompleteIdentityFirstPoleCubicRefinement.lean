/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicCubicZNeighborhood
public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchGeometry

/-!
# Complete cubic Z refinements at every original common pole point

Every point of the unchanged common pole localization lies in the actual
complete Z chart. Hence a compatible complete affine refinement exists there,
without imposing cubic compatibility on the starting affine patch.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "M" => completeIdentityFirstPolePatchMap K n h U
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "p" => (pullback.snd _ _ : (R) ⟶ chart (Ring K 1) (t))
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1

/-- Every actual common pole point has its target in the original marking-denominator open. -/
theorem completeIdentityFirstPolePatch_target_mem (z : Spec (.of (Z))) :
    (p) ((V).1.ι ((M) z)) ∈ nodeMarkingBasicOpen (t) := by
  change ((M) ≫ (V).1.ι ≫ (p)) z ∈ nodeMarkingBasicOpen (t)
  rw [completeIdentityFirstPolePatchMap_target]
  change (Q) ((η) (nodeMarkingDenominator (t))) ∉ z.asIdeal
  intro hz
  exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem z.asIdeal hz
    ((IsLocalization.Away.algebraMap_isUnit (nodeMarkingDenominator (t))).map (Q)))

/-- Cubic Z compatibility holds on the entire original common pole localization. -/
theorem completeIdentityFirstPolePatch_mem_cubicZ (z : Spec (.of (Z))) :
    (κ) ((V).1.ι ((M) z)) ∈ completeIdentityCubicChartOpen K n h 2 :=
  completeIdentityAdicTargetDenominator_le_cubicZ K n h 1 0 0
    (completeIdentityFirstPolePatch_target_mem K n h U z)

/-- Each common pole point has an actual compatible complete affine neighborhood. -/
theorem completeIdentityFirstPolePatch_cubicZ_refinement (z : Spec (.of (Z))) :
    ∃ W : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens,
      (V).1.ι ((M) z) ∈ (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 W).1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 W).1 ≤
        completeIdentityCubicChartOpen K n h 2 ∧
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 W).1 ≤
        completeIdentityAdicNodeNeighborhood K n h 1 0 0 :=
  completeIdentityAdicCubicZPatch_at K n h 1 0 0 _
    (completeIdentityFirstPolePatch_target_mem K n h U z)

end FLT.Mazur.PolygonInfinitesimalStages
