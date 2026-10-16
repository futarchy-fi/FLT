/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicCubicPatches
public import FLT.Mazur.PolygonCompletePointStageNodeRatios
public import FLT.Mazur.PolygonOriginalNodeBasicOpen

/-!
# The original target marking open supplies the actual complete cubic Z chart

The Z chart pulls back to precisely the original target marking complement.
Every point in the explicit target denominator open therefore has a complete
affine Z-compatible refinement, with the original adic source patch retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "R" => completeIdentityActionAdicChartSpace K n h m i j
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h m i j ≫
  completeIdentityActionAdicLiftSpaceMap K n h m
local notation "p" => (pullback.snd _ _ : (R) ⟶ chart (Ring K m) (parameter K m))
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "f" => originalStageToCompatibleProj K n h m
local notation "d" => PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j

/-- The actual complete Z chart pulls back to the unchanged target marking complement. -/
theorem completeIdentityAdicCubicZ_preimage :
    (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 =
      (p) ⁻¹ᵁ completePointStageNodeOpen K n h m 0 j := by
  have he : (κ) ≫ pullback.snd (a) (g) = (p) ≫ (d) ≫ (f) := by
    simp only [Category.assoc, completeIdentityActionAdicLiftSpaceMap,
      pullback.lift_snd, completeIdentityActionAdicChartSpaceMap_snd_assoc]
  rw [completeIdentityCubicChartOpen, ← Scheme.Hom.comp_preimage, he,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    ← completePointStageComplement_preimage]
  rfl

/-- The original target denominator open lies entirely in the actual complete Z chart. -/
theorem completeIdentityAdicTargetDenominator_le_cubicZ :
    (p) ⁻¹ᵁ nodeMarkingBasicOpen (parameter K m) ≤
      (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 := by
  rw [completeIdentityAdicCubicZ_preimage]
  exact fun _ hx ↦ nodeMarkingBasicOpen_le_completePointStageNodeOpen K m n h 0 j hx

/-- Every point of that denominator open admits an original complete affine Z refinement. -/
theorem completeIdentityAdicCubicZPatch_at (x : R)
    (hx : (p) x ∈ nodeMarkingBasicOpen (parameter K m)) :
    ∃ U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens,
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j U).1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
        completeIdentityCubicChartOpen K n h 2 ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
        completeIdentityAdicNodeNeighborhood K n h m i j :=
  completeIdentityAdicCubicPatch_at K n h m i j x 2
    (completeIdentityAdicTargetDenominator_le_cubicZ K n h m i j hx)

end FLT.Mazur.PolygonInfinitesimalStages
