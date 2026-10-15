/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionOpenNeighborhood
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientLifts

/-!
# Refined complete neighborhoods of the original adic node-pair relation

These patches cover every original node-pair point. Unlike unrestricted
coborder patches, their entire inverse image in the whole adic relation
belongs to that node-pair open. All original morphisms are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "a" => completeIdentityActionAdicChartSpaceMap K n h m i j
local notation "f" => completeIdentityActionAdicLiftSpaceMap K n h m
local notation "O" => completeIdentityActionAdicChartAmbientOpen K n h m i j

/-- The actual complete open obtained by removing the other original adic points. -/
abbrev completeIdentityAdicNodeNeighborhood :=
  ClosedImmersionOpenNeighborhood.neighborhood (a) (f)

/-- The whole adic inverse image is exactly the unchanged original node-pair open. -/
theorem completeIdentityAdicNodeNeighborhood_preimage :
    (f) ⁻¹ᵁ completeIdentityAdicNodeNeighborhood K n h m i j = (a).opensRange :=
  ClosedImmersionOpenNeighborhood.preimage_neighborhood (a) (f)

/-- Every original coborder patch refines to patches with no unwanted adic points. -/
theorem completeIdentityAdicAmbientPatch_refine
    (x : completeIdentityActionAdicChartSpace K n h m i j)
    (U : (O).toScheme.affineOpens)
    (hx : x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j U).1) :
    ∃ V : (O).toScheme.affineOpens,
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j V).1 ∧ V.1 ≤ U.1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j V).1 ≤
        completeIdentityAdicNodeNeighborhood K n h m i j :=
  ClosedImmersionOpenNeighborhood.exists_refined_patch (a) (f) x U.1 hx

/-- The refined complete patches cover every point of the original adic node-pair relation. -/
theorem completeIdentityAdicRefinedPatch_cover
    (x : completeIdentityActionAdicChartSpace K n h m i j) :
    ∃ U : (O).toScheme.affineOpens,
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j U).1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
        completeIdentityAdicNodeNeighborhood K n h m i j := by
  obtain ⟨U, hx⟩ := completeIdentityAdicAmbientPatch_cover K n h m i j x
  obtain ⟨V, hv, _, hn⟩ := completeIdentityAdicAmbientPatch_refine K n h m i j x U hx
  exact ⟨V, hv, hn⟩

/-- Every whole-adic point over a refined patch is already an original node-pair point. -/
theorem completeIdentityAdicRefinedPatch_preimage
    (U : (O).toScheme.affineOpens)
    (hU : (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
      completeIdentityAdicNodeNeighborhood K n h m i j) :
    (f) ⁻¹ᵁ (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤ (a).opensRange :=
  ClosedImmersionOpenNeighborhood.preimage_le_range (a) (f) _ hU

end FLT.Mazur.PolygonInfinitesimalStages
