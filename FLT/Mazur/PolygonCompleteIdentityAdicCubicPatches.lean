/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionRefinedOpenPatches
public import FLT.Mazur.PolygonCompleteIdentityAdicRefinedPatches
public import FLT.Mazur.PolygonCompleteIdentityCubicChartMaps

/-!
# Original refined node patches carrying the actual cubic coordinates

Every original adic node-pair point has a complete affine neighborhood
inside an actual cubic coordinate open, with no unwanted adic points.
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
local notation "C" k => completeIdentityCubicChartOpen K n h k

/-- Refined patches can be chosen inside any cubic chart containing the original point. -/
theorem completeIdentityAdicCubicPatch_at
    (x : completeIdentityActionAdicChartSpace K n h m i j)
    (k : Fin 3) (hx : ((a) ≫ (f)) x ∈ C k) :
    ∃ U : (O).toScheme.affineOpens,
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j U).1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤ (C k) ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
        completeIdentityAdicNodeNeighborhood K n h m i j :=
  ClosedImmersionOpenNeighborhood.exists_refined_patch_in (a) (f) x (C k) hx

/-- The cubic-compatible refined patches still cover the full original node-pair relation. -/
theorem completeIdentityAdicCubicPatch_cover
    (x : completeIdentityActionAdicChartSpace K n h m i j) :
    ∃ (k : Fin 3) (U : (O).toScheme.affineOpens),
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j U).1 ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤ (C k) ∧
      (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
        completeIdentityAdicNodeNeighborhood K n h m i j := by
  have hx : ((a) ≫ (f)) x ∈ ⨆ k, C k := by
    rw [completeIdentityCubicChartOpen_cover]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨U, hu⟩ := completeIdentityAdicCubicPatch_at K n h m i j x k hk
  exact ⟨k, U, hu⟩

end FLT.Mazur.PolygonInfinitesimalStages
