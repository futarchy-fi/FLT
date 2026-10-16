/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstRefinedErrorCriterion
public import FLT.Mazur.PolygonCompleteIdentityAdicCubicPatches

/-!
# Detect original node errors on the actual cubic coordinate patches

The cubic-compatible refined patches cover the full original node-pair
relation. Thus complete error certificates need only be constructed on
patches carrying the actual normalized cubic action coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstChartClosedError
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h
local notation "O" => completeIdentityActionAdicChartAmbientOpen K n h 1 0 0
local notation "δ" => completeIdentityFirstChartClosedError K n h
local notation "D" => completeIdentityFirstCompleteError K n h
local notation "t" => parameter K 1

/-- Cubic-compatible complete certificates detect the unchanged original error exactly. -/
theorem completeIdentityFirstCubicError_eq_zero_iff (z : ChartRing (t)) :
    (δ) z = 0 ↔ ∀ (k : Fin 3) (U : (O).toScheme.affineOpens),
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
        completeIdentityAdicNodeNeighborhood K n h 1 0 0 →
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
        completeIdentityCubicChartOpen K n h k →
      ∃ r, ∃ d : ℕ,
        (AffinePrincipalKernel.restriction
          (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U)
          (completeIdentityActionAmbientParameter K n h)) ^ d *
            ((D) U z - AffinePrincipalKernel.restriction
              (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U)
              (completeIdentityActionAmbientParameter K n h) * r) = 0 := by
  rw [completeIdentityFirstChartClosedError_eq_zero_iff]
  constructor
  · intro hz k U hU _
    apply (completeIdentityFirstRefinedError_local_iff K n h U hU z).mp
    exact Ideal.mem_map_of_mem _ hz
  · intro hz
    apply AffineIdealNeighborhoodMembership.mem_of_neighborhoods
    intro x
    obtain ⟨k, U, hx, hC, hU⟩ := completeIdentityAdicCubicPatch_cover K n h 1 0 0 x
    exact ⟨completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U, hx,
      (completeIdentityFirstRefinedError_local_iff K n h U hU z).mpr (hz k U hU hC)⟩

end FLT.Mazur.PolygonInfinitesimalStages
