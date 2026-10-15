/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealNeighborhoodMembership
public import FLT.Mazur.PolygonCompleteIdentityFirstRefinedEquations
public import FLT.Mazur.PolygonCompleteIdentityFirstChartResidualNormalForm

/-!
# Exact refined complete-coordinate test for original error vanishing

The covering patches detect membership in the full original ambient ideal.
Consequently original coordinate-error vanishing is equivalent to explicit
complete parameter-torsion certificates, with no extra adic kernel term.
The certificates themselves remain to be constructed from the cubic action.
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

/-- Local vanishing of an actual error has an exact complete-ring power-torsion test. -/
theorem completeIdentityFirstRefinedError_local_iff
    (U : (O).toScheme.affineOpens)
    (hU : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
      completeIdentityAdicNodeNeighborhood K n h 1 0 0)
    (z : ChartRing (t)) :
    completeIdentityFirstAmbientRestriction K n h
      (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U)
      (completeIdentityFirstAmbientError K n h z) ∈
        (J).map (completeIdentityFirstAmbientRestriction K n h
          (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U)).hom ↔
      ∃ r, ∃ d : ℕ,
        (AffinePrincipalKernel.restriction
          (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U)
          (completeIdentityActionAmbientParameter K n h)) ^ d *
            ((D) U z - AffinePrincipalKernel.restriction
              (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U)
              (completeIdentityActionAmbientParameter K n h) * r) = 0 := by
  rw [← completeIdentityFirstCompleteError_mem_iff,
    completeIdentityFirstRefinedEquation_mem_iff K n h U hU]

/-- The refined complete certificates detect the unchanged global closed-fiber error exactly. -/
theorem completeIdentityFirstRefinedError_eq_zero_iff (z : ChartRing (t)) :
    (δ) z = 0 ↔ ∀ U : (O).toScheme.affineOpens,
      (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
        completeIdentityAdicNodeNeighborhood K n h 1 0 0 →
      ∃ r, ∃ d : ℕ,
        (AffinePrincipalKernel.restriction
          (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U)
          (completeIdentityActionAmbientParameter K n h)) ^ d *
            ((D) U z - AffinePrincipalKernel.restriction
              (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U)
              (completeIdentityActionAmbientParameter K n h) * r) = 0 := by
  rw [completeIdentityFirstChartClosedError_eq_zero_iff]
  constructor
  · intro hz U hU
    apply (completeIdentityFirstRefinedError_local_iff K n h U hU z).mp
    exact Ideal.mem_map_of_mem _ hz
  · intro hz
    apply AffineIdealNeighborhoodMembership.mem_of_neighborhoods
    intro x
    obtain ⟨U, hx, hU⟩ := completeIdentityAdicRefinedPatch_cover K n h 1 0 0 x
    exact ⟨completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U, hx,
      (completeIdentityFirstRefinedError_local_iff K n h U hU z).mpr (hz U hU)⟩

/-- Vanishing of the two actual original errors suffices for the original node comparison. -/
theorem completeIdentityFirstGraphToChart_isIso_of_coordinateErrors
    (hx : (δ) (leftCoordinate (t)) = 0) (hy : (δ) (rightCoordinate (t)) = 0) :
    IsIso (completeIdentityFirstGraphToChart K n h) := by
  apply completeIdentityFirstGraphToChart_isIso_of_residualCoordinates K n h
  intro a b _ _
  rw [hx, hy, mul_zero, mul_zero, add_zero]

end FLT.Mazur.PolygonInfinitesimalStages
