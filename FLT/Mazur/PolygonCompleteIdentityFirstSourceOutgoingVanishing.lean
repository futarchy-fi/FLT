/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourceTargetComplement
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceTargetFunctions
public import FLT.Mazur.PolygonCompletePointFirstComplementNodeExtraction

/-!
# Outgoing target vanishing on every source-only node specialization

The actual complement map, cubic comparison, and coefficient equality
supply outgoing target and error certificates in arbitrary receiving rings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "F" => completeIdentityFirstSourcePoleInputFunctions K n h U
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h 1 0 0
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityFirstSourcePolePatch K n h U →+* B)
variable (hf : φ (completeIdentityFirstSourcePoleParameter K n h U) = 0)

local notation "Q" => completeIdentityFirstSourcePoleTargetFunctions K n h U
local notation "η" => algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
local notation "v" => completeIdentityFirstSourcePoleTargetComplement K n h U φ hf
local notation "N" => completePointStageNodeOpen K n h 1 0 0

include hf

/-- Source-node vanishing forces actual target outgoing vanishing, including nilpotents. -/
theorem completeIdentityFirstSourcePole_outgoing_zero
    (hx : φ ((S) ((η) (leftCoordinate (parameter K 1)))) = 0) :
    φ ((Q) (leftCoordinate (parameter K 1))) = 0 := by
  have hv : (v) ≫ (N).ι = Spec.map (CommRingCat.ofHom (φ.comp (Q))) := by
    rw [completeIdentityFirstSourcePoleTargetComplement_inclusion K n h U φ hf,
      CommRingCat.ofHom_comp, Spec.map_comp,
      completeIdentityFirstSourcePoleTargetFunctions_map K n h U]
  obtain ⟨h₂, h₃⟩ := completeIdentityFirstSourcePole_complementPoles K n h U φ hf
  apply completePointFirstComplementPoles_target_zero K n h (0 : Fin n)
    (φ.comp (Q)) (v) hv (φ.comp (S))
    (fun a ↦ congrArg φ (completeIdentityFirstSourcePoleTargetFunctions_coefficients K n h U a))
    h₂.symm h₃.symm hx

/-- The unchanged original outgoing error vanishes on those same full receiving rings. -/
theorem completeIdentityFirstSourcePole_outgoing_error_zero
    (hx : φ ((S) ((η) (leftCoordinate (parameter K 1)))) = 0) :
    φ ((ι) ((ρ) (completeIdentityFirstAmbientError K n h
      (leftCoordinate (parameter K 1))))) = 0 := by
  rw [← completeIdentityFirstSourcePoleTargetFunctions_error, φ.map_sub,
    completeIdentityFirstSourcePole_outgoing_zero K n h U φ hf hx, hx, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages
