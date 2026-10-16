/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourceNodeCubicCoverage
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceOutgoingVanishing

/-!
# Outgoing error certificates in the full original source-node ideals

The source-only factorization transports target and error vanishing back
to the unchanged affine quotient. No target denominator is inverted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)

local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "d" => nodeMarkingDenominator (t)
local notation "A" => Γ((R), (V).1)
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ι" => algebraMap (A) (Z)
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1
variable (I : Ideal Γ(completeIdentityActionAdicChartSpace K n h 1 0 0,
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1))
variable (hx : completeIdentityFirstPoleSource K n h U (leftCoordinate (parameter K 1)) ∈ I)
variable (hy : completeIdentityFirstPoleSource K n h U (rightCoordinate (parameter K 1)) ∈ I)
local notation "q" => Ideal.Quotient.mk I

local notation "φ" => completeIdentityFirstSourceNodeQuotientLift K n h U I hx hy
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "Q" => completeIdentityFirstSourcePoleTargetFunctions K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)

include hx hy

/-- The full original source-node quotient kills the actual outgoing target coordinate. -/
theorem completeIdentityFirstSourceNode_target_mem :
    completeIdentityFirstPoleTarget K n h U (leftCoordinate (t)) ∈ I := by
  have hp : (φ) (completeIdentityFirstSourcePoleParameter K n h U) = 0 := by
    rw [completeIdentityFirstSourcePoleParameter,
      completeIdentityFirstSourceNodeQuotientLift_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (completeIdentityFirstSourceNodeQuotient_parameter K n h U I hx)
  have hs : (φ) ((S) ((η) (leftCoordinate (t)))) = 0 := by
    rw [completeIdentityFirstSourcePoleFunctions_algebraMap,
      completeIdentityFirstSourceNodeQuotientLift_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have he := completeIdentityFirstSourcePole_outgoing_zero K n h U (φ) hp hs
  change (φ) ((ι) (completeIdentityFirstPoleTarget K n h U (leftCoordinate (t)))) = 0 at he
  rw [completeIdentityFirstSourceNodeQuotientLift_algebraMap] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he

/-- Its original outgoing ambient error belongs to that very same ideal. -/
theorem completeIdentityFirstSourceNode_error_mem :
    (ρ) (completeIdentityFirstAmbientError K n h (leftCoordinate (t))) ∈ I := by
  have he : (ρ) (completeIdentityFirstAmbientError K n h (leftCoordinate (t))) =
      completeIdentityFirstPoleTarget K n h U (leftCoordinate (t)) -
        (s) (leftCoordinate (t)) := by
    simp only [completeIdentityFirstAmbientError, completeIdentityFirstPoleTarget,
      completeIdentityFirstPoleSource, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_sub]
  rw [he]
  exact I.sub_mem (completeIdentityFirstSourceNode_target_mem K n h U I hx hy) hx

/-- The actual outgoing target marking denominator is one in the full source-node quotient. -/
theorem completeIdentityFirstSourceNode_target_left_denominator :
    (q) (1 - completeIdentityFirstPoleTarget K n h U (leftCoordinate (t))) = 1 := by
  rw [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr
    (completeIdentityFirstSourceNode_target_mem K n h U I hx hy), sub_zero]

end FLT.Mazur.PolygonInfinitesimalStages
