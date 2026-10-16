/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourceNodeGraphQuotient
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceIncomingComparison

/-!
# Incoming error certificates in the full original source-node ideals

The full original graph ideal and source-node equations imply incoming
target and error membership in that same ideal. No target denominator is inverted.
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
variable (hI : (completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).ker.ideal
  (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U) ≤ I)
local notation "q" => Ideal.Quotient.mk I

local notation "φ" => completeIdentityFirstSourceNodeQuotientLift K n h U I hx hy
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "Q" => completeIdentityFirstSourcePoleTargetFunctions K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)

include hx hy hI

/-- The full original source-node quotient kills the actual incoming target coordinate. -/
theorem completeIdentityFirstSourceNode_incoming_target_mem :
    completeIdentityFirstPoleTarget K n h U (rightCoordinate (t)) ∈ I := by
  have hp : (φ) (completeIdentityFirstSourcePoleParameter K n h U) = 0 := by
    rw [completeIdentityFirstSourcePoleParameter,
      completeIdentityFirstSourceNodeQuotientLift_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (completeIdentityFirstSourceNodeQuotient_parameter K n h U I hx)
  have hs : (φ) ((S) ((η) (rightCoordinate (t)))) = 0 := by
    rw [completeIdentityFirstSourcePoleFunctions_algebraMap,
      completeIdentityFirstSourceNodeQuotientLift_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  let w := completeIdentityFirstSourceNodeQuotientToGraph K n h U I hI
  have hw := completeIdentityFirstSourceNodeQuotientToGraph_sourcePole K n h U I hI hx hy
  have he := completeIdentityFirstSourcePole_incoming_zero K n h U (φ) hp w hw hs
  change (φ) ((ι) (completeIdentityFirstPoleTarget K n h U (rightCoordinate (t)))) = 0 at he
  rw [completeIdentityFirstSourceNodeQuotientLift_algebraMap] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he

/-- Its original incoming ambient error belongs to that very same ideal. -/
theorem completeIdentityFirstSourceNode_incoming_error_mem :
    (ρ) (completeIdentityFirstAmbientError K n h (rightCoordinate (t))) ∈ I := by
  have he : (ρ) (completeIdentityFirstAmbientError K n h (rightCoordinate (t))) =
      completeIdentityFirstPoleTarget K n h U (rightCoordinate (t)) -
        (s) (rightCoordinate (t)) := by
    simp only [completeIdentityFirstAmbientError, completeIdentityFirstPoleTarget,
      completeIdentityFirstPoleSource, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_sub]
  rw [he]
  exact I.sub_mem (completeIdentityFirstSourceNode_incoming_target_mem K n h U I hx hy hI) hy

/-- The actual incoming target marking denominator is one in the full source-node quotient. -/
theorem completeIdentityFirstSourceNode_target_right_denominator :
    (q) (1 - completeIdentityFirstPoleTarget K n h U (rightCoordinate (t))) = 1 := by
  rw [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr
    (completeIdentityFirstSourceNode_incoming_target_mem K n h U I hx hy hI), sub_zero]

end FLT.Mazur.PolygonInfinitesimalStages
