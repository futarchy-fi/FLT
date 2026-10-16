/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourceIncomingComparison
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceOutgoingVanishing
public import FLT.Mazur.PolygonCompletePointFirstIncomingLocalEquality
public import FLT.Mazur.PolygonCompletePointFirstOutgoingLocalEquality

/-!
# Exact source-node coordinate comparison in full local graph tests

The original cubic comparisons identify both coordinates in every local
receiving ring at the source node. No reduction of the graph or receiving
ring is taken and neither target denominator is inverted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
open PolygonSmoothing PolygonInfinitesimal WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "F" => completeIdentityFirstSourcePoleInputFunctions K n h U
local notation "Q" => completeIdentityFirstSourcePoleTargetFunctions K n h U
local notation "p" => Equiv.symm (finRotate n) (0 : Fin n)
local notation "b" => ZMod.finEquiv n (p)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h 1 0 (p)
local notation "a" => PolygonInfinitesimal.chart (Ring K 1) (t) n h (p)
local notation "r" => originalStageToCompatibleProj K n h 1
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityFirstSourcePolePatch K n h U →+* B)
variable (hf : φ (completeIdentityFirstSourcePoleParameter K n h U) = 0)
variable (w : Spec (.of B) ⟶ completeIdentityActionGraphAdicChart K n h 1 0 0)
variable (hw : w ≫ completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0 =
  Spec.map (CommRingCat.ofHom φ) ≫ completeIdentityFirstSourcePolePatchMap K n h U ≫
    Scheme.Opens.ι ((completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1))

variable [IsLocalRing B]
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)

include hf

/-- The outgoing error vanishes in the full local ring at a source-node point. -/
theorem completeIdentityFirstSourcePole_outgoing_eq_of_source_mem
    (hx : φ (completeIdentityFirstSourcePoleFunctions K n h U
      (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
        (leftCoordinate (parameter K 1)))) ∈ IsLocalRing.maximalIdeal B) :
    φ ((Q) (leftCoordinate (t))) = φ ((S) ((η) (leftCoordinate (t)))) := by
  let v := completeIdentityFirstSourcePoleTargetComplement K n h U φ hf
  have hv : v ≫ (completePointStageNodeOpen K n h 1 0 0).ι =
      Spec.map (CommRingCat.ofHom (φ.comp (Q))) := by
    rw [completeIdentityFirstSourcePoleTargetComplement_inclusion K n h U φ hf,
      CommRingCat.ofHom_comp, Spec.map_comp,
      completeIdentityFirstSourcePoleTargetFunctions_map K n h U]
  obtain ⟨h₂, h₃⟩ := completeIdentityFirstSourcePole_complementPoles K n h U φ hf
  exact completePointFirstComplementPoles_eq_of_source_mem K n h 0
    (φ.comp (Q)) v hv (φ.comp (S))
    (fun c ↦ congrArg φ (completeIdentityFirstSourcePoleTargetFunctions_coefficients K n h U c))
    h₂.symm h₃.symm hx

include hw

/-- The rotated full-graph comparison also identifies the incoming coordinate locally. -/
theorem completeIdentityFirstSourcePole_incoming_eq_of_source_mem
    (hy : φ (completeIdentityFirstSourcePoleFunctions K n h U
      (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
        (rightCoordinate (parameter K 1)))) ∈ IsLocalRing.maximalIdeal B) :
    φ ((Q) (rightCoordinate (t))) = φ ((S) ((η) (rightCoordinate (t)))) := by
  let he := completeIdentityFirstSourcePole_incomingCubic K n h U φ hf w hw
  let v := completePointCubicComparisonTargetComplement K n h 1 0 (p)
    (φ.comp (Q)) (φ.comp (S)) he
  have hv := completePointCubicComparisonTargetComplement_inclusion K n h 1 0 (p)
    (φ.comp (Q)) (φ.comp (S)) he
  have hp := completePointCubicComparison_poles K n h 1 0 (p)
    (φ.comp (Q)) (φ.comp (S)) he
  exact completePointFirstIncomingComplementPoles_eq_of_source_mem K n h 0
    (φ.comp (Q)) v hv (φ.comp (S))
    (fun c ↦ congrArg φ (completeIdentityFirstSourcePoleTargetFunctions_coefficients K n h U c))
    hp.1.symm hp.2.symm hy

/-- Both unchanged ambient errors vanish on these full local graph tests. -/
theorem completeIdentityFirstSourcePole_errors_zero_of_source_mem
    (hx : φ (completeIdentityFirstSourcePoleFunctions K n h U
      (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
        (leftCoordinate (parameter K 1)))) ∈ IsLocalRing.maximalIdeal B)
    (hy : φ (completeIdentityFirstSourcePoleFunctions K n h U
      (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
        (rightCoordinate (parameter K 1)))) ∈ IsLocalRing.maximalIdeal B) :
    φ (algebraMap _ _ ((completeIdentityFirstAmbientRestriction K n h (V))
      (completeIdentityFirstAmbientError K n h (leftCoordinate (t))))) = 0 ∧
    φ (algebraMap _ _ ((completeIdentityFirstAmbientRestriction K n h (V))
      (completeIdentityFirstAmbientError K n h (rightCoordinate (t))))) = 0 := by
  constructor
  · rw [← completeIdentityFirstSourcePoleTargetFunctions_error, map_sub,
      completeIdentityFirstSourcePole_outgoing_eq_of_source_mem K n h U φ hf hx, sub_self]
  · rw [← completeIdentityFirstSourcePoleTargetFunctions_error, map_sub,
      completeIdentityFirstSourcePole_incoming_eq_of_source_mem K n h U φ hf w hw hy, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages
