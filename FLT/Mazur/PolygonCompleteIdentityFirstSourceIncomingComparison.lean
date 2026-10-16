/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphRotatedCubic
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceTargetFunctions
public import FLT.Mazur.PolygonCompletePointCubicComplementComparison
public import FLT.Mazur.PolygonCompletePointFirstIncomingNodeExtraction

/-!
# Incoming cubic comparison on actual original graph tests

The source-only patch is tested through the unchanged full graph. Rotating
both chart labels to the predecessor of zero supplies the incoming contraction
comparison while retaining the original source and target coordinate maps.
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

include hf hw

/-- The rotated complete-graph equation supplies the actual incoming cubic comparison. -/
theorem completeIdentityFirstSourcePole_incomingCubic :
    Spec.map (CommRingCat.ofHom (φ.comp (S))) ≫ (d) ≫ integralCurveChart (E) 2 =
      Spec.map (CommRingCat.ofHom (φ.comp (Q))) ≫ (a) ≫ (r) ≫ (g) := by
  have hs : w ≫ completeIdentityActionGraphAdicChartSource K n h 1 0 0 =
      Spec.map (CommRingCat.ofHom (φ.comp (F))) := by
    rw [completeIdentityActionGraphAdicChartSource, ← Category.assoc, hw]
    simp only [Category.assoc, ← completeIdentityFirstSourcePoleInputFunctions_map,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have ht : (φ.comp (F)) (algebraMap (Ring K 1)[T;T⁻¹]
      (ChartRing (LaurentPolynomial.C (t))) (LaurentPolynomial.C (t))) = 0 := by
    rw [RingHom.comp_apply, completeIdentityFirstSourcePoleInputFunctions_parameter]
    exact hf
  have he := completeIdentityFirstGraph_rotatedCubic K n h 0 0 (b) w (φ.comp (F)) hs ht
  have hi : rotateIndex (b) (0 : Fin n) = (p) := by
    simp only [rotateIndex, map_zero, zero_add, RingEquiv.symm_apply_apply]
  have hd : w ≫ completeIdentityActionGraphAdicChartTarget K n h 1 0 0 =
      Spec.map (CommRingCat.ofHom (φ.comp (Q))) := by
    rw [completeIdentityActionGraphAdicChartTarget, ← Category.assoc, hw]
    simp only [Category.assoc, ← completeIdentityFirstSourcePoleTargetFunctions_map,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hi, ← Category.assoc w, hd] at he
  rw [completePointNodeToCubicChart_inclusion]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rw [he]
  congr 1
  apply congrArg (fun f : ChartRing (t) →+* B ↦ Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro z
  change φ ((S) (algebraMap (ChartRing (t)) (StageNodeLocalization K 1) z)) =
    φ ((F) (universalReciprocalScale (t) z))
  rw [completeIdentityFirstSourcePoleFunctions_algebraMap]
  congr 1
  change _ = (algebraMap _ _) ((completeIdentityFirstAmbientRestriction K n h (V))
    ((completeIdentityFirstAmbientSourceFunctions K n h)
      ((firstNodeParameterMap K) (universalReciprocalScale (t) z))))
  have hh := DFunLike.congr_fun (firstNodeParameterMap_universalScaling K) z
  simp only [RingHom.comp_apply] at hh
  rw [hh]
  rfl

local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
variable (hz : φ (completeIdentityFirstSourcePoleFunctions K n h U
  (algebraMap (ChartRing (parameter K 1)) (StageNodeLocalization K 1)
    (rightCoordinate (parameter K 1)))) = 0)

include hz

/-- Actual full-graph tests kill the incoming target when the incoming source is zero. -/
theorem completeIdentityFirstSourcePole_incoming_zero : φ ((Q) (rightCoordinate (t))) = 0 := by
  let he := completeIdentityFirstSourcePole_incomingCubic K n h U φ hf w hw
  let v := completePointCubicComparisonTargetComplement K n h 1 0 (p)
    (φ.comp (Q)) (φ.comp (S)) he
  have hv := completePointCubicComparisonTargetComplement_inclusion K n h 1 0 (p)
    (φ.comp (Q)) (φ.comp (S)) he
  have hp := completePointCubicComparison_poles K n h 1 0 (p)
    (φ.comp (Q)) (φ.comp (S)) he
  apply completePointFirstIncomingComplementPoles_target_zero K n h 0
    (φ.comp (Q)) v hv (φ.comp (S)) _ hp.1.symm hp.2.symm hz
  intro c
  exact congrArg φ (completeIdentityFirstSourcePoleTargetFunctions_coefficients K n h U c)

/-- The corresponding unchanged ambient incoming error also vanishes on these graph tests. -/
theorem completeIdentityFirstSourcePole_incoming_error_zero :
    φ (algebraMap _ _ ((completeIdentityFirstAmbientRestriction K n h (V))
      (completeIdentityFirstAmbientError K n h (rightCoordinate (t))))) = 0 := by
  rw [← completeIdentityFirstSourcePoleTargetFunctions_error, map_sub,
    completeIdentityFirstSourcePole_incoming_zero K n h U φ hf w hw hz, hz, sub_zero]

end FLT.Mazur.PolygonInfinitesimalStages
