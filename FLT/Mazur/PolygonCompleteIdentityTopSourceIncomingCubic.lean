/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityStageGraphRotatedCubic
public import FLT.Mazur.PolygonCompleteIdentityTopSourceTargetFunctions
public import FLT.Mazur.PolygonCompletePointCubicComplementComparison

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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "t" => parameter K (m + 1)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "F" => completeIdentityTopSourcePoleInputFunctions K n h m U
local notation "Q" => completeIdentityTopSourcePoleTargetFunctions K n h m U
local notation "p" => Equiv.symm (finRotate n) (0 : Fin n)
local notation "b" => ZMod.finEquiv n (p)
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h (m + 1) 0 (p)
local notation "a" => PolygonInfinitesimal.chart (Ring K (m + 1)) (t) n h (p)
local notation "r" => originalStageToCompatibleProj K n h (m + 1)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityTopSourcePolePatch K n h m U →+* B)
variable (hf : φ (completeIdentityTopSourcePoleParameter K n h m U) = 0)
variable (w : Spec (.of B) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0)
variable (hw : w ≫ completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0 =
  Spec.map (CommRingCat.ofHom φ) ≫ completeIdentityTopSourcePolePatchMap K n h m U ≫
    Scheme.Opens.ι ((completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U).1))

include hf hw

/-- The rotated complete-graph equation supplies the actual incoming cubic comparison. -/
theorem completeIdentityTopSourcePole_incomingCubic :
    Spec.map (CommRingCat.ofHom (φ.comp (S))) ≫ (d) ≫ integralCurveChart (E) 2 =
      Spec.map (CommRingCat.ofHom (φ.comp (Q))) ≫ (a) ≫ (r) ≫ (g) := by
  have hs : w ≫ completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 =
      Spec.map (CommRingCat.ofHom (φ.comp (F))) := by
    rw [completeIdentityActionGraphAdicChartSource, ← Category.assoc, hw]
    simp only [Category.assoc, ← completeIdentityTopSourcePoleInputFunctions_map,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have ht : (φ.comp (F)) (algebraMap (Ring K (m + 1))[T;T⁻¹]
      (ChartRing (LaurentPolynomial.C (t))) (LaurentPolynomial.C (t))) = 0 := by
    rw [RingHom.comp_apply, completeIdentityTopSourcePoleInputFunctions_parameter]
    exact hf
  have he := completeIdentityStageGraph_rotatedCubic K n h (m + 1) 0 0 (b) w (φ.comp (F)) hs ht
  have hi : rotateIndex (b) (0 : Fin n) = (p) := by
    simp only [rotateIndex, map_zero, zero_add, RingEquiv.symm_apply_apply]
  have hd : w ≫ completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 =
      Spec.map (CommRingCat.ofHom (φ.comp (Q))) := by
    rw [completeIdentityActionGraphAdicChartTarget, ← Category.assoc, hw]
    simp only [Category.assoc, ← completeIdentityTopSourcePoleTargetFunctions_map,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hi, ← Category.assoc w, hd] at he
  rw [completePointNodeToCubicChart_inclusion]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rw [he]
  congr 1
  apply congrArg (fun f : ChartRing (t) →+* B ↦ Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro z
  change φ ((S) (algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1)) z)) =
    φ ((F) (universalReciprocalScale (t) z))
  rw [completeIdentityTopSourcePoleFunctions_algebraMap]
  congr 1
  change _ = (algebraMap _ _) ((completeIdentityTopAmbientRestriction K n h m (V))
    ((completeIdentityTopAmbientSourceFunctions K n h m)
      ((stageNodeParameterMap K (m + 1)) (universalReciprocalScale (t) z))))
  have hh := DFunLike.congr_fun (stageNodeParameterMap_universalScaling K (m + 1)) z
  simp only [RingHom.comp_apply] at hh
  rw [hh]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
