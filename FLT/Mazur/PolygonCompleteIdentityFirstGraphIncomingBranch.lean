/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentReciprocalSubstitution
public import FLT.Mazur.PolygonCompleteIdentityGraphIncomingChart
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphOriginalNodes
public import FLT.Mazur.PolygonCompleteIdentityFirstBranchOriginal

/-!
# Exact incoming comparison of the finite and literal cubic graphs

The adjacent component's original action gives the right branch of the
actual diagonal node-pair chart. Compare both full node coordinates with
the finite graph, retaining the original coefficients and nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentFirstStageParameter
open LaurentUnitPoints PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "S" => Ring K[T;T⁻¹] 1
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K)))
local notation "r" => completeIdentityFirstGraphRightBranch K n h (0 : Fin n)
local notation "b" => ZMod.finEquiv n (finRotate n (0 : Fin n))
local notation "U" => completeIdentityFirstActionUnit K n h (0 : Fin n)

/-- The actual adjacent edge enters the original zero node chart. -/
theorem completeIdentityIncomingIndex_zero :
    (finRotate n).symm (rotateIndex (b) 0) = 0 := by
  simp [rotateIndex]

/-- The adjacent component supplies the full incoming branch of the literal zero-node graph. -/
def completeIdentityFirstRightToGraphChart :
    branchTorus (S) ⟶ completeIdentityActionGraphAdicChart K n h 1 0 0 :=
  (edgeInversion (S)).hom ≫ (q) ≫
    completeIdentityIncomingToGraphChartAt K n h 1 (b) 0
      (completeIdentityIncomingIndex_zero n)

/-- Its original source coordinate is the full original right puncture. -/
@[reassoc] theorem completeIdentityFirstRightToGraphChart_source :
    completeIdentityFirstRightToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartSource K n h 1 0 0 =
      (r) ≫ completeIdentityFirstGraphSchemeSource K n h 0 ≫ (firstNodeParameterIso K).hom := by
  rw [completeIdentityFirstRightToGraphChart, Category.assoc, Category.assoc,
    completeIdentityIncomingToGraphChartAt_source,
    ← precedingBranch_ringMap (parameterEval K) (C (t)) (e) (parameterEval_parameter K),
    edgeInversion_preceding_assoc, completeIdentityFirstGraphRightBranch_source_assoc,
    ← rightBranchOpen_eq_spec, firstNodeParameterIso_hom]
  rfl

/-- The entire target is original reciprocal multiplication on the original target node. -/
@[reassoc] theorem completeIdentityFirstRightToGraphChart_target :
    completeIdentityFirstRightToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartTarget K n h 1 0 0 =
      (r) ≫ completeIdentityFirstGraphSchemeTarget K n h 0 ≫
        Spec.map (CommRingCat.ofHom
          (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _))) := by
  rw [completeIdentityFirstRightToGraphChart, Category.assoc, Category.assoc,
    completeIdentityIncomingToGraphChartAt_target,
    ← completeIdentityFirstActionUnit_originalCoordinates_assoc,
    ← precedingBranch_ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _),
    spec_evalUnit_incoming_assoc, completeIdentityFirstGraphRightBranch_target_assoc,
    ← rightBranchOpen_eq_spec]
  rfl

/-- The full source polygon comparison retains its original node inclusion. -/
@[reassoc] theorem completeIdentityFirstRightToGraphChart_source_polygon :
    completeIdentityFirstRightToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartSource K n h 1 0 0 ≫
          PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h 0 =
      (r) ≫ completeIdentityFirstGraphOriginalSource K n h 0 := by
  rw [completeIdentityFirstRightToGraphChart_source_assoc]
  rfl

/-- The full target polygon comparison retains its original coefficient map and inclusion. -/
@[reassoc] theorem completeIdentityFirstRightToGraphChart_target_polygon :
    completeIdentityFirstRightToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartTarget K n h 1 0 0 ≫
          PolygonInfinitesimal.chart (A) (t) n h 0 =
      (r) ≫ completeIdentityFirstGraphOriginalTarget K n h 0 := by
  rw [completeIdentityFirstRightToGraphChart_target_assoc]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
