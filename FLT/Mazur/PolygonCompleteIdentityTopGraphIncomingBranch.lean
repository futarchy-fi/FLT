/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphIncomingBranch
public import FLT.Mazur.PolygonCompleteIdentityGraphIncomingChart
public import FLT.Mazur.PolygonCompleteIdentityTopGraphOriginalNodes
public import FLT.Mazur.PolygonCompleteIdentityTopBranchOriginal

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
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentStageParameter
open LaurentUnitPoints PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K (m + 1))))
local notation "r" => completeIdentityTopGraphRightBranch K n h (0 : Fin n) m
local notation "b" => ZMod.finEquiv n (finRotate n (0 : Fin n))
local notation "U" => completeIdentityTopActionUnit K n h (0 : Fin n) m

/-- The adjacent component supplies the full incoming branch of the literal zero-node graph. -/
def completeIdentityTopRightToGraphChart :
    branchTorus (S) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0 :=
  (edgeInversion (S)).hom ≫ (q) ≫
    completeIdentityIncomingToGraphChartAt K n h (m + 1) (b) 0
      (completeIdentityIncomingIndex_zero n)

/-- Its original source coordinate is the full original right puncture. -/
@[reassoc] theorem completeIdentityTopRightToGraphChart_source :
    completeIdentityTopRightToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 =
      (r) ≫ completeIdentityTopGraphSchemeSource K n h 0 m ≫
        (stageNodeParameterIso K (m + 1)).hom := by
  rw [completeIdentityTopRightToGraphChart, Category.assoc, Category.assoc,
    completeIdentityIncomingToGraphChartAt_source,
    ← precedingBranch_ringMap (parameterEval K (m + 1)) (C (t)) (e)
      (parameterEval_parameter K (m + 1)),
    edgeInversion_preceding_assoc, completeIdentityTopGraphRightBranch_source_assoc,
    ← rightBranchOpen_eq_spec, stageNodeParameterIso_hom]
  rfl

/-- The entire target is original reciprocal multiplication on the original target node. -/
@[reassoc] theorem completeIdentityTopRightToGraphChart_target :
    completeIdentityTopRightToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 =
      (r) ≫ completeIdentityTopGraphSchemeTarget K n h 0 m ≫
        Spec.map (CommRingCat.ofHom
          (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _))) := by
  rw [completeIdentityTopRightToGraphChart, Category.assoc, Category.assoc,
    completeIdentityIncomingToGraphChartAt_target,
    ← completeIdentityTopActionUnit_originalCoordinates_assoc,
    ← precedingBranch_ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _),
    spec_evalUnit_incoming_assoc, completeIdentityTopGraphRightBranch_target_assoc,
    ← rightBranchOpen_eq_spec]
  rfl

/-- The full source polygon comparison retains its original node inclusion. -/
@[reassoc] theorem completeIdentityTopRightToGraphChart_source_polygon :
    completeIdentityTopRightToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 ≫
          PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h 0 =
      (r) ≫ completeIdentityTopGraphOriginalSource K n h 0 m := by
  rw [completeIdentityTopRightToGraphChart_source_assoc]
  rfl

/-- The full target polygon comparison retains its original coefficient map and inclusion. -/
@[reassoc] theorem completeIdentityTopRightToGraphChart_target_polygon :
    completeIdentityTopRightToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 ≫
          PolygonInfinitesimal.chart (A) (t) n h 0 =
      (r) ≫ completeIdentityTopGraphOriginalTarget K n h 0 m := by
  rw [completeIdentityTopRightToGraphChart_target_assoc]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
