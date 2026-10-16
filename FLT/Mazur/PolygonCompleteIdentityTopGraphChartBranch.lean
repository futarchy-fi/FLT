/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChartEdge
public import FLT.Mazur.PolygonCompleteIdentityTopGraphOriginalNodes

/-!
# Exact left-branch comparison of the finite and literal cubic graphs

The same original left punctured branch maps to both graph constructions.
Its two node coordinates agree with their complete original coefficient
maps. This supplies a branch comparison, not an identification of whole
charts or a transfer of flatness to the finite branch-image graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentStageParameter
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
local notation "l" => completeIdentityTopGraphLeftBranch K n h (0 : Fin n) m

/-- The original retained-parameter left branch lies in the actual flat cubic-graph chart. -/
def completeIdentityTopLeftToGraphChart :
    branchTorus (S) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0 :=
  (q) ≫ completeIdentityFiniteEdgeToGraphChart K n h (m + 1)

/-- The actual chart and finite graph have the same entire original source node coordinate. -/
@[reassoc] theorem completeIdentityTopLeftToGraphChart_source :
    completeIdentityTopLeftToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 =
      (l) ≫ completeIdentityTopGraphSchemeSource K n h 0 m ≫
        (stageNodeParameterIso K (m + 1)).hom := by
  rw [completeIdentityTopLeftToGraphChart, Category.assoc,
    completeIdentityFiniteEdgeToGraphChart_source,
    completeIdentityTopGraphLeftBranch_source_assoc, stageNodeParameterIso_hom]
  exact (leftBranchOpen_ringMap (parameterEval K (m + 1)) (C (t)) (e)
    (parameterEval_parameter K (m + 1))).symm

/-- The target node coordinate also agrees, including the original truncated coefficient map. -/
@[reassoc] theorem completeIdentityTopLeftToGraphChart_target :
    completeIdentityTopLeftToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 =
      (l) ≫ completeIdentityTopGraphSchemeTarget K n h 0 m ≫
        Spec.map (CommRingCat.ofHom
          (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _))) := by
  rw [completeIdentityTopLeftToGraphChart, Category.assoc,
    completeIdentityFiniteEdgeToGraphChart_target,
    completeIdentityTopGraphLeftBranch_target_assoc, leftBranchOpen_ringMap,
    completeIdentityTopActionUnit_originalCoordinates_assoc]

/-- The original full source polygon agrees after the exact node-ring identification. -/
@[reassoc] theorem completeIdentityTopLeftToGraphChart_source_polygon :
    completeIdentityTopLeftToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0 ≫
          PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h 0 =
      (l) ≫ completeIdentityTopGraphOriginalSource K n h 0 m := by
  rw [completeIdentityTopLeftToGraphChart_source_assoc]
  rfl

/-- The target is likewise the original full stage target of the finite graph. -/
@[reassoc] theorem completeIdentityTopLeftToGraphChart_target_polygon :
    completeIdentityTopLeftToGraphChart K n h m ≫
        completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 ≫
          PolygonInfinitesimal.chart (A) (t) n h 0 =
      (l) ≫ completeIdentityTopGraphOriginalTarget K n h 0 m := by
  rw [completeIdentityTopLeftToGraphChart_target_assoc]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
