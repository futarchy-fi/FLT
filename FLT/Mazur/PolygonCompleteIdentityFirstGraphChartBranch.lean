/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChartEdge
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphOriginalNodes

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
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentFirstStageParameter
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
local notation "l" => completeIdentityFirstGraphLeftBranch K n h (0 : Fin n)

/-- The original retained-parameter left branch lies in the actual flat cubic-graph chart. -/
def completeIdentityFirstLeftToGraphChart :
    branchTorus (S) ⟶ completeIdentityActionGraphAdicChart K n h 1 0 0 :=
  (q) ≫ completeIdentityFiniteEdgeToGraphChart K n h 1

/-- The actual chart and finite graph have the same entire original source node coordinate. -/
@[reassoc] theorem completeIdentityFirstLeftToGraphChart_source :
    completeIdentityFirstLeftToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartSource K n h 1 0 0 =
      (l) ≫ completeIdentityFirstGraphSchemeSource K n h 0 ≫ (firstNodeParameterIso K).hom := by
  rw [completeIdentityFirstLeftToGraphChart, Category.assoc,
    completeIdentityFiniteEdgeToGraphChart_source,
    completeIdentityFirstGraphLeftBranch_source_assoc, firstNodeParameterIso_hom]
  exact (leftBranchOpen_ringMap (parameterEval K) (C (t)) (e)
    (parameterEval_parameter K)).symm

/-- The target node coordinate also agrees, including the original truncated coefficient map. -/
@[reassoc] theorem completeIdentityFirstLeftToGraphChart_target :
    completeIdentityFirstLeftToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartTarget K n h 1 0 0 =
      (l) ≫ completeIdentityFirstGraphSchemeTarget K n h 0 ≫
        Spec.map (CommRingCat.ofHom
          (ringMap (c) (t) (e) (stageCoefficientMap_parameter _ _))) := by
  rw [completeIdentityFirstLeftToGraphChart, Category.assoc,
    completeIdentityFiniteEdgeToGraphChart_target,
    completeIdentityFirstGraphLeftBranch_target_assoc, leftBranchOpen_ringMap,
    completeIdentityFirstActionUnit_originalCoordinates_assoc]

/-- The original full source polygon agrees after the exact node-ring identification. -/
@[reassoc] theorem completeIdentityFirstLeftToGraphChart_source_polygon :
    completeIdentityFirstLeftToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartSource K n h 1 0 0 ≫
          PolygonInfinitesimal.chart (A)[T;T⁻¹] (C (t)) n h 0 =
      (l) ≫ completeIdentityFirstGraphOriginalSource K n h 0 := by
  rw [completeIdentityFirstLeftToGraphChart_source_assoc]
  rfl

/-- The target is likewise the original full stage target of the finite graph. -/
@[reassoc] theorem completeIdentityFirstLeftToGraphChart_target_polygon :
    completeIdentityFirstLeftToGraphChart K n h ≫
        completeIdentityActionGraphAdicChartTarget K n h 1 0 0 ≫
          PolygonInfinitesimal.chart (A) (t) n h 0 =
      (l) ≫ completeIdentityFirstGraphOriginalTarget K n h 0 := by
  rw [completeIdentityFirstLeftToGraphChart_target_assoc]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
