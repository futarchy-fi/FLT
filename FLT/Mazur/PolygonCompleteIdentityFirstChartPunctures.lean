/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstStageParameterTorus
public import FLT.Mazur.PolygonCompleteIdentityGraphChartEdgeCartesian
public import FLT.Mazur.PolygonCompleteIdentityGraphIncomingCartesian
public import FLT.Mazur.PolygonCompleteIdentityFirstChartBranchImage

/-!
# Both full source punctures of the original first graph chart

The two maps defining the finite graph image are the entire original
source punctures of the literal adic chart, with their full structure.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonScalingNaturality LaurentFirstStageParameter PolygonPinching
open LaurentUnitPoints
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K)))
local notation "s" => completeIdentityActionGraphAdicChartSource K n h 1 0 0
local notation "o" => firstNodeParameterIso K
local notation "l" => completeIdentityFirstLeftToGraphChart K n h
local notation "r" => completeIdentityFirstRightToGraphChart K n h
local notation "b" => ZMod.finEquiv n (finRotate n (0 : Fin n))

/-- The original retained-parameter outgoing map is an open immersion. -/
instance completeIdentityFirstLeftToGraphChart_open : IsOpenImmersion (l) := by
  unfold completeIdentityFirstLeftToGraphChart
  infer_instance

/-- The actual incoming map is an open immersion, including its reciprocal parameter. -/
instance completeIdentityFirstRightToGraphChart_open : IsOpenImmersion (r) := by
  unfold completeIdentityFirstRightToGraphChart
  infer_instance

/-- The full outgoing square retains the original source node, not just its point set. -/
theorem completeIdentityFirstLeftToGraphChart_isPullback :
    IsPullback (l) (𝟙 _) (s) (leftBranchOpen (S) (e) ≫ (o).hom) := by
  have H := (IsPullback.of_id_snd (f := (q))).paste_horiz
    (completeIdentityFiniteEdgeToGraphChart_isPullback K n h 1)
  have he : (q) ≫ leftBranchOpen (Ring K 1)[T;T⁻¹]
      (LaurentPolynomial.C (parameter K 1)) = leftBranchOpen (S) (e) ≫ (o).hom := by
    rw [firstNodeParameterIso_hom]
    exact (leftBranchOpen_ringMap (parameterEval K) _ _
      (parameterEval_parameter K)).symm
  simpa only [branchTorus, completeIdentityFirstLeftToGraphChart, he] using H

/-- The full incoming square retains exactly the original opposite source puncture. -/
theorem completeIdentityFirstRightToGraphChart_isPullback :
    IsPullback (r) (𝟙 _) (s) (rightBranchOpen (S) (e) ≫ (o).hom) := by
  have H := (IsPullback.of_id_snd (f := (edgeInversion (S)).hom ≫ (q))).paste_horiz
    (completeIdentityIncomingToGraphChartAt_isPullback K n h 1 (b) 0
      (completeIdentityIncomingIndex_zero n))
  have he : ((edgeInversion (S)).hom ≫ (q)) ≫
      precedingBranch (Ring K 1)[T;T⁻¹] (LaurentPolynomial.C (parameter K 1)) =
      rightBranchOpen (S) (e) ≫ (o).hom := by
    rw [Category.assoc, ← precedingBranch_ringMap (parameterEval K) _ _
      (parameterEval_parameter K), edgeInversion_preceding_assoc, firstNodeParameterIso_hom]
    rfl
  simp only [Category.assoc] at he
  simpa only [branchTorus, completeIdentityFirstRightToGraphChart, Category.assoc, he] using H

end FLT.Mazur.PolygonInfinitesimalStages
