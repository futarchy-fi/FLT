/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentStageParameterTorus
public import FLT.Mazur.PolygonCompleteIdentityGraphChartEdgeCartesian
public import FLT.Mazur.PolygonCompleteIdentityGraphIncomingCartesian
public import FLT.Mazur.PolygonCompleteIdentityTopChartBranchImage

/-!
# Both full source punctures of the original higher graph chart

The two maps defining the finite graph image are the entire original
source punctures of the literal adic chart, with their full structure.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonScalingNaturality LaurentStageParameter PolygonPinching
open LaurentUnitPoints
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "q" => Spec.map (CommRingCat.ofHom (coeffMap (parameterEval K (m + 1))))
local notation "s" => completeIdentityActionGraphAdicChartSource K n h (m + 1) 0 0
local notation "o" => stageNodeParameterIso K (m + 1)
local notation "l" => completeIdentityTopLeftToGraphChart K n h m
local notation "r" => completeIdentityTopRightToGraphChart K n h m
local notation "b" => ZMod.finEquiv n (finRotate n (0 : Fin n))

/-- The original retained-parameter outgoing map is an open immersion. -/
instance completeIdentityTopLeftToGraphChart_open : IsOpenImmersion (l) := by
  unfold completeIdentityTopLeftToGraphChart
  infer_instance

/-- The actual incoming map is an open immersion, including its reciprocal parameter. -/
instance completeIdentityTopRightToGraphChart_open : IsOpenImmersion (r) := by
  unfold completeIdentityTopRightToGraphChart
  infer_instance

/-- The full outgoing square retains the original source node, not just its point set. -/
theorem completeIdentityTopLeftToGraphChart_isPullback :
    IsPullback (l) (𝟙 _) (s) (leftBranchOpen (S) (e) ≫ (o).hom) := by
  have H := (IsPullback.of_id_snd (f := (q))).paste_horiz
    (completeIdentityFiniteEdgeToGraphChart_isPullback K n h (m + 1))
  have he : (q) ≫ leftBranchOpen (Ring K (m + 1))[T;T⁻¹]
      (LaurentPolynomial.C (parameter K (m + 1))) = leftBranchOpen (S) (e) ≫ (o).hom := by
    rw [stageNodeParameterIso_hom]
    exact (leftBranchOpen_ringMap (parameterEval K (m + 1)) _ _
      (parameterEval_parameter K (m + 1))).symm
  simpa only [branchTorus, completeIdentityTopLeftToGraphChart, he] using H

/-- The full incoming square retains exactly the original opposite source puncture. -/
theorem completeIdentityTopRightToGraphChart_isPullback :
    IsPullback (r) (𝟙 _) (s) (rightBranchOpen (S) (e) ≫ (o).hom) := by
  have H := (IsPullback.of_id_snd (f := (edgeInversion (S)).hom ≫ (q))).paste_horiz
    (completeIdentityIncomingToGraphChartAt_isPullback K n h (m + 1) (b) 0
      (completeIdentityIncomingIndex_zero n))
  have he : ((edgeInversion (S)).hom ≫ (q)) ≫
      precedingBranch (Ring K (m + 1))[T;T⁻¹] (LaurentPolynomial.C (parameter K (m + 1))) =
      rightBranchOpen (S) (e) ≫ (o).hom := by
    rw [Category.assoc, ← precedingBranch_ringMap (parameterEval K (m + 1)) _ _
      (parameterEval_parameter K (m + 1)), edgeInversion_preceding_assoc, stageNodeParameterIso_hom]
    rfl
  simp only [Category.assoc] at he
  simpa only [branchTorus, completeIdentityTopRightToGraphChart, Category.assoc, he] using H

end FLT.Mazur.PolygonInfinitesimalStages
