/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphClosedComparison

/-!
# The actual two-branch schematic image inside the original adic chart

The original outgoing and incoming branches have a dense/closed
factorization through the finite graph. Thus their full schematic image in
the literal adic chart is this finite graph, without reducing either ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "L" => (S)[T;T⁻¹]
local notation "f" => completeIdentityFirstGraphToChart K n h
local notation "j" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "l" => completeIdentityFirstLeftToGraphChart K n h
local notation "r" => completeIdentityFirstRightToGraphChart K n h
local notation "b" => completeIdentityFirstGraphBothBranches K n h (0 : Fin n)

/-- The left comparison is the original branch morphism into the literal chart. -/
@[reassoc] theorem completeIdentityFirstGraphToChart_left :
    completeIdentityFirstGraphLeftBranch K n h 0 ≫ (f) = (l) := by
  apply (cancel_mono (j)).mp
  rw [Category.assoc, completeIdentityFirstGraphToChart_embedding]
  exact (completeIdentityFirstGraphToChartSpace_left K n h).symm

/-- The right comparison is the actual adjacent-component incoming branch. -/
@[reassoc] theorem completeIdentityFirstGraphToChart_right :
    completeIdentityFirstGraphRightBranch K n h 0 ≫ (f) = (r) := by
  apply (cancel_mono (j)).mp
  rw [Category.assoc, completeIdentityFirstGraphToChart_embedding]
  exact (completeIdentityFirstGraphToChartSpace_right K n h).symm

/-- Both original branches, jointly considered as a map into the actual adic chart. -/
def completeIdentityFirstChartBothBranches :
    Spec (.of ((L) × (L))) ⟶ completeIdentityActionGraphAdicChart K n h 1 0 0 :=
  inv (coprodSpec (L) (L)) ≫ coprod.desc (l) (r)

/-- Their dense/closed factorization retains the entire original comparison. -/
theorem completeIdentityFirstChartBothBranches_factorization :
    completeIdentityFirstChartBothBranches K n h = (b) ≫ (f) := by
  apply (cancel_epi (coprodSpec (L) (L))).mp
  rw [completeIdentityFirstChartBothBranches, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, coprodSpec_inl_assoc,
      completeIdentityFirstGraphBothBranches_left_assoc,
      completeIdentityFirstGraphToChart_left]
  · simp only [coprod.inr_desc, coprodSpec_inr_assoc,
      completeIdentityFirstGraphBothBranches_right_assoc,
      completeIdentityFirstGraphToChart_right]

/-- The full branch-image ideal in the actual chart is the finite comparison's full kernel. -/
theorem completeIdentityFirstChartBothBranches_ker :
    (completeIdentityFirstChartBothBranches K n h).ker = (f).ker := by
  rw [completeIdentityFirstChartBothBranches_factorization, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

end FLT.Mazur.PolygonInfinitesimalStages
