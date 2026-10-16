/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphClosedComparison

/-!
# The actual two-branch schematic image inside the original adic chart

The original outgoing and incoming branches have a dense/closed
factorization through the higher graph. Thus their full schematic image in
the literal adic chart is this higher graph, without reducing either ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "L" => (S)[T;T⁻¹]
local notation "f" => completeIdentityTopGraphToChart K n h m
local notation "j" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
local notation "l" => completeIdentityTopLeftToGraphChart K n h m
local notation "r" => completeIdentityTopRightToGraphChart K n h m
local notation "U" => completeIdentityTopActionUnit K n h 0 m
local notation "V" => completeIdentityTopActionReciprocalUnit K n h 0 m
local notation "b" => topNodeGraphBranches K[T;T⁻¹] m (U) (V)

/-- The left comparison is the original branch morphism into the literal chart. -/
@[reassoc] theorem completeIdentityTopGraphToChart_left :
    completeIdentityTopGraphLeftBranch K n h 0 m ≫ (f) = (l) := by
  apply (cancel_mono (j)).mp
  rw [Category.assoc, completeIdentityTopGraphToChart_embedding]
  exact (completeIdentityTopGraphToChartSpace_left K n h m).symm

/-- The right comparison is the actual adjacent-component incoming branch. -/
@[reassoc] theorem completeIdentityTopGraphToChart_right :
    completeIdentityTopGraphRightBranch K n h 0 m ≫ (f) = (r) := by
  apply (cancel_mono (j)).mp
  rw [Category.assoc, completeIdentityTopGraphToChart_embedding]
  exact (completeIdentityTopGraphToChartSpace_right K n h m).symm

/-- Both original branches, jointly considered as a map into the actual adic chart. -/
def completeIdentityTopChartBothBranches :
    Spec (.of ((L) × (L))) ⟶ completeIdentityActionGraphAdicChart K n h (m + 1) 0 0 :=
  inv (coprodSpec (L) (L)) ≫ coprod.desc (l) (r)

/-- Their dense/closed factorization retains the entire original comparison. -/
theorem completeIdentityTopChartBothBranches_factorization :
    completeIdentityTopChartBothBranches K n h m = (b) ≫ (f) := by
  apply (cancel_epi (coprodSpec (L) (L))).mp
  rw [completeIdentityTopChartBothBranches, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, coprodSpec_inl_assoc,
      topNodeGraphBranches_left_assoc]
    exact (completeIdentityTopGraphToChart_left K n h m).symm
  · simp only [coprod.inr_desc, coprodSpec_inr_assoc,
      topNodeGraphBranches_right_assoc]
    exact (completeIdentityTopGraphToChart_right K n h m).symm

/-- The full branch-image ideal in the actual chart is the finite comparison's full kernel. -/
theorem completeIdentityTopChartBothBranches_ker :
    (completeIdentityTopChartBothBranches K n h m).ker = (f).ker := by
  rw [completeIdentityTopChartBothBranches_factorization, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

end FLT.Mazur.PolygonInfinitesimalStages
