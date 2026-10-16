/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFlatTransfer
public import FLT.Mazur.PolygonCompleteIdentityFiniteLawCriterion

/-!
# The unchanged original first positive-order multiplication law

Original-base flatness of the full finite graph forces every original node
defect to descend. The existing boundary rigidity theorem then identifies
the actual multiplication with Laurent multiplication. Rotation and full
edge detection extend this equality over the entire first-stage polygon.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "C" => firstNodeBranchSubalgebra K[T;T⁻¹]

/-- Every unchanged original defect descends to the full first-stage source node algebra. -/
theorem completeIdentityFirstActionNodeDefect_mem_source (z : ChartRing (e)) :
    completeIdentityFirstActionNodeDefect K n h 0 z ∈ (C) :=
  completeIdentityFirstGraphOriginalFlat_defect K n h 0
    (completeIdentityFirstGraphOriginalScalars_flat K n h) z

/-- The actual first-order action preserves all original node functions. -/
theorem completeIdentityFirstActionBranch_preserves_source
    (p : (S)[T;T⁻¹] × (S)[T;T⁻¹]) (hp : p ∈ (C)) :
    completeIdentityFirstActionBranchEquiv K n h 0 p ∈ (C) :=
  completeIdentityFirstGraphOriginalFlat_preserves K n h 0
    (completeIdentityFirstGraphOriginalScalars_flat K n h) p hp

/-- Original identity multiplication is Laurent multiplication at the first positive order. -/
theorem completeIdentityFiniteLaw_firstPositive :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h 0 1 =
      completeIdentityFiniteOriginalMul K n h 0 1 :=
  completeIdentityFiniteLaw_one_of_graphOriginalFlat K n h 0
    (completeIdentityFirstGraphOriginalScalars_flat K n h)

/-- The first positive-order comparison holds on the entire polygon, including all nodes. -/
theorem completeIdentityFiniteComparison_firstPositive :
    completeIdentityFiniteScaling K n h 1 ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityFiniteInput K n h 0 1 ≫ completeIdentityActionTarget K n h 0 :=
  (completeIdentityFiniteComparison_iff_laurentLaw K n h 1).mpr
    (completeIdentityFiniteLaw_firstPositive K n h)

end FLT.Mazur.PolygonInfinitesimalStages
