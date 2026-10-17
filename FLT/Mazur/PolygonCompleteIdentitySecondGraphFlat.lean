/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartSocleVanishing
public import FLT.Mazur.PolygonCompleteIdentitySecondResidualSocle

/-!
# The actual second graph is flat over its original base

The proved first positive law discharges the preceding-defect hypothesis.
This identifies the entire original second graph chart and constructs its
node action without assuming the second canonical correction vanishes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The full actual second-stage node comparison has zero kernel. -/
theorem completeIdentitySecondChartNodeKernel_eq_bot :
    completeIdentityTopChartNodeKernel K n h 1 = ⊥ :=
  completeIdentityTopChartNodeKernel_eq_bot K n h 1
    (completeIdentitySecondPrecedingDefect K n h)

/-- The whole original second graph chart is identified, including its nilpotents. -/
theorem completeIdentitySecondGraphToChart_isIso :
    IsIso (completeIdentityTopGraphToChart K n h 1) :=
  completeIdentityTopGraphToChart_isIso K n h 1
    (completeIdentitySecondPrecedingDefect K n h)

/-- The unchanged smaller coefficient map of the original second graph is flat. -/
theorem completeIdentitySecondGraphOriginalScalars_flat :
    (completeIdentityTopGraphOriginalScalars K n h 0 1).Flat :=
  completeIdentityTopGraphOriginalScalars_flat K n h 1
    (completeIdentitySecondPrecedingDefect K n h)

/-- The actual second-stage universal action extends to the full source node. -/
def completeIdentitySecondOriginalNode :
    ChartRing (parameter K[T;T⁻¹] 2) →ₐ[Ring K[T;T⁻¹] 2]
      ChartRing (parameter K[T;T⁻¹] 2) :=
  completeIdentityTopGraphOriginalFlatNode K n h 0 1
    (completeIdentitySecondPrecedingDefect K n h)
    (completeIdentitySecondGraphOriginalScalars_flat K n h)

/-- The constructed second node retains the exact original outgoing action. -/
theorem completeIdentitySecondOriginalNode_left :
    leftLaurentMap (parameter K[T;T⁻¹] 2)
      (completeIdentitySecondOriginalNode K n h (leftCoordinate (parameter K[T;T⁻¹] 2))) =
        (completeIdentityTopActionUnit K n h 0 1).val :=
  completeIdentityTopGraphOriginalFlatNode_left K n h 0 1
    (completeIdentitySecondPrecedingDefect K n h)
    (completeIdentitySecondGraphOriginalScalars_flat K n h)

/-- The same second node retains the exact reciprocal incoming action. -/
theorem completeIdentitySecondOriginalNode_right :
    leftLaurentMap (parameter K[T;T⁻¹] 2) (branchSwapMap (parameter K[T;T⁻¹] 2)
      (completeIdentitySecondOriginalNode K n h (rightCoordinate (parameter K[T;T⁻¹] 2)))) =
        LaurentPolynomial.invert (completeIdentityTopActionUnit K n h 0 1)⁻¹.val :=
  completeIdentityTopGraphOriginalFlatNode_right K n h 0 1
    (completeIdentitySecondPrecedingDefect K n h)
    (completeIdentitySecondGraphOriginalScalars_flat K n h)

end FLT.Mazur.PolygonInfinitesimalStages
