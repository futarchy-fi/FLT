/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphIncomingBranch
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphBranchExt

/-!
# The full finite graph satisfies the original cubic action equation

The actual incoming graph chart proves the missing right-branch equation.
Schematic density of the two punctures then proves the unchanged cubic
relation on the entire finite graph, including its node-supported nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "W" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "r" => completeIdentityFirstGraphRightBranch K n h (0 : Fin n)
local notation "s" => completeIdentityFirstGraphOriginalSource K n h (0 : Fin n)
local notation "d" => completeIdentityFirstGraphOriginalTarget K n h (0 : Fin n)
local notation "f" => completeIdentityFiniteInput K n h (0 : Fin n) 1
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "p" => originalStageToCompatibleProj K n h 1
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)

/-- The actual adjacent component proves the full original cubic equation on the right puncture. -/
@[reassoc] theorem completeIdentityFirstGraphOriginalNodes_right_cubic :
    (r) ≫ (d) ≫ (p) ≫ (c) = (r) ≫ (s) ≫ (f) ≫ (a) := by
  rw [← completeIdentityFirstRightToGraphChart_target_polygon_assoc,
    ← completeIdentityFirstRightToGraphChart_source_polygon_assoc,
    completeIdentityActionGraphAdicChartTarget, completeIdentityActionGraphAdicChartSource]
  simp only [Category.assoc]
  rw [← completeIdentityActionAdicChartSpace_cubic]

/-- The whole finite graph, with its original coefficients and nilpotents, obeys the cubic law. -/
@[reassoc] theorem completeIdentityFirstGraphOriginalNodes_cubic :
    (d) ≫ (p) ≫ (c) = (s) ≫ (f) ≫ (a) := by
  let _ : IsSeparated (terminal.from (integralCurve (W))) := by
    rw [← terminal.comp_from (integralCurveStructure (W))]
    infer_instance
  apply completeIdentityFirstGraph_ext K n h 0
    (terminal.from (integralCurve (W))) _ _ (Subsingleton.elim _ _)
  · exact completeIdentityFirstGraphOriginalNodes_left_cubic K n h 0
  · exact completeIdentityFirstGraphOriginalNodes_right_cubic K n h

end FLT.Mazur.PolygonInfinitesimalStages
