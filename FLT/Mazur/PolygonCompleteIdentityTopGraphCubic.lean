/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopGraphIncomingBranch
public import FLT.Mazur.PolygonTopNodeGraphBranchExt

/-!
# The full higher graph satisfies the original cubic action equation

The actual incoming graph chart proves the missing right-branch equation.
Schematic density of the two punctures then proves the unchanged cubic
relation on the entire higher graph, including its node-supported nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "W" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "r" => completeIdentityTopGraphRightBranch K n h (0 : Fin n) m
local notation "s" => completeIdentityTopGraphOriginalSource K n h (0 : Fin n) m
local notation "d" => completeIdentityTopGraphOriginalTarget K n h (0 : Fin n) m
local notation "f" => completeIdentityFiniteInput K n h (0 : Fin n) (m + 1)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "p" => originalStageToCompatibleProj K n h (m + 1)
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)

/-- The actual adjacent component proves the full original cubic equation on the right puncture. -/
@[reassoc] theorem completeIdentityTopGraphOriginalNodes_right_cubic :
    (r) ≫ (d) ≫ (p) ≫ (c) = (r) ≫ (s) ≫ (f) ≫ (a) := by
  rw [← completeIdentityTopRightToGraphChart_target_polygon_assoc,
    ← completeIdentityTopRightToGraphChart_source_polygon_assoc,
    completeIdentityActionGraphAdicChartTarget, completeIdentityActionGraphAdicChartSource]
  simp only [Category.assoc]
  rw [← completeIdentityActionAdicChartSpace_cubic]

/-- The whole higher graph, with its original coefficients and nilpotents, obeys the cubic law. -/
@[reassoc] theorem completeIdentityTopGraphOriginalNodes_cubic :
    (d) ≫ (p) ≫ (c) = (s) ≫ (f) ≫ (a) := by
  let _ : IsSeparated (terminal.from (integralCurve (W))) := by
    rw [← terminal.comp_from (integralCurveStructure (W))]
    infer_instance
  apply topNodeGraph_ext K[T;T⁻¹] m
    (completeIdentityTopActionUnit K n h 0 m)
    (completeIdentityTopActionReciprocalUnit K n h 0 m)
    (terminal.from (integralCurve (W))) _ _ (Subsingleton.elim _ _)
  · exact completeIdentityTopGraphOriginalNodes_left_cubic K n h 0 m
  · exact completeIdentityTopGraphOriginalNodes_right_cubic K n h m

end FLT.Mazur.PolygonInfinitesimalStages
