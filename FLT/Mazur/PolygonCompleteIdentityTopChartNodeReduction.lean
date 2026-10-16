/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartSourceFunctions
public import FLT.Mazur.PolygonCompleteIdentityTopGraphReduction

/-!
# Original node functions and reduction on the whole higher graph chart

The source ring maps to actual chart functions and evaluates to the original
finite-graph source. Composing with its reduction yields a map from the full
chart onto the unchanged split node, with every source function retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
  completeIdentityTopGraphReduction
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "e" => parameter (R) (m + 1)
local notation "B" => ChartRing (e)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "E" => completeIdentityTopGraphAlgebra K n h (0 : Fin n) m
local notation "s" => completeIdentityTopChartSource K n h m
local notation "f" => completeIdentityTopGraphToChart K n h m
local notation "p" => completeIdentityTopChartSourceFunctions K n h m
variable (hm : completeIdentityFiniteMulDefect K n h 0 m = 0)
/-- Cache the existing finite-graph ring structure for the full source comparison. -/
local instance topChartNodeReductionCommRing : CommRing (E) := inferInstance

/-- The original whole chart reduces onto the unchanged split node through the full comparison. -/
def completeIdentityTopChartNodeReduction : Γ((H), ⊤) →+* ChartRing (0 : R) :=
  (completeIdentityTopGraphReduction K n h 0 m hm).comp (SpectrumGlobalRange.ringHom (f))

/-- The chart reduction uses the original node reduction on every source function. -/
theorem completeIdentityTopChartNodeReduction_source (z : B) :
    completeIdentityTopChartNodeReduction K n h m hm ((p) z) = topNodeReduction (R) m z := by
  change completeIdentityTopGraphReduction K n h 0 m hm
    (SpectrumGlobalRange.ringHom (f) ((p) z)) = _
  rw [completeIdentityTopChartSourceFunctions_evaluation,
    completeIdentityTopGraphReduction_source]

/-- The actual chart reduction kills the unchanged original smoothing parameter. -/
theorem completeIdentityTopChartNodeReduction_parameter :
    completeIdentityTopChartNodeReduction K n h m hm
      (completeIdentityTopChartParameter K n h m) = 0 := by
  rw [← completeIdentityTopChartSourceFunctions_parameter,
    completeIdentityTopChartNodeReduction_source, topNodeReduction,
    ringMap_scalar]
  change algebraMap (R) (ChartRing (0 : R)) (reduction (R) (m + 1) (e)) = 0
  rw [reduction_parameter, map_zero]

/-- Every original split-node function is attained by the actual chart reduction. -/
theorem completeIdentityTopChartNodeReduction_surjective :
    Function.Surjective (completeIdentityTopChartNodeReduction K n h m hm) := by
  intro z
  obtain ⟨w, rfl⟩ := topNodeReduction_surjective (R) m z
  exact ⟨(p) w, completeIdentityTopChartNodeReduction_source K n h m hm w⟩

end FLT.Mazur.PolygonInfinitesimalStages
