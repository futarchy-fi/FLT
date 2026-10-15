/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartResidualCoordinates
public import FLT.Mazur.PolygonCompleteIdentityFirstChartFiberSocle

/-!
# Actual closed-fiber normal form and the remaining two-error socle test

Every actual closed-fiber function is its original node value plus a
combination of the two actual coordinate errors. Thus node preservation
reduces to common-annihilator vanishing for those combinations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstChartClosedError completeIdentityFirstChartClosedReduction
  completeIdentityFirstChartClosedSection completeIdentityFirstChartClosedQuotient
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "t" => parameter K 1
local notation "Q" => completeIdentityFirstChartClosedFiber K n h
local notation "r" => completeIdentityFirstChartClosedReduction K n h
local notation "s" => completeIdentityFirstChartClosedSection K n h
local notation "δ" => completeIdentityFirstChartClosedError K n h
local notation "dx" => (δ) (leftCoordinate (t))
local notation "dy" => (δ) (rightCoordinate (t))
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "x" => (q) (completeIdentityFirstChartSourceX K n h)
local notation "y" => (q) (completeIdentityFirstChartSourceY K n h)

/-- Every residual element is a combination of the two actual original coordinate errors. -/
theorem completeIdentityFirstChartResidual_normalForm (z : Q) (hz : (r) z = 0) :
    ∃ a b : Q, a * (dx) + b * (dy) = z := by
  apply Ideal.mem_span_pair.mp
  rw [← completeIdentityFirstChartResidualKernel_twoCoordinates]
  exact hz

/-- Every full closed-fiber function retains its original node part and its two error terms. -/
theorem completeIdentityFirstChartClosed_normalForm (z : Q) :
    ∃ a b : Q, z = (s) ((r) z) + a * (dx) + b * (dy) := by
  have hz : (r) (z - (s) ((r) z)) = 0 := by
    rw [map_sub, completeIdentityFirstChartClosedSection_rightInverse K n h, sub_self]
  obtain ⟨a, b, hab⟩ := completeIdentityFirstChartResidual_normalForm K n h _ hz
  refine ⟨a, b, ?_⟩
  calc
    z = (s) ((r) z) + (z - (s) ((r) z)) := by abel
    _ = (s) ((r) z) + a * (dx) + b * (dy) := by rw [← hab, add_assoc]

/-- It suffices to eliminate common coordinate annihilators among the two actual error terms. -/
theorem completeIdentityFirstGraphToChart_isIso_of_residualCoordinates
    (hs : ∀ a b : Q, (x) * (a * (dx) + b * (dy)) = 0 →
      (y) * (a * (dx) + b * (dy)) = 0 → a * (dx) + b * (dy) = 0) :
    IsIso (completeIdentityFirstGraphToChart K n h) := by
  apply completeIdentityFirstGraphToChart_isIso_of_closedSocle K n h
  intro z hx hy
  obtain ⟨a, b, rfl⟩ := completeIdentityFirstChartResidual_normalForm K n h z
    (completeIdentityFirstChartClosedSocle_reduction K n h z hx hy)
  exact hs a b hx hy

end FLT.Mazur.PolygonInfinitesimalStages
