/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartScalars
public import FLT.Mazur.PolygonStageFlatLayer

/-!
# Exact parameter annihilators in the literal first graph chart

Original-base flatness identifies the parameter annihilator with its image.
Consequently every common source-coordinate annihilator is a parameter
multiple and its product with every other such element is zero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "a" => completeIdentityActionGraphAdicChartScalars K n h 1 0 0
local notation "x" => completeIdentityFirstChartSourceX K n h
local notation "y" => completeIdentityFirstChartSourceY K n h

/-- The original smoothing parameter as a global function on the full chart. -/
def completeIdentityFirstChartParameter : Γ((H), ⊤) := (a) (parameter K 1)
local notation "t" => completeIdentityFirstChartParameter K n h

/-- The actual first-chart parameter is square-zero. -/
theorem completeIdentityFirstChartParameter_sq : (t) ^ 2 = 0 := by
  change ((a) (parameter K 1)) ^ 2 = 0
  rw [← map_pow, parameter_pow, map_zero]

/-- Flatness over the original base gives the exact parameter annihilator. -/
theorem completeIdentityFirstChartParameter_annihilator (z : Γ((H), ⊤)) :
    (t) * z = 0 ↔ ∃ w : Γ((H), ⊤), (t) * w = z := by
  let _ := (a).toAlgebra
  let _ : Module.Flat (Ring K 1) Γ((H), ⊤) :=
    completeIdentityActionGraphAdicChartScalars_flat K n h 1 0 0
  have he := flat_parameter_smul_eq_zero_iff K 0 Γ((H), ⊤) z
  change parameter K 1 • z = 0 ↔ ∃ w, parameter K 1 ^ 1 • w = z at he
  rw [pow_one] at he
  exact he

/-- Any original common node annihilator is an actual parameter multiple. -/
theorem completeIdentityFirstChartSocle_parameter (z : Γ((H), ⊤))
    (hx : (x) * z = 0) : ∃ w : Γ((H), ⊤), (t) * w = z := by
  apply (completeIdentityFirstChartParameter_annihilator K n h z).mp
  rw [completeIdentityFirstChartParameter, ← completeIdentityFirstChartSource_xy,
    mul_right_comm, hx, zero_mul]

/-- Products of original source-coordinate annihilators vanish in the full chart. -/
theorem completeIdentityFirstChartSocle_mul (z w : Γ((H), ⊤))
    (hz : (x) * z = 0) (hw : (x) * w = 0) : z * w = 0 := by
  obtain ⟨u, rfl⟩ := completeIdentityFirstChartSocle_parameter K n h z hz
  obtain ⟨v, rfl⟩ := completeIdentityFirstChartSocle_parameter K n h w hw
  calc
    ((t) * u) * ((t) * v) = (t) ^ 2 * (u * v) := by ring
    _ = 0 := by rw [completeIdentityFirstChartParameter_sq, zero_mul]

end FLT.Mazur.PolygonInfinitesimalStages
