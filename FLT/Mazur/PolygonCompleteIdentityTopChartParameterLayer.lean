/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartScalars
public import FLT.Mazur.PolygonStageFlatLayer

/-!
# Exact parameter annihilators in the literal higher graph chart

Original-base flatness identifies the parameter annihilator with the last-power image.
Consequently every common source-coordinate annihilator is a last-power
multiple at the full original stage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "a" => completeIdentityActionGraphAdicChartScalars K n h (m + 1) 0 0
local notation "x" => completeIdentityTopChartSourceX K n h m
local notation "y" => completeIdentityTopChartSourceY K n h m

/-- The original smoothing parameter as a global function on the full chart. -/
def completeIdentityTopChartParameter : Γ((H), ⊤) := (a) (parameter K (m + 1))
local notation "t" => completeIdentityTopChartParameter K n h m

/-- The actual higher-chart parameter has its original nilpotence order. -/
theorem completeIdentityTopChartParameter_pow : (t) ^ (m + 2) = 0 := by
  change ((a) (parameter K (m + 1))) ^ (m + 2) = 0
  rw [← map_pow, parameter_pow, map_zero]

/-- Flatness over the original base gives the exact parameter annihilator. -/
theorem completeIdentityTopChartParameter_annihilator (z : Γ((H), ⊤)) :
    (t) * z = 0 ↔ ∃ w : Γ((H), ⊤), (t) ^ (m + 1) * w = z := by
  let _ := (a).toAlgebra
  let _ : Module.Flat (Ring K (m + 1)) Γ((H), ⊤) :=
    completeIdentityActionGraphAdicChartScalars_flat K n h (m + 1) 0 0
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow,
    completeIdentityTopChartParameter] using
    (flat_parameter_smul_eq_zero_iff K m Γ((H), ⊤) z)

/-- Flatness also identifies the last-power annihilator with the parameter ideal. -/
theorem completeIdentityTopChartLastPower_annihilator (z : Γ((H), ⊤)) :
    (t) ^ (m + 1) * z = 0 ↔ ∃ w : Γ((H), ⊤), (t) * w = z := by
  let _ := (a).toAlgebra
  let _ : Module.Flat (Ring K (m + 1)) Γ((H), ⊤) :=
    completeIdentityActionGraphAdicChartScalars_flat K n h (m + 1) 0 0
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow,
    completeIdentityTopChartParameter] using
    (flat_last_smul_eq_zero_iff K m Γ((H), ⊤) z)

/-- Any original common node annihilator is an actual last-power multiple. -/
theorem completeIdentityTopChartSocle_parameter (z : Γ((H), ⊤))
    (hx : (x) * z = 0) : ∃ w : Γ((H), ⊤), (t) ^ (m + 1) * w = z := by
  apply (completeIdentityTopChartParameter_annihilator K n h m z).mp
  rw [completeIdentityTopChartParameter, ← completeIdentityTopChartSource_xy,
    mul_right_comm, hx, zero_mul]

end FLT.Mazur.PolygonInfinitesimalStages
