/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartKernelPowers
public import FLT.Mazur.TwoCoordinateTorsionSocle
public import FLT.Mazur.PolygonCompleteIdentityTopGraphChartFlat

/-!
# Exact node-socle obstruction to identifying the original higher chart

If the actual comparison kernel is nonzero, it contains a nonzero function
killed by both original node coordinates. Conversely, ruling out precisely
these functions identifies the full finite graph with the original chart.
No node-socle vanishing is assumed as data or proved here.
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
local notation "I" => completeIdentityTopChartNodeKernel K n h m
local notation "x" => completeIdentityTopChartSourceX K n h m
local notation "y" => completeIdentityTopChartSourceY K n h m
local notation "f" => completeIdentityTopGraphToChart K n h m

/-- Any actual nonzero comparison error supplies a nonzero original node-socle element. -/
theorem completeIdentityTopChartNodeKernel_socle (z : Γ((H), ⊤))
    (hz : z ∈ (I)) (hn : z ≠ 0) :
    ∃ w : Γ((H), ⊤), w ∈ (I) ∧ w ≠ 0 ∧ (x) * w = 0 ∧ (y) * w = 0 := by
  obtain ⟨a, b, ha, hb⟩ := completeIdentityTopChartNodeKernel_powers K n h m z hz
  exact TwoCoordinateTorsionSocle.exists_common_annihilator (I) (x) (y) z hz hn ha hb

/-- The whole unchanged kernel vanishes exactly when its original node socle vanishes. -/
theorem completeIdentityTopChartNodeKernel_eq_bot_iff :
    (I) = ⊥ ↔ ∀ z ∈ (I), (x) * z = 0 → (y) * z = 0 → z = 0 :=
  TwoCoordinateTorsionSocle.eq_bot_iff (I) (x) (y)
    (completeIdentityTopChartNodeKernel_powers K n h m)

/-- An original node-socle vanishing argument suffices for the actual chart identification. -/
theorem completeIdentityTopGraphToChart_isIso_of_nodeSocle
    (hs : ∀ z ∈ (I), (x) * z = 0 → (y) * z = 0 → z = 0) : IsIso (f) :=
  completeIdentityTopGraphToChart_isIso_of_kernel K n h m
    ((completeIdentityTopChartNodeKernel_eq_bot_iff K n h m).mpr hs)

end FLT.Mazur.PolygonInfinitesimalStages
