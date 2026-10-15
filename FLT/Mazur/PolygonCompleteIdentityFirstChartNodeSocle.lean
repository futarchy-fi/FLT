/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartKernelPowers
public import FLT.Mazur.TwoCoordinateTorsionSocle

/-!
# Exact node-socle obstruction to identifying the original first chart

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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "I" => completeIdentityFirstChartNodeKernel K n h
local notation "x" => completeIdentityFirstChartSourceX K n h
local notation "y" => completeIdentityFirstChartSourceY K n h
local notation "f" => completeIdentityFirstGraphToChart K n h

/-- Any actual nonzero comparison error supplies a nonzero original node-socle element. -/
theorem completeIdentityFirstChartNodeKernel_socle (z : Γ((H), ⊤))
    (hz : z ∈ (I)) (hn : z ≠ 0) :
    ∃ w : Γ((H), ⊤), w ∈ (I) ∧ w ≠ 0 ∧ (x) * w = 0 ∧ (y) * w = 0 := by
  obtain ⟨a, b, ha, hb⟩ := completeIdentityFirstChartNodeKernel_powers K n h z hz
  exact TwoCoordinateTorsionSocle.exists_common_annihilator (I) (x) (y) z hz hn ha hb

/-- The whole unchanged kernel vanishes exactly when its original node socle vanishes. -/
theorem completeIdentityFirstChartNodeKernel_eq_bot_iff :
    (I) = ⊥ ↔ ∀ z ∈ (I), (x) * z = 0 → (y) * z = 0 → z = 0 :=
  TwoCoordinateTorsionSocle.eq_bot_iff (I) (x) (y)
    (completeIdentityFirstChartNodeKernel_powers K n h)

/-- Vanishing of the actual kernel identifies the full original chart, including nilpotents. -/
theorem completeIdentityFirstGraphToChart_isIso_of_kernel (hi : (I) = ⊥) : IsIso (f) := by
  have he : Function.Injective (SpectrumGlobalRange.ringHom (f)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hi
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  exact Function.Injective.of_comp he

/-- An original node-socle vanishing argument suffices for the actual chart identification. -/
theorem completeIdentityFirstGraphToChart_isIso_of_nodeSocle
    (hs : ∀ z ∈ (I), (x) * z = 0 → (y) * z = 0 → z = 0) : IsIso (f) :=
  completeIdentityFirstGraphToChart_isIso_of_kernel K n h
    ((completeIdentityFirstChartNodeKernel_eq_bot_iff K n h).mpr hs)

end FLT.Mazur.PolygonInfinitesimalStages
