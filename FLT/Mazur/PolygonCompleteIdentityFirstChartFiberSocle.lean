/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartClosedLayer
public import FLT.Mazur.PolygonCompleteIdentityFirstChartSocleKernel

/-!
# The exact remaining obstruction is in the literal original closed fiber

The faithful parameter layer identifies common coordinate annihilators in
the full chart and its actual closed fiber. Thus proving absence of the
latter is equivalent to killing the entire original comparison kernel.
This does not claim that the closed-fiber socle vanishes.
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
local notation "Q" => completeIdentityFirstChartClosedFiber K n h
local notation "I" => completeIdentityFirstChartNodeKernel K n h
local notation "x" => completeIdentityFirstChartSourceX K n h
local notation "y" => completeIdentityFirstChartSourceY K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "l" => completeIdentityFirstChartClosedLayer K n h

/-- Every actual closed-fiber node-socle element embeds in the original comparison kernel. -/
theorem completeIdentityFirstChartClosedLayer_mem_kernel (z : Q)
    (hx : (q) (x) * z = 0) (hy : (q) (y) * z = 0) : (l) z ∈ (I) := by
  apply completeIdentityFirstChartSocle_mem_kernel K n h
  · rw [← completeIdentityFirstChartClosedLayer_mul, hx, map_zero]
  · rw [← completeIdentityFirstChartClosedLayer_mul, hy, map_zero]

/-- Nonzero literal closed-fiber socle elements give nonzero original comparison errors. -/
theorem completeIdentityFirstChartClosedLayer_ne_zero (z : Q) (hz : z ≠ 0) :
    (l) z ≠ 0 := by
  intro he
  apply hz
  apply completeIdentityFirstChartClosedLayer_injective K n h
  simpa only [map_zero] using he

/-- The full original kernel vanishes exactly when its literal closed fiber has no node socle. -/
theorem completeIdentityFirstChartNodeKernel_eq_bot_iff_closedSocle :
    (I) = ⊥ ↔ ∀ z : Q, (q) (x) * z = 0 → (q) (y) * z = 0 → z = 0 := by
  constructor
  · intro hi z hx hy
    have hz := completeIdentityFirstChartClosedLayer_mem_kernel K n h z hx hy
    rw [hi, Ideal.mem_bot] at hz
    exact (map_eq_zero_iff _ (completeIdentityFirstChartClosedLayer_injective K n h)).mp hz
  · intro hs
    apply (completeIdentityFirstChartNodeKernel_eq_bot_iff_socle K n h).mpr
    intro z hx hy
    obtain ⟨w, hw, _⟩ := completeIdentityFirstChartClosedLayer_socle K n h z hx hy
    rw [hs w hw.2.1 hw.2.2, map_zero] at hw
    exact hw.1.symm

/-- Actual closed-fiber node-socle vanishing identifies the full original first chart. -/
theorem completeIdentityFirstGraphToChart_isIso_of_closedSocle
    (hs : ∀ z : Q, (q) (x) * z = 0 → (q) (y) * z = 0 → z = 0) :
    IsIso (completeIdentityFirstGraphToChart K n h) :=
  completeIdentityFirstGraphToChart_isIso_of_kernel K n h
    ((completeIdentityFirstChartNodeKernel_eq_bot_iff_closedSocle K n h).mpr hs)

end FLT.Mazur.PolygonInfinitesimalStages
