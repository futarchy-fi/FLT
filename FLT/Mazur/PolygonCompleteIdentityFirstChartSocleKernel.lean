/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartNodeSocle
public import FLT.Mazur.OpenRangeCoordinateUnit

/-!
# Every common source-coordinate annihilator belongs to the actual kernel

The original source coordinates are units on their respective full
punctures. Thus the kernel condition in the node-socle obstruction is
automatic; it does not impose an extra condition on the remaining geometry.
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
local notation "l" => completeIdentityFirstLeftToGraphChart K n h
local notation "r" => completeIdentityFirstRightToGraphChart K n h

/-- Every common original node annihilator vanishes on both actual graph punctures. -/
theorem completeIdentityFirstChartSocle_mem_kernel (z : Γ((H), ⊤))
    (hx : (x) * z = 0) (hy : (y) * z = 0) : z ∈ (I) := by
  have hl : (l).appTop z = 0 := by
    apply OpenRangeCoordinateUnit.appTop_eq_zero (l) (x) z _ hx
    rw [completeIdentityFirstChartSourceX_open, Scheme.Hom.coe_opensRange]
  have hr : (r).appTop z = 0 := by
    apply OpenRangeCoordinateUnit.appTop_eq_zero (r) (y) z _ hy
    rw [completeIdentityFirstChartSourceY_open, Scheme.Hom.coe_opensRange]
  rw [completeIdentityFirstChartNodeKernel, completeIdentityFirstChartEvaluation_ker]
  constructor
  · change (Scheme.ΓSpecIso _).hom ((l).appTop z) = 0
    rw [hl, map_zero]
  · change (Scheme.ΓSpecIso _).hom ((r).appTop z) = 0
    rw [hr, map_zero]

/-- The actual comparison kernel vanishes precisely when the whole chart has no node socle. -/
theorem completeIdentityFirstChartNodeKernel_eq_bot_iff_socle :
    (I) = ⊥ ↔ ∀ z : Γ((H), ⊤), (x) * z = 0 → (y) * z = 0 → z = 0 := by
  rw [completeIdentityFirstChartNodeKernel_eq_bot_iff]
  constructor
  · intro hs z hx hy
    exact hs z (completeIdentityFirstChartSocle_mem_kernel K n h z hx hy) hx hy
  · intro hs z _ hx hy
    exact hs z hx hy

end FLT.Mazur.PolygonInfinitesimalStages
