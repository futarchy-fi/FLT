/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartParameterLayer
public import FLT.Mazur.ExactParameterLayer

/-!
# The literal closed fiber embeds in the original higher graph chart

The quotient is taken by the unchanged original base parameter. Its
faithful layer map preserves both actual source-coordinate actions.
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
local notation "t" => completeIdentityTopChartParameter K n h m

/-- The full special-fiber ring of the literal original graph chart. -/
abbrev completeIdentityTopChartClosedFiber := Γ((H), ⊤) ⧸ Ideal.span {(t)}

/-- The quotient retains the actual original parameter ideal. -/
def completeIdentityTopChartClosedQuotient :
    Γ((H), ⊤) →+* completeIdentityTopChartClosedFiber K n h m := Ideal.Quotient.mk _

/-- Multiplication by the original last power embeds its full closed-fiber layer. -/
def completeIdentityTopChartClosedLayer :
    completeIdentityTopChartClosedFiber K n h m →ₗ[Γ((H), ⊤)] Γ((H), ⊤) :=
  ExactParameterLayer.layer (t) ((t) ^ (m + 1))
    (by rw [← pow_succ, completeIdentityTopChartParameter_pow])
local notation "q" => completeIdentityTopChartClosedQuotient K n h m
local notation "l" => completeIdentityTopChartClosedLayer K n h m

/-- Every quotient representative maps to its original last-power multiple. -/
theorem completeIdentityTopChartClosedLayer_mk (z : Γ((H), ⊤)) :
    (l) ((q) z) = (t) ^ (m + 1) * z := rfl

/-- The entire closed fiber, including its nilpotents, embeds faithfully. -/
theorem completeIdentityTopChartClosedLayer_injective : Function.Injective (l) :=
  ExactParameterLayer.layer_injective _ _ _
    (completeIdentityTopChartLastPower_annihilator K n h m)

/-- This is an equivariant embedding for every original chart function. -/
theorem completeIdentityTopChartClosedLayer_mul (x : Γ((H), ⊤))
    (z : completeIdentityTopChartClosedFiber K n h m) :
    (l) ((q) x * z) = x * (l) z := ExactParameterLayer.layer_mul ..

/-- Every original coordinate annihilator comes from a unique actual closed-fiber function. -/
theorem completeIdentityTopChartClosedLayer_socle (z : Γ((H), ⊤))
    (hx : completeIdentityTopChartSourceX K n h m * z = 0)
    (hy : completeIdentityTopChartSourceY K n h m * z = 0) :
    ∃! w : completeIdentityTopChartClosedFiber K n h m, (l) w = z ∧
      (q) (completeIdentityTopChartSourceX K n h m) * w = 0 ∧
      (q) (completeIdentityTopChartSourceY K n h m) * w = 0 :=
  ExactParameterLayer.socle_lift _ _ _
    (completeIdentityTopChartLastPower_annihilator K n h m)
    (completeIdentityTopChartParameter_annihilator K n h m) _ _
    (completeIdentityTopChartSource_xy K n h m) z hx hy

end FLT.Mazur.PolygonInfinitesimalStages
