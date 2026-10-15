/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartParameterLayer
public import FLT.Mazur.SquareZeroParameterLayer

/-!
# The literal closed fiber embeds in the original first graph chart

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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "t" => completeIdentityFirstChartParameter K n h

/-- The full special-fiber ring of the literal original graph chart. -/
abbrev completeIdentityFirstChartClosedFiber := Γ((H), ⊤) ⧸ Ideal.span {(t)}

/-- The quotient retains the actual original parameter ideal. -/
def completeIdentityFirstChartClosedQuotient :
    Γ((H), ⊤) →+* completeIdentityFirstChartClosedFiber K n h := Ideal.Quotient.mk _

/-- Multiplication by the original parameter embeds its full closed-fiber layer. -/
def completeIdentityFirstChartClosedLayer :
    completeIdentityFirstChartClosedFiber K n h →ₗ[Γ((H), ⊤)] Γ((H), ⊤) :=
  SquareZeroParameterLayer.layer (t)
    (by simpa only [pow_two] using completeIdentityFirstChartParameter_sq K n h)
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "l" => completeIdentityFirstChartClosedLayer K n h

/-- Every quotient representative maps to its original parameter multiple. -/
theorem completeIdentityFirstChartClosedLayer_mk (z : Γ((H), ⊤)) :
    (l) ((q) z) = (t) * z := rfl

/-- The entire closed fiber, including its nilpotents, embeds faithfully. -/
theorem completeIdentityFirstChartClosedLayer_injective : Function.Injective (l) :=
  SquareZeroParameterLayer.layer_injective _ _
    (completeIdentityFirstChartParameter_annihilator K n h)

/-- This is an equivariant embedding for every original chart function. -/
theorem completeIdentityFirstChartClosedLayer_mul (x : Γ((H), ⊤))
    (z : completeIdentityFirstChartClosedFiber K n h) :
    (l) ((q) x * z) = x * (l) z := SquareZeroParameterLayer.layer_mul ..

/-- Every original coordinate annihilator comes from a unique actual closed-fiber function. -/
theorem completeIdentityFirstChartClosedLayer_socle (z : Γ((H), ⊤))
    (hx : completeIdentityFirstChartSourceX K n h * z = 0)
    (hy : completeIdentityFirstChartSourceY K n h * z = 0) :
    ∃! w : completeIdentityFirstChartClosedFiber K n h, (l) w = z ∧
      (q) (completeIdentityFirstChartSourceX K n h) * w = 0 ∧
      (q) (completeIdentityFirstChartSourceY K n h) * w = 0 :=
  SquareZeroParameterLayer.socle_lift _ _
    (completeIdentityFirstChartParameter_annihilator K n h) _ _
    (completeIdentityFirstChartSource_xy K n h) z hx hy

end FLT.Mazur.PolygonInfinitesimalStages
