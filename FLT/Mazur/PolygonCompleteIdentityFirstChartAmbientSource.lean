/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartSourceFunctions

/-!
# Original source functions on the full ambient first-node relation

These functions precede restriction by the complete graph ideal. The
parameter and both coordinates restrict to the unchanged chart functions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (e)
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0

/-- Original source functions on the node-relation space, before imposing the graph ideal. -/
def completeIdentityFirstAmbientSourceFunctions : (B) →+* Γ((R), ⊤) :=
  (pullback.fst _ _ ≫ (firstNodeParameterIso K).inv).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (B))).inv.hom
local notation "p" => completeIdentityFirstAmbientSourceFunctions K n h

/-- Restricting an ambient source function gives its actual full-chart function. -/
theorem completeIdentityFirstAmbientSourceFunctions_restrict (z : B) :
    (c).appTop ((p) z) = completeIdentityFirstChartSourceFunctions K n h z := by
  change ((Scheme.ΓSpecIso (.of (B))).inv ≫
    (pullback.fst _ _ ≫ (firstNodeParameterIso K).inv).appTop ≫ (c).appTop) z = _
  rw [← Scheme.Hom.comp_appTop]
  rfl

/-- The original smoothing parameter in the ambient relation ring. -/
def completeIdentityFirstAmbientParameter : Γ((R), ⊤) :=
  (p) (algebraMap (S) (B) (e))

/-- The ambient parameter restricts to the original flat chart's parameter. -/
theorem completeIdentityFirstAmbientParameter_restrict :
    (c).appTop (completeIdentityFirstAmbientParameter K n h) =
      completeIdentityFirstChartParameter K n h := by
  rw [completeIdentityFirstAmbientParameter,
    completeIdentityFirstAmbientSourceFunctions_restrict,
    completeIdentityFirstChartSourceFunctions_parameter]

/-- Both original source coordinates multiply to the ambient smoothing parameter. -/
theorem completeIdentityFirstAmbientSourceFunctions_xy :
    (p) (leftCoordinate (e)) * (p) (rightCoordinate (e)) =
      completeIdentityFirstAmbientParameter K n h := by
  rw [← map_mul, coordinate_relation]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
