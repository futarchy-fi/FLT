/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartSourceFunctions

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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "S" => Ring K[T;T⁻¹] (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "B" => ChartRing (e)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0

/-- Original source functions on the node-relation space, before imposing the graph ideal. -/
def completeIdentityTopAmbientSourceFunctions : (B) →+* Γ((R), ⊤) :=
  (pullback.fst _ _ ≫ (stageNodeParameterIso K (m + 1)).inv).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (B))).inv.hom
local notation "p" => completeIdentityTopAmbientSourceFunctions K n h m

/-- Restricting an ambient source function gives its actual full-chart function. -/
theorem completeIdentityTopAmbientSourceFunctions_restrict (z : B) :
    (c).appTop ((p) z) = completeIdentityTopChartSourceFunctions K n h m z := by
  change ((Scheme.ΓSpecIso (.of (B))).inv ≫
    (pullback.fst _ _ ≫ (stageNodeParameterIso K (m + 1)).inv).appTop ≫ (c).appTop) z = _
  rw [← Scheme.Hom.comp_appTop]
  rfl

/-- The original smoothing parameter in the ambient relation ring. -/
def completeIdentityTopAmbientParameter : Γ((R), ⊤) :=
  (p) (algebraMap (S) (B) (e))

/-- The ambient parameter restricts to the original flat chart's parameter. -/
theorem completeIdentityTopAmbientParameter_restrict :
    (c).appTop (completeIdentityTopAmbientParameter K n h m) =
      completeIdentityTopChartParameter K n h m := by
  rw [completeIdentityTopAmbientParameter,
    completeIdentityTopAmbientSourceFunctions_restrict,
    completeIdentityTopChartSourceFunctions_parameter]

/-- Both original source coordinates multiply to the ambient smoothing parameter. -/
theorem completeIdentityTopAmbientSourceFunctions_xy :
    (p) (leftCoordinate (e)) * (p) (rightCoordinate (e)) =
      completeIdentityTopAmbientParameter K n h m := by
  rw [← map_mul, coordinate_relation]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
