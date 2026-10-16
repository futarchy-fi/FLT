/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartParameterLayer
public import FLT.Mazur.PolygonCompleteIdentityTopChartBranchQuotient

/-!
# Original node functions on the whole higher graph chart

The source ring maps to actual chart functions and evaluates to the original
finite-graph source. The source map retains the complete original node
ring and every original coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) (m + 1)
local notation "e" => parameter (R) (m + 1)
local notation "B" => ChartRing (e)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "E" => completeIdentityTopGraphAlgebra K n h (0 : Fin n) m
local notation "s" => completeIdentityTopChartSource K n h m
local notation "f" => completeIdentityTopGraphToChart K n h m
local notation "v" => topNodeGraphSource K[T;T⁻¹] m
  (completeIdentityTopActionUnit K n h 0 m)
  (completeIdentityTopActionReciprocalUnit K n h 0 m)
/-- Cache the existing finite-graph ring structure for the full source comparison. -/
local instance topChartSourceFunctionsCommRing : CommRing (E) := inferInstance

/-- Pull all actual source-node functions to the original whole chart. -/
def completeIdentityTopChartSourceFunctions : (B) →+* Γ((H), ⊤) :=
  (s).appTop.hom.comp (Scheme.ΓSpecIso (.of (B))).inv.hom
local notation "p" => completeIdentityTopChartSourceFunctions K n h m

/-- The source retains the actual original smoothing parameter as a chart function. -/
theorem completeIdentityTopChartSourceFunctions_parameter :
    (p) (algebraMap (S) (B) (e)) = completeIdentityTopChartParameter K n h m := by
  have he := completeIdentityTopChartSource_xy K n h m
  change (p) (leftCoordinate (e)) * (p) (rightCoordinate (e)) = _ at he
  rw [← map_mul, coordinate_relation] at he
  exact he

/-- The original comparison evaluates every source-node function without changing it. -/
theorem completeIdentityTopChartSourceFunctions_evaluation (z : B) :
    SpectrumGlobalRange.ringHom (f) ((p) z) = (v) z := by
  have he : (f) ≫ (s) = Spec.map (CommRingCat.ofHom (v).toRingHom) := by
    rw [completeIdentityTopChartSource, ← Category.assoc,
      completeIdentityTopGraphToChart_source, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    rfl
  have hh : (Scheme.ΓSpecIso (.of (B))).inv ≫ (s).appTop ≫ (f).appTop ≫
      (Scheme.ΓSpecIso (.of (E))).hom = CommRingCat.ofHom (v).toRingHom := by
    rw [← Category.assoc (s).appTop, ← Scheme.Hom.comp_appTop, he,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun g : CommRingCat.of (B) ⟶ CommRingCat.of (E) ↦ g z) hh

end FLT.Mazur.PolygonInfinitesimalStages
