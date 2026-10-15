/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartParameterLayer
public import FLT.Mazur.PolygonCompleteIdentityFirstChartBranchQuotient
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphReduction

/-!
# Original node functions and reduction on the whole first graph chart

The source ring maps to actual chart functions and evaluates to the original
finite-graph source. Composing with its reduction yields a map from the full
chart onto the unchanged split node, with every source function retained.
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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "E" => completeIdentityFirstErrorAlgebra K n h (0 : Fin n)
local notation "s" => completeIdentityFirstChartSource K n h
local notation "f" => completeIdentityFirstGraphToChart K n h
local notation "v" => completeIdentityFirstGraphSource K n h (0 : Fin n)
/-- Cache the existing finite-graph ring structure for the full source comparison. -/
local instance firstChartSourceFunctionsCommRing : CommRing (E) := inferInstance

/-- Pull all actual source-node functions to the original whole chart. -/
def completeIdentityFirstChartSourceFunctions : (B) →+* Γ((H), ⊤) :=
  (s).appTop.hom.comp (Scheme.ΓSpecIso (.of (B))).inv.hom
local notation "p" => completeIdentityFirstChartSourceFunctions K n h

/-- The source retains the actual original smoothing parameter as a chart function. -/
theorem completeIdentityFirstChartSourceFunctions_parameter :
    (p) (algebraMap (S) (B) (e)) = completeIdentityFirstChartParameter K n h := by
  have he := completeIdentityFirstChartSource_xy K n h
  change (p) (leftCoordinate (e)) * (p) (rightCoordinate (e)) = _ at he
  rw [← map_mul, coordinate_relation] at he
  exact he

/-- The original comparison evaluates every source-node function without changing it. -/
theorem completeIdentityFirstChartSourceFunctions_evaluation (z : B) :
    SpectrumGlobalRange.ringHom (f) ((p) z) = (v) z := by
  have he : (f) ≫ (s) = Spec.map (CommRingCat.ofHom (v).toRingHom) := by
    rw [completeIdentityFirstChartSource, ← Category.assoc,
      completeIdentityFirstGraphToChart_source, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    rfl
  have hh : (Scheme.ΓSpecIso (.of (B))).inv ≫ (s).appTop ≫ (f).appTop ≫
      (Scheme.ΓSpecIso (.of (E))).hom = CommRingCat.ofHom (v).toRingHom := by
    rw [← Category.assoc (s).appTop, ← Scheme.Hom.comp_appTop, he,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun g : CommRingCat.of (B) ⟶ CommRingCat.of (E) ↦ g z) hh

/-- The original whole chart reduces onto the unchanged split node through the full comparison. -/
def completeIdentityFirstChartNodeReduction : Γ((H), ⊤) →+* ChartRing (0 : R) :=
  (completeIdentityFirstGraphReduction K n h 0).comp (SpectrumGlobalRange.ringHom (f))

/-- The chart reduction uses the original node reduction on every source function. -/
theorem completeIdentityFirstChartNodeReduction_source (z : B) :
    completeIdentityFirstChartNodeReduction K n h ((p) z) = firstNodeReduction (R) z := by
  change completeIdentityFirstGraphReduction K n h 0
    (SpectrumGlobalRange.ringHom (f) ((p) z)) = _
  rw [completeIdentityFirstChartSourceFunctions_evaluation,
    completeIdentityFirstGraphReduction_source]

/-- The actual chart reduction kills the unchanged original smoothing parameter. -/
theorem completeIdentityFirstChartNodeReduction_parameter :
    completeIdentityFirstChartNodeReduction K n h
      (completeIdentityFirstChartParameter K n h) = 0 := by
  rw [← completeIdentityFirstChartSourceFunctions_parameter,
    completeIdentityFirstChartNodeReduction_source, firstNodeReduction,
    ringMap_scalar]
  change algebraMap (R) (ChartRing (0 : R)) (reduction (R) 1 (e)) = 0
  rw [reduction_parameter, map_zero]

/-- Every original split-node function is attained by the actual chart reduction. -/
theorem completeIdentityFirstChartNodeReduction_surjective :
    Function.Surjective (completeIdentityFirstChartNodeReduction K n h) := by
  intro z
  obtain ⟨w, rfl⟩ := firstNodeReduction_surjective (R) z
  exact ⟨(p) w, completeIdentityFirstChartNodeReduction_source K n h w⟩

end FLT.Mazur.PolygonInfinitesimalStages
