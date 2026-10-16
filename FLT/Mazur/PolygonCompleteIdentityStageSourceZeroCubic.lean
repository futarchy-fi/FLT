/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonUniversalNodeRestriction
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoherence
public import FLT.Mazur.PolygonCompleteIdentityOrderZeroLaw

/-!
# The full parameter-zero source cubic comparison at every stage

Adjacent restriction and its exact kernel transport the proved order-zero
law to any receiving ring that kills the original parameter. All other
nilpotents in that ring are retained; no higher action law is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (j : Fin n)
local notation "d" m => PolygonInfinitesimal.chart
  (Ring K m)[T;T⁻¹] (C (parameter K m)) n h j
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

omit [NeZero n] in
/-- Adjacent universal node restriction is the actual full finite-input restriction. -/
@[reassoc] theorem universalNodeRestriction_chart (m : ℕ) :
    Spec.map (CommRingCat.ofHom (universalNodeRestriction K m)) ≫ (d (m + 1)) =
      (d m) ≫ completeIdentityFiniteRestriction K n h m := by
  rw [completeIdentityFiniteRestriction, scalingParameterMap, chart_parameterProjection]
  rfl

/-- Every parameter-zero receiving map retains the original full source cubic comparison. -/
theorem completeIdentityStageSource_cubic_of_parameter_zero (m : ℕ)
    {T : Type} [CommRing T] (f : ChartRing (C (parameter K m)) →+* T)
    (hf : f (algebraMap (Ring K m)[T;T⁻¹]
      (ChartRing (C (parameter K m))) (C (parameter K m))) = 0) :
    Spec.map (CommRingCat.ofHom f) ≫ (d m) ≫
        completeIdentityFiniteScaling K n h m ≫ (g) =
      Spec.map (CommRingCat.ofHom f) ≫ (d m) ≫
        completeIdentityFiniteInput K n h 0 m ≫ (a) := by
  induction m with
  | zero => rw [completeIdentityFiniteComparison_zero]
  | succ m ih =>
    rw [← universalNodeDesc_comp K m f hf, CommRingCat.ofHom_comp, Spec.map_comp]
    simp only [Category.assoc, universalNodeRestriction_chart_assoc,
      completeIdentityFiniteRestriction_scaling_assoc,
      completeIdentityFiniteRestriction_input_assoc]
    exact ih (universalNodeDesc K m f hf) (universalNodeDesc_parameter K m f hf)

end FLT.Mazur.PolygonInfinitesimalStages
