/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstUniversalNodeReduction
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoherence
public import FLT.Mazur.PolygonCompleteIdentityOrderZeroLaw

/-!
# The actual first source cubic action on its full parameter-zero chart

The constructed full chart restriction and finite-stage coherence transport
the proved order-zero action law to the original first-stage input. The
factorization criterion retains arbitrary nilpotents in the receiving ring.
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
local notation "r" => firstUniversalNodeRestriction K
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

omit [NeZero n] in
/-- The literal parameter-zero node restriction is the original finite input restriction. -/
@[reassoc] theorem firstUniversalNodeRestriction_chart :
    Spec.map (CommRingCat.ofHom (r)) ≫ (d 1) =
      (d 0) ≫ completeIdentityFiniteRestriction K n h 0 := by
  rw [completeIdentityFiniteRestriction, scalingParameterMap, chart_parameterProjection]
  rfl

/-- The two actual first-stage cubic maps agree on the entire parameter-zero node chart. -/
theorem completeIdentityFirstSourceZero_cubic :
    Spec.map (CommRingCat.ofHom (r)) ≫ (d 1) ≫
        completeIdentityFiniteScaling K n h 1 ≫ (g) =
      Spec.map (CommRingCat.ofHom (r)) ≫ (d 1) ≫
        completeIdentityFiniteInput K n h 0 1 ≫ (a) := by
  rw [firstUniversalNodeRestriction_chart_assoc, firstUniversalNodeRestriction_chart_assoc,
    completeIdentityFiniteRestriction_scaling_assoc, completeIdentityFiniteRestriction_input_assoc,
    completeIdentityFiniteComparison_zero]

/-- Every source map killing the actual parameter inherits that same whole-node cubic equality. -/
theorem completeIdentityFirstSource_cubic_of_parameter_zero
    {T : Type} [CommRing T] (f : ChartRing (C (parameter K 1)) →+* T)
    (hf : f (algebraMap (Ring K 1)[T;T⁻¹]
      (ChartRing (C (parameter K 1))) (C (parameter K 1))) = 0) :
    Spec.map (CommRingCat.ofHom f) ≫ (d 1) ≫
        completeIdentityFiniteScaling K n h 1 ≫ (g) =
      Spec.map (CommRingCat.ofHom f) ≫ (d 1) ≫
        completeIdentityFiniteInput K n h 0 1 ≫ (a) := by
  have he := congrArg (fun z ↦ Spec.map (CommRingCat.ofHom
    (firstUniversalNodeDesc K f hf)) ≫ z) (completeIdentityFirstSourceZero_cubic K n h j)
  simpa only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    firstUniversalNodeDesc_comp] using he

end FLT.Mazur.PolygonInfinitesimalStages
