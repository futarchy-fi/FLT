/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAmbientParameterComparison

/-!
# The actual first ambient coordinate errors satisfy the smoothing relation

The original cubic equality forces the two original node coefficient maps
to agree. Consequently target-minus-scaled-source errors satisfy the exact
quadratic smoothing identity. This does not assert that either error vanishes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1
local notation "s" => completeIdentityAdicAmbientStructure K n h 1 0 0
local notation "q" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "p" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)
local notation "D" => completeIdentityFirstAmbientError K n h

/-- The full cubic relation retains the same truncated coefficients on its target node. -/
@[reassoc] theorem completeIdentityFirstAmbientTarget_structure :
    (pullback.snd _ _ : (R) ⟶ PolygonSmoothing.chart (A) (t)) ≫
      chartStructure (A) (t) = (s) := by
  apply (cancel_mono (baseToSeries K 1)).mp
  have he := completeIdentityAdicAmbientStructure_complete K n h 1 0 0
  rw [← completeIdentityActionLiftSpace_target_structure] at he
  rw [Category.assoc, completeIdentityActionAdicLiftSpaceMap, pullback.lift_snd_assoc,
    Category.assoc, completeIdentityActionAdicChartSpaceMap_snd_assoc,
    originalStageToCompatibleProj_toBase] at he
  change (pullback.snd _ _ ≫ PolygonInfinitesimal.chart (A) (t) n h 0) ≫
    toBase (A) (t) n h ≫ baseToSeries K 1 = _ at he
  rw [Category.assoc, chart_toBase_assoc] at he
  simpa only [Category.assoc] using he

/-- Every original target scalar agrees with the source coefficient map. -/
theorem completeIdentityFirstAmbientTarget_scalar (r : A) :
    (q) (algebraMap (A) (ChartRing (t)) r) =
      (s).appTop ((Scheme.ΓSpecIso (.of (A))).inv r) := by
  have he := congrArg Scheme.Hom.appTop
    (completeIdentityFirstAmbientTarget_structure K n h)
  have hh := congrArg (fun f ↦ ((Scheme.ΓSpecIso (.of (A))).inv ≫ f) r) he
  have hn : (Scheme.ΓSpecIso (.of (A))).inv ≫ (chartStructure (A) (t)).appTop =
      CommRingCat.ofHom (algebraMap (A) (ChartRing (t))) ≫
        (Scheme.ΓSpecIso (.of (ChartRing (t)))).inv :=
    (Scheme.ΓSpecIso_inv_naturality _).symm
  rw [Scheme.Hom.comp_appTop] at hh
  rw [← Category.assoc (Scheme.ΓSpecIso (.of (A))).inv
    (chartStructure (A) (t)).appTop, hn] at hh
  exact hh

/-- Source and target have the same smoothing parameter before imposing the graph ideal. -/
theorem completeIdentityFirstAmbientTarget_xy :
    (q) (x) * (q) (y) = completeIdentityFirstAmbientParameter K n h := by
  rw [← map_mul, coordinate_relation, completeIdentityFirstAmbientTarget_scalar,
    ← completeIdentityFirstAmbientSource_scalar, stageCoefficientMap_parameter]
  rfl

/-- Reciprocal scaling preserves the actual ambient smoothing parameter. -/
theorem completeIdentityFirstAmbientScaledSource_xy :
    (p) ((σ) ((b) (x))) * (p) ((σ) ((b) (y))) =
      completeIdentityFirstAmbientParameter K n h := by
  rw [← map_mul, ← map_mul, ← map_mul, coordinate_relation, ringMap_scalar,
    AlgHom.commutes, stageCoefficientMap_parameter]
  rfl

/-- The actual original coordinate errors satisfy the full quadratic smoothing equation. -/
theorem completeIdentityFirstAmbientError_smoothing :
    (p) ((σ) ((b) (x))) * (D) (y) + (p) ((σ) ((b) (y))) * (D) (x) +
      (D) (x) * (D) (y) = 0 := by
  have ht := completeIdentityFirstAmbientTarget_xy K n h
  have hs := completeIdentityFirstAmbientScaledSource_xy K n h
  unfold completeIdentityFirstAmbientError
  calc
    _ = (q) (x) * (q) (y) - (p) ((σ) ((b) (x))) * (p) ((σ) ((b) (y))) := by ring
    _ = 0 := by rw [ht, hs, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages
