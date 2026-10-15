/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientStructure
public import FLT.Mazur.PolygonCompleteIdentityFirstCompleteEquations

/-!
# The complete parameter specializes to the original ambient parameter

This comparison uses the actual coefficient diagram of the full relation,
not its closed graph. It removes the ambiguity in a chosen parameter lift.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityActionLiftSpaceStructure completeIdentityFirstActionUnit
  completeIdentityFirstActionField completeIdentityFirstActionNodeDefect
  completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1
local notation "s" => completeIdentityAdicAmbientStructure K n h 1 0 0
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "B" => ChartRing (parameter K[T;T⁻¹] 1)
local notation "q" => Scheme.ΓSpecIso (CommRingCat.of (Ring K 1))

/-- The actual source-node coefficient functions agree before imposing any graph equations. -/
theorem completeIdentityFirstAmbientSource_scalar (r : Ring K 1) :
    completeIdentityFirstAmbientSourceFunctions K n h
      (algebraMap (Ring K[T;T⁻¹] 1) (B) ((c) r)) = (s).appTop ((q).inv r) := by
  have he := congrArg Scheme.Hom.appTop
    (completeIdentityFirstAmbientSource_structure K n h)
  have hn : (q).inv ≫ (Spec.map (CommRingCat.ofHom (c))).appTop ≫
      (chartStructure (Ring K[T;T⁻¹] 1) (parameter K[T;T⁻¹] 1)).appTop =
      CommRingCat.ofHom ((algebraMap (Ring K[T;T⁻¹] 1) (B)).comp (c)) ≫
        (Scheme.ΓSpecIso (.of (B))).inv := by
    change _ ≫ _ ≫ (Spec.map _).appTop = _
    simp only [← Scheme.Hom.comp_appTop, ← Spec.map_comp,
      Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hh := congrArg (fun f : Γ(Spec (.of (Ring K 1)), ⊤) ⟶ Γ((R), ⊤) ↦
    ((q).inv ≫ f) r) he
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ← Category.assoc, hn] at hh
  exact hh

/-- The complete global parameter pulls back to the literal original ambient parameter. -/
theorem completeIdentityActionAmbientParameter_pullback :
    (k).appTop (completeIdentityActionAmbientParameter K n h) =
      completeIdentityFirstAmbientParameter K n h := by
  change ((completeIdentityActionLiftSpaceStructure K n h).appTop ≫ (k).appTop)
    ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv PowerSeries.X) = _
  rw [← Scheme.Hom.comp_appTop, completeIdentityAdicAmbientStructure_complete,
    Scheme.Hom.comp_appTop]
  have he := congrArg (fun f ↦ f PowerSeries.X)
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (seriesToStage K 1).toRingHom)).symm
  change (baseToSeries K 1).appTop
      ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv PowerSeries.X) =
    (q).inv (seriesToStage K 1 PowerSeries.X) at he
  rw [CommRingCat.comp_apply, he, seriesToStage_X,
    ← completeIdentityFirstAmbientSource_scalar, stageCoefficientMap_parameter]
  rfl

variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "t" => completeIdentityActionAmbientParameter K n h

/-- The original complete parameter has its prescribed value on every transported affine patch. -/
theorem completeIdentityActionAmbientParameter_patch :
    (p) (AffinePrincipalKernel.restriction (W) (t)) =
      (ρ) (completeIdentityFirstAmbientParameter K n h) := by
  change ((AffinePrincipalKernel.restriction (W)) ≫ (p)) (t) = _
  rw [Scheme.Hom.map_appLE]
  rw [← completeIdentityActionAmbientParameter_pullback K n h]
  change _ = ((k).appTop ≫ (ρ)) (t)
  have ht : (k).appLE ⊤ ⊤ (by simp) = (k).appTop := (k).appLE_eq_app
  rw [← ht, Scheme.Hom.appLE_map]

end FLT.Mazur.PolygonInfinitesimalStages
