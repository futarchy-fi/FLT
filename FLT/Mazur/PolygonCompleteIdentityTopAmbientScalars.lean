/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientStructure
public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientTarget

/-!
# Original source and target coefficients on the higher ambient relation

This comparison uses the actual coefficient diagram of the full relation,
with its original source and target maps before imposing the graph ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  completeIdentityActionLiftSpaceStructure completeIdentityTopActionUnit
  completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h (m + 1) 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h (m + 1)
local notation "s" => completeIdentityAdicAmbientStructure K n h (m + 1) 0 0
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "B" => ChartRing (parameter K[T;T⁻¹] (m + 1))
local notation "q" => Scheme.ΓSpecIso (CommRingCat.of (Ring K (m + 1)))

/-- Moving the Laurent unit preserves the same original ambient coefficients. -/
@[reassoc] theorem completeIdentityTopAmbientSource_structure :
    (pullback.fst _ _ ≫ (stageNodeParameterIso K (m + 1)).inv :
      completeIdentityActionAdicChartSpace K n h (m + 1) 0 0 ⟶ _) ≫
        chartStructure (Ring K[T;T⁻¹] (m + 1)) (parameter K[T;T⁻¹] (m + 1)) ≫
          Spec.map (CommRingCat.ofHom
            (stageCoefficientMap (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (m + 1))) =
      completeIdentityAdicAmbientStructure K n h (m + 1) 0 0 := by
  rw [Category.assoc, stageNodeParameterIso_inv_structure]
  rfl

/-- The actual source-node coefficient functions agree before imposing any graph equations. -/
theorem completeIdentityTopAmbientSource_scalar (r : Ring K (m + 1)) :
    completeIdentityTopAmbientSourceFunctions K n h m
      (algebraMap (Ring K[T;T⁻¹] (m + 1)) (B) ((c) r)) = (s).appTop ((q).inv r) := by
  have he := congrArg Scheme.Hom.appTop
    (completeIdentityTopAmbientSource_structure K n h m)
  have hn : (q).inv ≫ (Spec.map (CommRingCat.ofHom (c))).appTop ≫
      (chartStructure (Ring K[T;T⁻¹] (m + 1)) (parameter K[T;T⁻¹] (m + 1))).appTop =
      CommRingCat.ofHom ((algebraMap (Ring K[T;T⁻¹] (m + 1)) (B)).comp (c)) ≫
        (Scheme.ΓSpecIso (.of (B))).inv := by
    change _ ≫ _ ≫ (Spec.map _).appTop = _
    simp only [← Scheme.Hom.comp_appTop, ← Spec.map_comp,
      Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hh := congrArg (fun f : Γ(Spec (.of (Ring K (m + 1))), ⊤) ⟶ Γ((R), ⊤) ↦
    ((q).inv ≫ f) r) he
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ← Category.assoc, hn] at hh
  exact hh

/-- The full cubic relation retains the same truncated coefficients on its target node. -/
@[reassoc] theorem completeIdentityTopAmbientTarget_structure :
    (pullback.snd _ _ : (R) ⟶ PolygonSmoothing.chart (A) (t)) ≫
      chartStructure (A) (t) = (s) := by
  apply (cancel_mono (baseToSeries K (m + 1))).mp
  have he := completeIdentityAdicAmbientStructure_complete K n h (m + 1) 0 0
  rw [← completeIdentityActionLiftSpace_target_structure] at he
  rw [Category.assoc, completeIdentityActionAdicLiftSpaceMap, pullback.lift_snd_assoc,
    Category.assoc, completeIdentityActionAdicChartSpaceMap_snd_assoc,
    originalStageToCompatibleProj_toBase] at he
  change (pullback.snd _ _ ≫ PolygonInfinitesimal.chart (A) (t) n h 0) ≫
    toBase (A) (t) n h ≫ baseToSeries K (m + 1) = _ at he
  rw [Category.assoc, chart_toBase_assoc] at he
  simpa only [Category.assoc] using he

/-- Every original target scalar agrees with the source coefficient map. -/
theorem completeIdentityTopAmbientTarget_scalar (r : A) :
    (completeIdentityTopAmbientTargetFunctions K n h m) (algebraMap (A) (ChartRing (t)) r) =
      (s).appTop ((Scheme.ΓSpecIso (.of (A))).inv r) := by
  have he := congrArg Scheme.Hom.appTop
    (completeIdentityTopAmbientTarget_structure K n h m)
  have hh := congrArg (fun f ↦ ((Scheme.ΓSpecIso (.of (A))).inv ≫ f) r) he
  have hn : (Scheme.ΓSpecIso (.of (A))).inv ≫ (chartStructure (A) (t)).appTop =
      CommRingCat.ofHom (algebraMap (A) (ChartRing (t))) ≫
        (Scheme.ΓSpecIso (.of (ChartRing (t)))).inv :=
    (Scheme.ΓSpecIso_inv_naturality _).symm
  rw [Scheme.Hom.comp_appTop] at hh
  rw [← Category.assoc (Scheme.ΓSpecIso (.of (A))).inv
    (chartStructure (A) (t)).appTop, hn] at hh
  exact hh

end FLT.Mazur.PolygonInfinitesimalStages
