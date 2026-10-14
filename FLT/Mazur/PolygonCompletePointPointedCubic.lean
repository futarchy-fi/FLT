/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointMarkingRatios
public import FLT.Mazur.WeierstrassIntegralZeroSection
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# The complete-base cubic factorization preserves the original marking

The original marking maps to the integral zero section under the constructed cubic morphism.
The morphism is proper over the original coefficient spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "e" => completePointSectionFrame K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
open WeierstrassIntegralChart

local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := (exactVeroneseProj K n h)) (U)

attribute [local instance] MvPolynomial.gradedAlgebra
local notation "m" => completePointMarkingY K n h i

/-- Along the marking the complete projective chart evaluation is the infinity evaluation. -/
theorem completePointMarkingY_chartRingMap :
    (m).appTop.hom.comp ((B).inv.hom.comp
      (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 1 (U) le_rfl
        (sectionChartScalars (f).appTop.hom (U)))) =
    (chartInfinityEvaluation (S := Γ(S₀, ⊤)) (W)).toRingHom.comp
      (projectiveChartAlgebra (W) 1).toRingHom := by
  apply ProjectiveSpace.chartRing_hom_ext Γ(S₀, ⊤) (Fin 3) 1
  · intro a
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_scalar]
    erw [(projectiveChartAlgebra (W) 1).commutes,
      (chartInfinityEvaluation (S := Γ(S₀, ⊤)) (W)).commutes]
    exact completePointMarkingY_scalar K n h i a
  · intro j
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_coordinate,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, projectiveChartAlgebra_coordinate,
      chartInfinityEvaluation_coord]
    exact completePointMarkingY_ratio K n h i j

/-- The original marked section is sent to the actual integral zero section. -/
@[reassoc] theorem completePointToIntegralCubic_marking :
    (s) ≫ completePointToIntegralCubic K n h i =
      (S₀).toSpecΓ ≫ integralCurveZero (W) := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  rw [Category.assoc, completePointToIntegralCubic_projective]
  rw [← completePointMarkingY_ι K n h i, Category.assoc, completePointToProjectiveSpace]
  change (m) ≫ (U).ι ≫ sectionProjectiveMorphism (tensorPower (L) 3) 2 (T)
    (completePointProjectiveSections_cover K n h i) (f).appTop.hom = _
  rw [sectionGeneratorOpen_ι_projectiveMorphism (tensorPower (L) 3) 2 (T)
    (completePointProjectiveSections_cover K n h i) (f).appTop.hom 1]
  simp only [sectionProjectiveLocalMorphism, sectionProjectiveChartMorphism,
    integralCurveZero, Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap, projectiveChartMorphism]
  rw [← Category.assoc (m) (U).toScheme.toSpecΓ,
    Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, ← Spec.map_comp_assoc]
  change (S₀).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((m).appTop.hom.comp ((B).inv.hom.comp
      (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 1 (U) le_rfl
        (sectionChartScalars (f).appTop.hom (U)))))) ≫ _ = _
  rw [completePointMarkingY_chartRingMap]
  rfl

/-- The original cubic morphism is proper over the actual coefficient spectrum. -/
theorem completePointToIntegralCubic_proper :
    IsProper (completePointToIntegralCubic K n h i) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  have hp : IsProper (completePointToIntegralCubic K n h i ≫ integralCurveStructure (W)) := by
    rw [completePointToIntegralCubic_over]
    infer_instance
  exact IsProper.of_comp (completePointToIntegralCubic K n h i) (integralCurveStructure (W))

end FLT.Mazur.PolygonInfinitesimalStages
