/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneMarkingRatios
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# The cubic factorization preserves the original marking

The actual Y-chart ratios give the infinity evaluation on its whole projective
coordinate ring. The mono cubic embedding then upgrades that calculation to
the pointed identity for the original global integral-cubic morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
open WeierstrassIntegralChart

local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := G.left) (U)

attribute [local instance] MvPolynomial.gradedAlgebra
local notation "m" => relativePointMarkingY G hg s hI e

/-- Along the marking the complete projective chart evaluation is the infinity evaluation. -/
theorem relativePointMarkingY_chartRingMap :
    (m).appTop.hom.comp ((B).inv.hom.comp
      (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 1 (U) le_rfl
        (sectionChartScalars G.hom.appTop.hom (U)))) =
    (chartInfinityEvaluation (S := Γ(S, ⊤)) (W)).toRingHom.comp
      (projectiveChartAlgebra (W) 1).toRingHom := by
  apply ProjectiveSpace.chartRing_hom_ext Γ(S, ⊤) (Fin 3) 1
  · intro a
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_scalar]
    erw [(projectiveChartAlgebra (W) 1).commutes,
      (chartInfinityEvaluation (S := Γ(S, ⊤)) (W)).commutes]
    exact relativePointMarkingY_scalar G hg s hI e a
  · intro i
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_coordinate,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, projectiveChartAlgebra_coordinate,
      chartInfinityEvaluation_coord]
    exact relativePointMarkingY_ratio G hg s hI e i

/-- The original marked section is sent to the actual integral zero section. -/
@[reassoc] theorem relativePointToIntegralCubic_marking :
    s.left ≫ relativePointToIntegralCubic G hg s hI e =
      S.toSpecΓ ≫ integralCurveZero (W) := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  rw [Category.assoc, relativePointToIntegralCubic_projective]
  rw [← relativePointMarkingY_ι G hg s hI e, Category.assoc,
    relativePointToProjectiveSpace, sectionGeneratorOpen_ι_projectiveMorphism]
  simp only [sectionProjectiveLocalMorphism, sectionProjectiveChartMorphism,
    integralCurveZero, Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap, projectiveChartMorphism]
  rw [← Category.assoc (m) (U).toScheme.toSpecΓ,
    Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, ← Spec.map_comp_assoc]
  change S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((m).appTop.hom.comp ((B).inv.hom.comp
      (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 1 (U) le_rfl
        (sectionChartScalars G.hom.appTop.hom (U)))))) ≫ _ = _
  rw [relativePointMarkingY_chartRingMap]
  rfl

end FLT.Mazur.FCurve
