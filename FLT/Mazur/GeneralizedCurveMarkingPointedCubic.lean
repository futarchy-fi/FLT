/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingMarkingRatios
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# The cubic factorization preserves the original marking

The actual Y-chart ratios give the infinity evaluation on its whole projective
coordinate ring. The mono cubic embedding then upgrades that calculation to
the pointed identity for the original global integral-cubic morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingPointedCubicProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := E.curve.left) (U)

attribute [local instance] MvPolynomial.gradedAlgebra
local notation "m" => smoothMarkingMarkingY E s e

/-- Along the marking the complete projective chart evaluation is the infinity evaluation. -/
theorem smoothMarkingMarkingY_chartRingMap :
    (m).appTop.hom.comp ((B).inv.hom.comp
      (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 1 (U) le_rfl
        (sectionChartScalars E.curve.hom.appTop.hom (U)))) =
    (chartInfinityEvaluation (S := Γ(S, ⊤)) (W)).toRingHom.comp
      (projectiveChartAlgebra (W) 1).toRingHom := by
  apply ProjectiveSpace.chartRing_hom_ext Γ(S, ⊤) (Fin 3) 1
  · intro a
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_scalar]
    erw [(projectiveChartAlgebra (W) 1).commutes,
      (chartInfinityEvaluation (S := Γ(S, ⊤)) (W)).commutes]
    exact smoothMarkingMarkingY_scalar E s e a
  · intro i
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_coordinate,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, projectiveChartAlgebra_coordinate,
      chartInfinityEvaluation_coord]
    exact smoothMarkingMarkingY_ratio E s e i

/-- The original marked section is sent to the actual integral zero section. -/
@[reassoc] theorem smoothMarkingToIntegralCubic_marking :
    (t).left ≫ smoothMarkingToIntegralCubic E s e =
      S.toSpecΓ ≫ integralCurveZero (W) := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  rw [Category.assoc, smoothMarkingToIntegralCubic_projective]
  rw [← smoothMarkingMarkingY_ι E s e, Category.assoc,
    smoothMarkingToProjectiveSpace, sectionGeneratorOpen_ι_projectiveMorphism]
  simp only [sectionProjectiveLocalMorphism, sectionProjectiveChartMorphism,
    integralCurveZero, Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap, projectiveChartMorphism]
  rw [← Category.assoc (m) (U).toScheme.toSpecΓ,
    Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, ← Spec.map_comp_assoc]
  change S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((m).appTop.hom.comp ((B).inv.hom.comp
      (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 1 (U) le_rfl
        (sectionChartScalars E.curve.hom.appTop.hom (U)))))) ≫ _ = _
  rw [smoothMarkingMarkingY_chartRingMap]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
