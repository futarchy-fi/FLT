/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicFactorization
public import FLT.Mazur.DivisorComplementSectionRatios
public import FLT.Mazur.ModuleSectionProjectiveTransition
public import FLT.Mazur.PolygonCompletePointRelativeAffineMorphism
public import FLT.Mazur.WeierstrassAffineMonicComparison

/-!
# The global complete-base cubic map retains the original affine evaluation
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "e" => completePointSectionFrame K n h i

local notation "L" => completePointLine K n h i
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" => GlobalIdealPowerCompatibility.complement (Scheme.Hom.ker (s))
local notation "u" => Scheme.Opens.ι (X := exactVeroneseProj K n h) (U)
local notation "B" => Scheme.Opens.topIso (X := exactVeroneseProj K n h) (U)
local notation "φ" => completePointComplementBaseMap K n h i
local notation "E" => completePointCoordinateEvaluation K n h i

/-- The original complement is contained in the third generator chart. -/
theorem completePointComplement_le_zGenerator :
    (U) ≤ sectionGeneratorOpen (tensorPower (L) 3) (T 2) :=
  divisorComplement_le_powerGenerator hI 3 (by decide)

/-- The normalized projective coordinates retain the actual original affine functions. -/
theorem completePointComplement_projectiveRatios (j : Fin 3) :
    (B).inv (sectionRatioOn (tensorPower (L) 3) (T 2) (U)
      (completePointComplement_le_zGenerator K n h i) (T j)) =
      ![completePointComplementX K n h i,
        completePointComplementY K n h i, 1] j := by
  erw [← divisorComplementFunction_eq_ratio hI 3 (by decide) (T j)]
  fin_cases j
  · exact completePointProjectiveX_function K n h i
  · exact completePointProjectiveY_function K n h i
  · exact completePointProjectiveZ_function K n h i

/-- The scalar restriction in the projective chart is the original complement base map. -/
theorem completePointComplement_chartScalars :
    (B).inv.hom.comp (sectionChartScalars (f).appTop.hom (U)) = φ := by
  ext a
  unfold completePointComplementBaseMap sectionChartScalars
  simp only [RingHom.comp_apply, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The affine evaluation and normalized projective evaluation agree on the whole chart ring. -/
theorem completePointComplement_chartRingMap :
    ((E).comp (affineChartToMonic (W)).toRingHom).comp
      (projectiveChartAlgebra (W) 2).toRingHom =
    (B).inv.hom.comp (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 2 (U)
      (completePointComplement_le_zGenerator K n h i)
      (sectionChartScalars (f).appTop.hom (U))) := by
  apply ProjectiveSpace.chartRing_hom_ext Γ(S, ⊤) (Fin 3) 2
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      sectionProjectiveChartRingMap_scalar]
    erw [(projectiveChartAlgebra (W) 2).commutes, (affineChartToMonic (W)).commutes,
      completePointCoordinateEvaluation_scalar]
    exact (congrArg (fun b : Γ(S, ⊤) →+* _ => b a)
      (completePointComplement_chartScalars K n h i)).symm
  · intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      projectiveChartAlgebra_coordinate, sectionProjectiveChartRingMap_coordinate,
      completePointComplement_projectiveRatios, affineChartToMonic, evaluation_coord]
    fin_cases j
    · exact completePointCoordinateEvaluation_x K n h i
    · exact completePointCoordinateEvaluation_y K n h i
    · exact map_one (E)

/-- The global integral-cubic map restricts to the actual original affine evaluation. -/
theorem completePointToIntegralCubic_affine :
    (u) ≫ completePointToIntegralCubic K n h i =
      completePointToAffineCubic K n h i ≫
        Spec.map (CommRingCat.ofHom (affineChartToMonic (W)).toRingHom) ≫
          integralCurveChart (W) 2 := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  simp only [Category.assoc, completePointToIntegralCubic_projective,
    integralCurveChart_projectiveMap]
  rw [completePointToProjectiveSpace, sectionProjectiveMorphism_onOpen
    (tensorPower (L) 3) 2 (T) (completePointProjectiveSections_cover K n h i)
    (f).appTop.hom 2 (U) (completePointComplement_le_zGenerator K n h i)]
  simp only [sectionProjectiveChartMorphism, completePointToAffineCubic,
    projectiveChartMap, projectiveChartMorphism, Category.assoc,
    ← Spec.map_comp_assoc]
  change _ = _ ≫ Spec.map (CommRingCat.ofHom
    (((E).comp (affineChartToMonic (W)).toRingHom).comp
      (projectiveChartAlgebra (W) 2).toRingHom)) ≫ _
  rw [completePointComplement_chartRingMap]


end FLT.Mazur.PolygonInfinitesimalStages
