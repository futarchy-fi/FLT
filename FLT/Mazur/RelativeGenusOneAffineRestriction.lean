/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCubicFactorization
public import FLT.Mazur.DivisorComplementSectionRatios
public import FLT.Mazur.ModuleSectionProjectiveTransition
public import FLT.Mazur.RelativeGenusOneAffineIso
public import FLT.Mazur.WeierstrassAffineMonicComparison

/-!
# The global cubic factorization retains the original affine isomorphism

On the original point complement the normalized projective ratios are the
original affine functions. The global map therefore restricts to the already
constructed affine isomorphism, with its explicit monic-chart comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
local notation "U" => (s.left.ker.support.compl : G.left.Opens)
local notation "u" => Scheme.Opens.ι (X := G.left) (U)
local notation "B" => Scheme.Opens.topIso (X := G.left) (U)
local notation "φ" => relativePointComplementBaseMap G s
local notation "E" => relativePointCoordinateEvaluation G hg s hI e

/-- The original complement is contained in the third generator chart. -/
theorem relativePointComplement_le_zGenerator :
    (U) ≤ sectionGeneratorOpen (tensorPower (L) 3) (T 2) :=
  divisorComplement_le_powerGenerator hI 3 (by decide)

/-- The normalized projective coordinates retain the actual original affine functions. -/
theorem relativePointComplement_projectiveRatios (i : Fin 3) :
    (B).inv (sectionRatioOn (tensorPower (L) 3) (T 2) (U)
      (relativePointComplement_le_zGenerator G hg s hI e) (T i)) =
      ![relativePointComplementX G hg s hI e,
        relativePointComplementY G hg s hI e, 1] i := by
  erw [← divisorComplementFunction_eq_ratio hI 3 (by decide) (T i)]
  fin_cases i
  · exact relativePointProjectiveX_function G hg s hI e
  · exact relativePointProjectiveY_function G hg s hI e
  · exact relativePointProjectiveZ_function G s hI

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom] in
/-- The scalar restriction in the projective chart is the original complement base map. -/
theorem relativePointComplement_chartScalars :
    (B).inv.hom.comp (sectionChartScalars G.hom.appTop.hom (U)) = φ := by
  ext a
  unfold relativePointComplementBaseMap sectionChartScalars
  simp only [RingHom.comp_apply, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The affine evaluation and normalized projective evaluation agree on the whole chart ring. -/
theorem relativePointComplement_chartRingMap :
    ((E).comp (affineChartToMonic (W)).toRingHom).comp
      (projectiveChartAlgebra (W) 2).toRingHom =
    (B).inv.hom.comp (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 2 (U)
      (relativePointComplement_le_zGenerator G hg s hI e)
      (sectionChartScalars G.hom.appTop.hom (U))) := by
  apply ProjectiveSpace.chartRing_hom_ext Γ(S, ⊤) (Fin 3) 2
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      sectionProjectiveChartRingMap_scalar]
    erw [(projectiveChartAlgebra (W) 2).commutes, (affineChartToMonic (W)).commutes,
      relativePointCoordinateEvaluation_scalar]
    exact (congrArg (fun f : Γ(S, ⊤) →+* _ => f a)
      (relativePointComplement_chartScalars G s)).symm
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      projectiveChartAlgebra_coordinate, sectionProjectiveChartRingMap_coordinate,
      relativePointComplement_projectiveRatios, affineChartToMonic, evaluation_coord]
    fin_cases i
    · exact relativePointCoordinateEvaluation_x G hg s hI e
    · exact relativePointCoordinateEvaluation_y G hg s hI e
    · exact map_one (E)

/-- The global integral-cubic map restricts to the actual original affine isomorphism. -/
theorem relativePointToIntegralCubic_affine :
    (u) ≫ relativePointToIntegralCubic G hg s hI e =
      relativePointToAffineCubic G hg s hI e ≫
        Spec.map (CommRingCat.ofHom (affineChartToMonic (W)).toRingHom) ≫
          integralCurveChart (W) 2 := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  simp only [Category.assoc, relativePointToIntegralCubic_projective,
    integralCurveChart_projectiveMap]
  rw [relativePointToProjectiveSpace, sectionProjectiveMorphism_onOpen
    (tensorPower (L) 3) 2 (T) (relativePointProjectiveSections_cover G hg s hI e)
    G.hom.appTop.hom 2 (U) (relativePointComplement_le_zGenerator G hg s hI e)]
  simp only [sectionProjectiveChartMorphism, relativePointToAffineCubic,
    projectiveChartMap, projectiveChartMorphism, Category.assoc,
    ← Spec.map_comp_assoc]
  change _ = _ ≫ Spec.map (CommRingCat.ofHom
    (((E).comp (affineChartToMonic (W)).toRingHom).comp
      (projectiveChartAlgebra (W) 2).toRingHom)) ≫ _
  rw [relativePointComplement_chartRingMap]

end FLT.Mazur.FCurve
