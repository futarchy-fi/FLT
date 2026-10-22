/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicFactorization
public import FLT.Mazur.DivisorComplementSectionRatios
public import FLT.Mazur.ModuleSectionProjectiveTransition
public import FLT.Mazur.GeneralizedCurveMarkingAffineCubicMorphism
public import FLT.Mazur.WeierstrassAffineMonicComparison

/-!
# The global cubic factorization retains the original affine morphism

On the original point complement the normalized projective ratios are the
original affine functions. The global map therefore restricts to the already
constructed affine morphism, with its explicit monic-chart comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingAffineRestrictionProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (t)))) : E.curve.left.Opens)
local notation "u" => Scheme.Opens.ι (X := E.curve.left) (U)
local notation "B" => Scheme.Opens.topIso (X := E.curve.left) (U)
local notation "φ" => smoothMarkingComplementBaseMap E s
local notation "Q" => smoothMarkingCoordinateEvaluation E s e

/-- The original complement is contained in the third generator chart. -/
theorem smoothMarkingComplement_le_zGenerator :
    (U) ≤ sectionGeneratorOpen (tensorPower (L) 3) (T 2) :=
  divisorComplement_le_powerGenerator (hI) 3 (by decide)

/-- The normalized projective coordinates retain the actual original affine functions. -/
theorem smoothMarkingComplement_projectiveRatios (i : Fin 3) :
    (B).inv (sectionRatioOn (tensorPower (L) 3) (T 2) (U)
      (smoothMarkingComplement_le_zGenerator E s e) (T i)) =
      ![smoothMarkingComplementX E s e,
        smoothMarkingComplementY E s e, 1] i := by
  erw [← divisorComplementFunction_eq_ratio (hI) 3 (by decide) (T i)]
  fin_cases i
  · exact smoothMarkingProjectiveX_function E s e
  · exact smoothMarkingProjectiveY_function E s e
  · exact smoothMarkingProjectiveZ_function E s

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
/-- The scalar restriction in the projective chart is the original complement base map. -/
theorem smoothMarkingComplement_chartScalars :
    (B).inv.hom.comp (sectionChartScalars E.curve.hom.appTop.hom (U)) = φ := by
  ext a
  unfold smoothMarkingComplementBaseMap sectionChartScalars
  simp only [RingHom.comp_apply, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The affine evaluation and normalized projective evaluation agree on the whole chart ring. -/
theorem smoothMarkingComplement_chartRingMap :
    ((Q).comp (affineChartToMonic (W)).toRingHom).comp
      (projectiveChartAlgebra (W) 2).toRingHom =
    (B).inv.hom.comp (sectionProjectiveChartRingMap (tensorPower (L) 3) 2 (T) 2 (U)
      (smoothMarkingComplement_le_zGenerator E s e)
      (sectionChartScalars E.curve.hom.appTop.hom (U))) := by
  apply ProjectiveSpace.chartRing_hom_ext Γ(S, ⊤) (Fin 3) 2
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      sectionProjectiveChartRingMap_scalar]
    erw [(projectiveChartAlgebra (W) 2).commutes, (affineChartToMonic (W)).commutes,
      smoothMarkingCoordinateEvaluation_scalar]
    exact (congrArg (fun f : Γ(S, ⊤) →+* _ => f a)
      (smoothMarkingComplement_chartScalars E s)).symm
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      projectiveChartAlgebra_coordinate, sectionProjectiveChartRingMap_coordinate,
      smoothMarkingComplement_projectiveRatios, affineChartToMonic, evaluation_coord]
    fin_cases i
    · exact smoothMarkingCoordinateEvaluation_x E s e
    · exact smoothMarkingCoordinateEvaluation_y E s e
    · exact map_one (Q)

/-- The global integral-cubic map restricts to the actual original affine morphism. -/
theorem smoothMarkingToIntegralCubic_affine :
    (u) ≫ smoothMarkingToIntegralCubic E s e =
      smoothMarkingToAffineCubic E s e ≫
        Spec.map (CommRingCat.ofHom (affineChartToMonic (W)).toRingHom) ≫
          integralCurveChart (W) 2 := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  simp only [Category.assoc, smoothMarkingToIntegralCubic_projective,
    integralCurveChart_projectiveMap]
  rw [smoothMarkingToProjectiveSpace, sectionProjectiveMorphism_onOpen
    (tensorPower (L) 3) 2 (T) (smoothMarkingProjectiveSections_cover E s e)
    E.curve.hom.appTop.hom 2 (U) (smoothMarkingComplement_le_zGenerator E s e)]
  simp only [sectionProjectiveChartMorphism, smoothMarkingToAffineCubic,
    projectiveChartMap, projectiveChartMorphism, Category.assoc,
    ← Spec.map_comp_assoc]
  change _ = _ ≫ Spec.map (CommRingCat.ofHom
    (((Q).comp (affineChartToMonic (W)).toRingHom).comp
      (projectiveChartAlgebra (W) 2).toRingHom)) ≫ _
  rw [smoothMarkingComplement_chartRingMap]

end FLT.Mazur.GeneralizedEllipticCurve
