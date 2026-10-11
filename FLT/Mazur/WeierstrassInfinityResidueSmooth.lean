/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueGeometry
public import FLT.Mazur.WeierstrassSplitNodalRelativeSmooth
public import FLT.Mazur.WeierstrassIntegralCoefficientMap

/-!
# The full smooth locus of the original positive-depth residue cubic

The retained Laurent coordinate identifies the entire original smooth
cubic, and the comparison preserves its actual integral coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Equation equality transports the full smooth torus, with its original target scheme. -/
def splitEquationSmoothIso {K : Type u} [CommRing K] {U : WeierstrassCurve K}
    (a : Kˣ) (h : U = splitNodalEquation a) :
    Spec (.of K[T;T⁻¹]) ≅ (integralSmoothOpen U).toScheme := by
  subst U
  exact splitNodalRelativeSmoothIso a

/-- Transport of the smooth comparison retains every original chart coordinate. -/
@[reassoc] theorem splitEquationSmoothIso_inclusion
    {K : Type u} [CommRing K] {U : WeierstrassCurve K}
    (a : Kˣ) (h : U = splitNodalEquation a) :
    (splitEquationSmoothIso a h).hom ≫ (integralSmoothOpen U).ι =
      Spec.map (CommRingCat.ofHom (((equationChartEquiv h 1).trans
        (splitNodalChartLaurentEquiv a)).toAlgHom.toRingHom)) ≫ integralCurveChart U 1 := by
  subst U
  exact splitNodalTorusToSmooth_inclusion a

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)

/-- The actual original residue cubic has its entire smooth open parametrized by Laurent units. -/
def infinityResidueSmoothIso :
    Spec (.of K[T;T⁻¹]) ≅ (integralSmoothOpen V).toScheme :=
  splitEquationSmoothIso (WeierstrassDilatation.residueTangentUnit D)
    (splitDepth_residue_equation D hdepth)

/-- The smooth comparison preserves all original integral functions under contraction. -/
@[reassoc] theorem infinityResidueSmoothIso_contraction :
    (infinityResidueSmoothIso D hdepth).hom ≫ (integralSmoothOpen V).ι ≫
        integralCoefficientMorphism W = infinityResidueContraction D hdepth := by
  rw [infinityResidueSmoothIso, splitEquationSmoothIso_inclusion_assoc,
    integralCurveChart_coefficientMorphism]
  unfold infinityResidueContraction chartCoefficientMorphism
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  let e := (equationChartEquiv (splitDepth_residue_equation D hdepth) 1).trans
    (splitNodalChartLaurentEquiv (WeierstrassDilatation.residueTangentUnit D))
  change ((e.toAlgHom.restrictScalars R).comp (chartCoefficientMap W 1)).toRingHom = _
  congr 1
  apply hom_ext
  intro i
  simp only [e, AlgHom.comp_apply, chartCoefficientMap_coord, AlgHom.restrictScalars_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply,
    equationChartEquiv_coord, infinityResidueOriginalMap_coord]
  exact splitNodalChartToLaurent_coord _ i

/-- The entire original tensor infinity chart is the original residue smooth cubic. -/
def infinityTensorSmoothIso :
    Spec (.of (ChartScalarExtension K W 1)) ≅ (integralSmoothOpen V).toScheme :=
  (infinityResidueIso D hdepth).symm ≪≫ infinityResidueSmoothIso D hdepth

/-- The full tensor-chart comparison is induced by the actual original contraction. -/
@[reassoc] theorem infinityTensorSmoothIso_contraction :
    (infinityTensorSmoothIso D hdepth).hom ≫ (integralSmoothOpen V).ι ≫
        integralCoefficientMorphism W = TensorOpenChart.projection ≫ integralCurveChart W 1 := by
  apply (cancel_epi (infinityResidueIso D hdepth).hom).mp
  simp only [infinityTensorSmoothIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [infinityResidueSmoothIso_contraction, infinityResidueIso_contraction]

end FLT.Mazur.WeierstrassIntegralChart
