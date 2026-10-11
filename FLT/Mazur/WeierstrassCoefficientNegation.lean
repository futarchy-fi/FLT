/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientZero
public import FLT.Mazur.WeierstrassGlobalNegation
public import FLT.Mazur.WeierstrassAffineMorphismExt
public import FLT.Mazur.WeierstrassIntegralSeparated

/-!
# Negation commutes with arbitrary coefficient extension

The affine coordinate formula and schematic density prove the comparison
on the whole cubic, including singular fibers and nonreduced bases.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
local notation "V" => W.map (algebraMap R S)

/-- The actual affine negation formula is natural in the coefficient algebra. -/
theorem chartCoefficientMap_negation :
    (chartCoefficientMap W 2).comp (affineNegation W) =
      ((affineNegation V).restrictScalars R).comp (chartCoefficientMap W 2) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
      affineNegation_coord, chartNegationCoordinates, WeierstrassCurve.Projective.negY,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk,
      Matrix.head_cons, Matrix.tail_cons, map_sub, map_neg, map_mul, AlgHom.commutes,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      ← IsScalarTower.algebraMap_apply R S]

/-- The global negation square commutes without a discriminant hypothesis. -/
@[reassoc] theorem integralCoefficientMorphism_negation :
    integralCurveNegation V ≫ integralCoefficientMorphism W =
      integralCoefficientMorphism W ≫ integralCurveNegation W := by
  apply integralCurve_hom_ext_affine V (integralCurveStructure W)
  · simp only [Category.assoc, integralCoefficientMorphism_structure]
    rw [← Category.assoc, integralCurveNegation_structure,
      integralCurveNegation_structure, integralCoefficientMorphism_structure]
  · simp only [← Category.assoc, integralCurveChart_negation_affine,
      integralCurveChart_coefficientMorphism]
    simp only [Category.assoc, integralCurveChart_coefficientMorphism,
      integralCurveChart_negation_affine]
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (· ≫ integralCurveChart W 2)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (chartCoefficientMap_negation (S := S) W).symm

end FLT.Mazur.WeierstrassIntegralChart
