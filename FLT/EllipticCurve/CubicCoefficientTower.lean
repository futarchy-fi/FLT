/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChangeBaseChange
/-! # Composition of coefficient extension

For a scalar tower, the two successive coefficient morphisms agree with
direct extension after identifying their Weierstrass equations.
The identity is checked on both quotient chart rings and then glued.

This supplies the curve-level compatibility needed for composition of
parameter-changing cyclic automorphisms. Compatibility on torsion and
cyclic quotients is a further step.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (W : WeierstrassCurve R)

theorem coefficientTower_curve :
    (W.map (algebraMap R S)).map (algebraMap S T) = W.map (algebraMap R T) := by
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R S T]

theorem chartRingCongr_mk {A : Type u} [CommRing A] {V U : WeierstrassCurve A}
    (h : V = U) (b : Bool) (f : MvPolynomial (Fin 2) A) :
    chartRingCongr h b (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f := by
  subst U
  rfl

theorem chartCoefficientMap_tower (b : Bool) :
    (chartCoefficientMap (W.map (algebraMap R S)) T b).comp
        (chartCoefficientMap W S b) =
      (chartRingCongr (coefficientTower_curve (S := S) (T := T) W).symm b).toRingHom.comp
        (chartCoefficientMap W T b) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro f
  change chartCoefficientMap (W.map (algebraMap R S)) T b
      (chartCoefficientMap W S b (Ideal.Quotient.mk _ f)) =
    chartRingCongr _ b (chartCoefficientMap W T b (Ideal.Quotient.mk _ f))
  rw [chartCoefficientMap_mk, chartCoefficientMap_mk,
    chartCoefficientMap_mk, chartRingCongr_mk]
  congr 1
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq R S T]

theorem chartCoefficientMorphism_tower (b : Bool) :
    chartCoefficientMorphism (W.map (algebraMap R S)) T b ≫
        chartCoefficientMorphism W S b =
      eqToHom (congrArg (fun E => chart E b)
        (coefficientTower_curve (S := S) (T := T) W)) ≫
          chartCoefficientMorphism W T b := by
  dsimp only [chartCoefficientMorphism]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((chartCoefficientMap (W.map (algebraMap R S)) T b).comp
      (chartCoefficientMap W S b))) = _
  rw [chartCoefficientMap_tower]
  change Spec.map (CommRingCat.ofHom (chartCoefficientMap W T b) ≫
    CommRingCat.ofHom (chartRingCongr
      (coefficientTower_curve (S := S) (T := T) W).symm b).toAlgHom.toRingHom) = _
  rw [Spec.map_comp, chartRingCongr_spec]

theorem coefficientMorphism_tower :
    coefficientMorphism (W.map (algebraMap R S)) T ≫ coefficientMorphism W S =
      eqToHom (congrArg scheme (coefficientTower_curve (S := S) (T := T) W)) ≫
        coefficientMorphism W T := by
  apply pushout.hom_ext
  · change sourceChart ((W.map (algebraMap R S)).map (algebraMap S T)) false ≫ _ =
      sourceChart ((W.map (algebraMap R S)).map (algebraMap S T)) false ≫ _
    rw [← Category.assoc, sourceChart_coefficientMorphism, Category.assoc,
      sourceChart_coefficientMorphism, ← Category.assoc, chartCoefficientMorphism_tower,
      Category.assoc, ← sourceChart_coefficientMorphism, ← Category.assoc,
      (chart_eqToHom (coefficientTower_curve (S := S) (T := T) W) false),
      Category.assoc]
  · change sourceChart ((W.map (algebraMap R S)).map (algebraMap S T)) true ≫ _ =
      sourceChart ((W.map (algebraMap R S)).map (algebraMap S T)) true ≫ _
    rw [← Category.assoc, sourceChart_coefficientMorphism, Category.assoc,
      sourceChart_coefficientMorphism, ← Category.assoc, chartCoefficientMorphism_tower,
      Category.assoc, ← sourceChart_coefficientMorphism, ← Category.assoc,
      (chart_eqToHom (coefficientTower_curve (S := S) (T := T) W) true),
      Category.assoc]

end WeierstrassCurve.CubicCharts
