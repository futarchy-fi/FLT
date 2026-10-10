/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveProduct

/-!
# Swapping the actual inputs of the integral cubic

The tensor-algebra interchange induces the swap of the actual scheme fiber
product. The compatibility is proved using both projections, so it applies
over arbitrary coefficient rings and on every input chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Interchange the factors of a concrete chart product. -/
def chartProductSwap (j k : Fin 3) : ChartProduct W j k →ₐ[R] ChartProduct W k j :=
  (Algebra.TensorProduct.comm R (Coordinate W j) (Coordinate W k)).toAlgHom

/-- The first input becomes the second input. -/
@[simp] theorem chartProductSwap_left (j k : Fin 3) :
    (chartProductSwap W j k).comp (chartProductLeft W j k) = chartProductRight W k j :=
  Algebra.TensorProduct.comm_comp_includeLeft R (Coordinate W j) (Coordinate W k)

/-- The second input becomes the first input. -/
@[simp] theorem chartProductSwap_right (j k : Fin 3) :
    (chartProductSwap W j k).comp (chartProductRight W j k) = chartProductLeft W k j :=
  Algebra.TensorProduct.comm_comp_includeRight R (Coordinate W j) (Coordinate W k)

/-- Two swaps recover the original input algebra. -/
@[simp] theorem chartProductSwap_swap (j k : Fin 3) :
    (chartProductSwap W k j).comp (chartProductSwap W j k) = AlgHom.id R _ := by
  apply AlgHom.ext
  intro x
  change Algebra.TensorProduct.comm R (Coordinate W k) (Coordinate W j)
    (Algebra.TensorProduct.comm R (Coordinate W j) (Coordinate W k) x) = x
  rw [← Algebra.TensorProduct.comm_symm]
  exact AlgEquiv.symm_apply_apply _ x

attribute [irreducible] chartProductSwap

/-- On spectra the tensor swap interchanges the first input projection. -/
theorem chartProductSwap_spec_left (j k : Fin 3) :
    Spec.map (CommRingCat.ofHom (chartProductSwap W j k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (chartProductLeft W j k).toRingHom) =
      Spec.map (CommRingCat.ofHom (chartProductRight W k j).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (chartProductSwap_left W j k)

/-- On spectra the tensor swap interchanges the second input projection. -/
theorem chartProductSwap_spec_right (j k : Fin 3) :
    Spec.map (CommRingCat.ofHom (chartProductSwap W j k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (chartProductRight W j k).toRingHom) =
      Spec.map (CommRingCat.ofHom (chartProductLeft W k j).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (chartProductSwap_right W j k)

/-- Swap the factors of the actual integral curve fiber product. -/
def integralCurveSwap : integralCurveProduct W ⟶ integralCurveProduct W :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm

/-- First projection after swapping. -/
@[reassoc (attr := simp)] theorem integralCurveSwap_fst :
    integralCurveSwap W ≫ pullback.fst _ _ = pullback.snd _ _ :=
  pullback.lift_fst _ _ _

/-- Second projection after swapping. -/
@[reassoc (attr := simp)] theorem integralCurveSwap_snd :
    integralCurveSwap W ≫ pullback.snd _ _ = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

/-- The actual swap is involutive. -/
@[simp] theorem integralCurveSwap_swap :
    integralCurveSwap W ≫ integralCurveSwap W = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- Tensor interchange realizes the swap on each member of the product atlas. -/
theorem integralCurveProductChart_swap (b c : Bool) :
    integralCurveProductChart W b c ≫ integralCurveSwap W =
      Spec.map (CommRingCat.ofHom (chartProductSwap W
        (productChartCoordinate c) (productChartCoordinate b)).toRingHom) ≫
          integralCurveProductChart W c b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralCurveSwap_fst, integralCurveProductChart_snd,
      integralCurveProductChart_fst]
    rw [← Category.assoc, chartProductSwap_spec_left]
  · simp only [Category.assoc, integralCurveSwap_snd, integralCurveProductChart_fst,
      integralCurveProductChart_snd]
    rw [← Category.assoc, chartProductSwap_spec_right]

end FLT.Mazur.WeierstrassIntegralChart
