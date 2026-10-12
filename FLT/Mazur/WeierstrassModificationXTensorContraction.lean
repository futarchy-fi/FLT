/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXTensorOriginal
public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.TensorOpenChart

/-!
# The original tensor contraction commutes with coefficient extension

The independently constructed extended affine input recovers the original
incidence-chart contraction, on all functions and without reducedness assumptions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "V" => W.map (algebraMap R S)
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "f" => tensorOriginalAffineMap W s b3 b4 b6 h3 h4 h6 S

/-- Coefficient extension retains each original affine cubic function in the tensor chart. -/
theorem tensorOriginalAffineMap_coefficient :
    ((f).restrictScalars R).comp (WeierstrassIntegralChart.chartCoefficientMap W 2) =
      (Algebra.TensorProduct.includeRight : Coordinate W s b3 b4 b6 →ₐ[R] T).comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change f (WeierstrassIntegralChart.chartCoefficientMap W 2
      (WeierstrassIntegralChart.coord W 2 0)) =
        (1 : S) ⊗ₜ[R] fromOriginal W s b3 b4 b6 h3 h4 h6
          (WeierstrassIntegralChart.coord W 2 0)
    rw [WeierstrassIntegralChart.chartCoefficientMap_coord, tensorOriginalAffineMap_x]
    rw [fromOriginal_x]
  · change f (WeierstrassIntegralChart.chartCoefficientMap W 2
      (WeierstrassIntegralChart.coord W 2 1)) =
        (1 : S) ⊗ₜ[R] fromOriginal W s b3 b4 b6 h3 h4 h6
          (WeierstrassIntegralChart.coord W 2 1)
    rw [WeierstrassIntegralChart.chartCoefficientMap_coord, tensorOriginalAffineMap_y]
    rw [fromOriginal_y]
  · change f (WeierstrassIntegralChart.chartCoefficientMap W 2
      (WeierstrassIntegralChart.coord W 2 2)) =
        (1 : S) ⊗ₜ[R] fromOriginal W s b3 b4 b6 h3 h4 h6
          (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one, map_one]
    rfl

/-- The entire extended affine input projects to the actual original incidence contraction. -/
@[reassoc] theorem tensorOriginalAffineMap_toCurve :
    Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        WeierstrassIntegralChart.integralCurveChart V 2 ≫
          WeierstrassIntegralChart.integralCoefficientMorphism W =
      TensorOpenChart.projection ≫ toCurve W s b3 b4 b6 h3 h4 h6 := by
  rw [WeierstrassIntegralChart.integralCurveChart_coefficientMorphism]
  unfold WeierstrassIntegralChart.chartCoefficientMorphism TensorOpenChart.projection toCurve
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  apply congrArg (· ≫ WeierstrassIntegralChart.integralCurveChart W 2)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (tensorOriginalAffineMap_coefficient (S := S)
    W s b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
