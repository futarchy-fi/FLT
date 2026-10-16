/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTensorInfinity
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioTensorAffine
public import FLT.Mazur.WeierstrassModificationXCoefficientContraction
public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityStructure

/-!
# The complete initial overlap in the original arithmetic infinity tensor chart

The explicit original projective transition on the whole node intersection
preserves the coefficient and cubic projections and the corrected polygon map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassIntegralChart
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
attribute [local irreducible] arithmeticFactorRatioAffinePolygonMap
  arithmeticFactorRatioInfinityPolygonMap
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (ha : IsUnit W.a₁)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "r" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "hr" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "hm" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "E" => polynomialNodeOverlapInfinityIso (W.map q) (q s) (q b3) (q b4) (q b6)
  r hr J (arithmeticParameterIdeal_nilpotent π m) hm (arithmeticCoefficient_mem π m h3)
local notation "T" => Spec.map (CommRingCat.ofHom
  (arithmeticFactorRatioInfinityTransition π m W s b3 b4 b6 h₃ h₄ h₆).toRingHom)
local notation "P" => polynomialNodeOverlapInclusion (W.map q) (q s)
local notation "F" => arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6

/-- The original full overlap maps explicitly into the original arithmetic infinity tensor. -/
def arithmeticFactorRatioOverlapInfinity :
    Spec (.of (PolynomialNodeOverlap (W.map q) (q s))) ⟶
      Spec (.of (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) :=
  (E).hom ≫ T ≫ (arithmeticInfinityTensorIso π m W).hom

attribute [local irreducible] arithmeticFactorRatioOverlapInfinity
  polynomialSlopeRoot polynomialNodeOverlapInfinityIso arithmeticInitialTensorNodeChart

/-- The explicit overlap retains its complete arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticFactorRatioOverlapInfinity_structure :
    arithmeticFactorRatioOverlapInfinity π m W s b3 b4 b6 ha h2 h3 h4 h6 h₃ h₄ h₆ ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (Q ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolynomialNodeOverlap (W.map q) (q s)))) := by
  rw [arithmeticFactorRatioOverlapInfinity, Category.assoc, Category.assoc,
    arithmeticInfinityTensorIso_structure]
  unfold arithmeticFactorRatioInfinityTransition
  rw [initialInfinityTransition_structure, polynomialNodeOverlapInfinityIso_structure]

/-- The explicit full overlap keeps every original cubic function under contraction. -/
@[reassoc] theorem arithmeticFactorRatioOverlapInfinity_toCurve :
    arithmeticFactorRatioOverlapInfinity π m W s b3 b4 b6 ha h2 h3 h4 h6 h₃ h₄ h₆ ≫
      TensorOpenChart.projection ≫ integralCurveChart W 1 =
      P ≫ F ≫ TensorOpenChart.projection ≫ toCurve W s b3 b4 b6 h₃ h₄ h₆ := by
  rw [arithmeticFactorRatioOverlapInfinity, Category.assoc, Category.assoc,
    arithmeticInfinityTensorIso_projection_assoc,
    ← integralCurveChart_coefficientMorphism]
  unfold arithmeticFactorRatioInfinityTransition
  rw [initialInfinityTransition_toCurve_assoc, ← Category.assoc]
  erw [polynomialNodeOverlapInfinityIso_hom_inclusion]
  simp only [arithmeticInitialTensorNodeChart, Category.assoc]
  rw [arithmeticInitialTensorIso_projection_assoc, coefficientMap_toCurve]
  rfl

variable (hs : π ∣ s) (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆) (k : ℕ)

/-- The complete explicit infinity overlap agrees with the original full initial tensor map. -/
@[reassoc] theorem arithmeticFactorRatioOverlapInfinity_polygon :
    arithmeticFactorRatioOverlapInfinity π m W s b3 b4 b6 ha h2 h3 h4 h6 h₃ h₄ h₆ ≫
      arithmeticFactorRatioTensorInfinityMap π m W s b3 b4 b6
        ha hs h2 h3 h4 h6 h3a h4a h6a k =
      P ≫ F ≫ arithmeticFactorRatioTensorAffineMap π m W s b3 b4 b6
        ha hs h2 h3 h4 h6 k := by
  rw [arithmeticFactorRatioOverlapInfinity, Category.assoc, Category.assoc,
    arithmeticFactorRatioTensorInfinityMap_transport,
    arithmeticFactorRatioInfinityPolygonMap_initial,
    ← Category.assoc, polynomialNodeOverlapInfinityIso_hom_inclusion]
  simp only [arithmeticInitialTensorNodeChart, Category.assoc]
  rw [arithmeticFactorRatioTensorAffineMap_transport]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
