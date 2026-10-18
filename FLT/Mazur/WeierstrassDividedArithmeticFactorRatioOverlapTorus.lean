/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioOverlapParameter
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioOverlap
public import FLT.Mazur.WeierstrassModificationXFullInfinityFactorRatioBoundary

/-!
# The entire arithmetic infinity parameter on the original full overlap

The actual projective transition pulls the regular infinity ratio back to the
canonical Laurent parameter on D(q), before any target polygon is chosen.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "r₀" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hr₀" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hm₀" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)


variable (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆)

/-- The full specialized infinity cubic carries its regular canonical Laurent ratio. -/
def arithmeticFullInfinityRatioParameter :
    Spec (.of (WeierstrassIntegralChart.Coordinate (W.map q) 1)) ⟶
      PolygonSmoothing.branchTorus Q :=
  infinityFactorRatioParameter (W.map q) J (arithmeticParameterIdeal_nilpotent π m)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3a)
    (arithmeticCoefficient_mem π m h4a) (arithmeticCoefficient_mem π m h6a)
    (q s) (q b3) r₀ hm₀ (arithmeticCoefficient_mem π m h3)

local notation "f" => arithmeticFullInfinityRatioParameter π m W s b3 b4 b6
  ha h2 h3 h4 h6 h3a h4a h6a
local notation "P" => arithmeticFactorRatioOverlapParameter π m W s b3 b4 b6 ha h2 h3 h4 h6
variable (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)

attribute [local irreducible] arithmeticInfinityTensorIso arithmeticFactorRatioOverlapInfinity
  polynomialSlopeRoot

/-- The original complete tensor overlap pulls back exactly the full Laurent ratio. -/
@[reassoc] theorem arithmeticFullInfinityRatioParameter_overlap :
    arithmeticFactorRatioOverlapInfinity π m W s b3 b4 b6 ha h2 h3 h4 h6 h₃ h₄ h₆ ≫
      (arithmeticInfinityTensorIso π m W).inv ≫ f = P := by
  rw [arithmeticFactorRatioOverlapInfinity]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  unfold arithmeticFullInfinityRatioParameter arithmeticFactorRatioInfinityTransition
  rw [fullInfinityFactorRatioParameter_boundary (W.map q) (q s) (q b3) (q b4) (q b6)
    _ _ _ J (arithmeticParameterIdeal_nilpotent π m)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3a)
    (arithmeticCoefficient_mem π m h4a) (arithmeticCoefficient_mem π m h6a)
    r₀ hr₀ hm₀ (arithmeticCoefficient_mem π m h3)]
  simp only [factorRatioInfinityParameter, Iso.hom_inv_id_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
