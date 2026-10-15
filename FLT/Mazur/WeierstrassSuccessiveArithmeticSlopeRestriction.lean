/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticRestrictionMaps

/-!
# Small slopes on consecutive arithmetic thickenings

The original coefficients and small slope commute with the actual quotient
restriction. Root uniqueness avoids expanding the nested chosen-root terms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => (AlgHom.toRingHom (restriction R π m))

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)

variable (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

local notation "e₁" => nilpotentNodeSlope (W.map q₁) (q₁ s) (q₁ π)
  (q₁ b3) (q₁ b4) (q₁ b6) (ideal Q₁ (parameter R π (m + 1)))
  (arithmeticParameterIdeal_nilpotent π (m + 1)) (ha.map q₁)
  (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
  (arithmeticCoefficient_mem π (m + 1) h3) (arithmeticCoefficient_mem π (m + 1) h4)
  (arithmeticCoefficient_mem π (m + 1) h6)
local notation "e₀" => nilpotentNodeSlope (W.map q₀) (q₀ s) (q₀ π)
  (q₀ b3) (q₀ b4) (q₀ b6) (ideal Q₀ (parameter R π m))
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q₀)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)

/-- The original linear coefficient survives arithmetic restriction. -/
theorem arithmeticNodeSlopeLinear_restriction :
    SuccessiveIncidence.coefficientRingMap f (q₁ π)
      (nodeSlopeLinear (W.map q₁) (q₁ π) (q₁ b3)) =
        nodeSlopeLinear (W.map q₀) (q₀ π) (q₀ b3) := by
  exact nodeSlopeLinear_map f (W.map q₁) (q₁ π) (q₁ b3)

/-- The original constant coefficient survives arithmetic restriction. -/
theorem arithmeticNodeSlopeConstant_restriction :
    SuccessiveIncidence.coefficientRingMap f (q₁ π)
      (nodeSlopeConstant (W.map q₁) (q₁ s) (q₁ π) (q₁ b4) (q₁ b6)) =
        nodeSlopeConstant (W.map q₀) (q₀ s) (q₀ π) (q₀ b4) (q₀ b6) := by
  exact nodeSlopeConstant_map f (W.map q₁) (q₁ s) (q₁ π) (q₁ b4) (q₁ b6)

/-- The constructed small slope commutes with the original quotient restriction. -/
theorem arithmeticNodeSlope_restriction :
    SuccessiveIncidence.coefficientRingMap f (q₁ π) e₁ = e₀ := by
  apply NilpotentQuadraticRoot.root_unique
    (nodeArithmeticIdeal (q₀ π) (ideal Q₀ (parameter R π m)))
    (nodeArithmeticIdeal_nilpotent _ _ (arithmeticParameterIdeal_nilpotent π m))
    (nodeSlopeLinear (W.map q₀) (q₀ π) (q₀ b3))
    (nodeSlopeConstant (W.map q₀) (q₀ s) (q₀ π) (q₀ b4) (q₀ b6))
    (nodeSlopeLinear_unit _ _ _ _ (arithmeticParameterIdeal_nilpotent π m)
      (ha.map q₀) (arithmeticCoefficient_mem π m h3))
  · apply SuccessiveIncidence.coefficientRingMap_ideal f (q₁ π)
      (ideal Q₁ (parameter R π (m + 1))) (ideal Q₀ (parameter R π m))
      (arithmeticParameterIdeal_restriction R π m)
    exact nilpotentNodeSlope_mem (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
      _ (arithmeticParameterIdeal_nilpotent π (m + 1)) (ha.map q₁)
      (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
      (arithmeticCoefficient_mem π (m + 1) h3) (arithmeticCoefficient_mem π (m + 1) h4)
      (arithmeticCoefficient_mem π (m + 1) h6)
  · exact nilpotentNodeSlope_mem (W.map q₀) (q₀ s) (q₀ π) (q₀ b3) (q₀ b4) (q₀ b6)
      _ (arithmeticParameterIdeal_nilpotent π m) (ha.map q₀)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
      (arithmeticCoefficient_mem π m h6)
  · have he := congrArg (SuccessiveIncidence.coefficientRingMap f (q₁ π))
      (nilpotentNodeSlope_equation (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
        _ (arithmeticParameterIdeal_nilpotent π (m + 1)) (ha.map q₁)
        (arithmeticCoefficient_mem π (m + 1) hs) (arithmeticCoefficient_mem π (m + 1) h2)
        (arithmeticCoefficient_mem π (m + 1) h3) (arithmeticCoefficient_mem π (m + 1) h4)
        (arithmeticCoefficient_mem π (m + 1) h6))
    simpa only [map_add, map_mul, map_pow, arithmeticNodeSlopeLinear_restriction,
      arithmeticNodeSlopeConstant_restriction] using he
  · exact nilpotentNodeSlope_equation (W.map q₀) (q₀ s) (q₀ π) (q₀ b3) (q₀ b4) (q₀ b6)
      _ (arithmeticParameterIdeal_nilpotent π m) (ha.map q₀)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
      (arithmeticCoefficient_mem π m h6)

end FLT.Mazur.WeierstrassSuccessiveX
