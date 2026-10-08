/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityDividedLine
public import FLT.Mazur.WeierstrassSlopeSwapFormula

/-!
# A homogeneous cross relation for the two inner infinity laws

Both divided cubic equations are centered at the middle input. Their difference
relates the first homogeneous output to the second slope, without canceling an
input difference or the leading coefficient of either cubic.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ x₃ z₁ z₂ z₃ l m : R}

/-- The first inner third point and the second inner slope satisfy an integral cross relation. -/
theorem infinity_inner_cross
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂) :
    (x₃ - x₁) *
        (infinityLineLeading W l * x₃ - infinityAdditionXYZ W x₁ x₂ z₁ l 0) =
      (l - m) * infinitySlopeDenominator W x₃ (z₂ + l * (x₃ - x₂)) z₃ := by
  have hl' : l * (x₁ - x₂) = z₁ - z₂ := by linear_combination -hl
  have ha := infinityLineDivided_of_slope W hl' (infinitySlope_cubic_swap W hl hcl)
  have hd := infinityLineDivided_of_slope W hm hcm
  have hf := infinityLineDivided_cross W ha hd
  have hz : z₂ + m * (x₃ - x₂) = z₃ := by linear_combination hm
  rw [hz, show x₂ + (x₃ - x₂) = x₃ by ring] at hf
  rw [← infinityAdditionXYZ_swap W hl, infinityAdditionXYZ_x]
  linear_combination hf

/-- The cross relation uses the actual normalized third factor after clearing only output Y. -/
theorem infinity_inner_cross_normalized {u v c : R}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂)
    (hx : u * c = infinityAdditionXYZ W x₁ x₂ z₁ l 0)
    (hn : (-1 - W.a₁ * u - W.a₃ * v) * c = infinityLineLeading W l) :
    c * (x₃ - x₁) * ((-1 - W.a₁ * u - W.a₃ * v) * x₃ - u) =
      (l - m) * infinitySlopeDenominator W x₃ (z₂ + l * (x₃ - x₂)) z₃ := by
  have h := infinity_inner_cross W hl hm hcl hcm
  rw [← hx, ← hn] at h
  linear_combination h

end FLT.Mazur.WeierstrassIntegralChart
