/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInnerCross

/-!
# A common quadratic pencil for the two inner secants

Compare the two divided cubics as polynomials in a free coordinate, retaining
both third factors. This is stronger than the cross relation at either endpoint
and does not divide by an input difference or a slope difference.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Dividing at the common center leaves the first input and third-point factors. -/
theorem infinityLineDivided_third_factor {x₁ x₂ z₁ z₂ l : R}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hc : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) (T : R) :
    infinityLineDivided W x₂ z₂ l (T - x₂) =
      (T - x₁) *
        (infinityLineLeading W l * T - infinityAdditionXYZ W x₁ x₂ z₁ l 0) := by
  have hl' : l * (x₁ - x₂) = z₁ - z₂ := by linear_combination -hl
  have ha := infinityLineDivided_of_slope W hl' (infinitySlope_cubic_swap W hl hc)
  rw [infinityLineDivided_factor W ha, ← infinityAdditionXYZ_swap W hl,
    infinityAdditionXYZ_x]
  ring

/-- The two inner third factors belong to a single quadratic pencil. -/
theorem infinity_inner_pencil {x₁ x₂ x₃ z₁ z₂ z₃ l m : R}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂) (T : R) :
    (T - x₁) *
        (infinityLineLeading W l * T - infinityAdditionXYZ W x₁ x₂ z₁ l 0) -
      (T - x₃) *
        (infinityLineLeading W m * T - infinityAdditionXYZ W x₂ x₃ z₂ m 0) =
      (l - m) *
        infinitySlopeDenominator W T (z₂ + l * (T - x₂)) (z₂ + m * (T - x₂)) := by
  have hm' : m * (x₂ - x₃) = z₂ - z₃ := by linear_combination -hm
  have h := infinityLineDivided_sub W x₂ z₂ l m (T - x₂)
  rw [infinityLineDivided_third_factor W hl hcl,
    infinityLineDivided_third_factor W hm' (infinitySlope_cubic_swap W hm hcm),
    infinityAdditionXYZ_swap W hm, show x₂ + (T - x₂) = T by ring] at h
  exact h

/-- The common pencil uses both actual normalized third factors, with their scales explicit. -/
theorem infinity_inner_pencil_normalized {x₁ x₂ x₃ z₁ z₂ z₃ l m u v u' v' c c' : R}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂)
    (hx : u * c = infinityAdditionXYZ W x₁ x₂ z₁ l 0)
    (hn : (-1 - W.a₁ * u - W.a₃ * v) * c = infinityLineLeading W l)
    (hx' : u' * c' = infinityAdditionXYZ W x₂ x₃ z₂ m 0)
    (hn' : (-1 - W.a₁ * u' - W.a₃ * v') * c' = infinityLineLeading W m)
    (T : R) :
    c * (T - x₁) * ((-1 - W.a₁ * u - W.a₃ * v) * T - u) -
        c' * (T - x₃) * ((-1 - W.a₁ * u' - W.a₃ * v') * T - u') =
      (l - m) *
        infinitySlopeDenominator W T (z₂ + l * (T - x₂)) (z₂ + m * (T - x₂)) := by
  have h := infinity_inner_pencil W hl hm hcl hcm T
  rw [← hx, ← hn, ← hx', ← hn'] at h
  linear_combination h

end FLT.Mazur.WeierstrassIntegralChart
