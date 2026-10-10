/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityInnerPencil
public import FLT.Mazur.WeierstrassInfinitySlopeMap

/-!
# The inner pencil as an identity of polynomials

Extend coefficients before introducing the free coordinate. Polynomial equality
retains coefficients over finite and nonreduced rings, where equality of the
associated polynomial functions would not suffice.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ x₃ z₁ z₂ z₃ l m : R}

/-- The two inner secants give equal quadratic polynomials after the explicit correction. -/
theorem infinity_inner_pencil_polynomial
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂) :
    (X - C x₁) *
        (C (infinityLineLeading W l) * X - C (infinityAdditionXYZ W x₁ x₂ z₁ l 0)) -
      (X - C x₃) *
        (C (infinityLineLeading W m) * X - C (infinityAdditionXYZ W x₂ x₃ z₂ m 0)) =
      C (l - m) * infinitySlopeDenominator (W.map C) X
        (C z₂ + C l * (X - C x₂)) (C z₂ + C m * (X - C x₂)) := by
  have h := infinity_inner_pencil (W.map C)
    (infinitySlope_line_map C hl) (infinitySlope_line_map C hm)
    (infinitySlope_cubic_map W C hcl) (infinitySlope_cubic_map W C hcm) X
  simpa only [infinityLineLeading_map, ← infinityAdditionXYZ_map,
    Function.comp_apply, map_sub] using h

/-- The same polynomial identity retains both actual homogeneous normalizers. -/
theorem infinity_inner_pencil_polynomial_normalized {u v u' v' c c' : R}
    (hl : l * (x₂ - x₁) = z₂ - z₁)
    (hm : m * (x₃ - x₂) = z₃ - z₂)
    (hcl : l * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hcm : m * infinitySlopeDenominator W x₃ z₂ z₃ =
      infinitySlopeNumerator W x₂ x₃ z₂)
    (hx : u * c = infinityAdditionXYZ W x₁ x₂ z₁ l 0)
    (hn : (-1 - W.a₁ * u - W.a₃ * v) * c = infinityLineLeading W l)
    (hx' : u' * c' = infinityAdditionXYZ W x₂ x₃ z₂ m 0)
    (hn' : (-1 - W.a₁ * u' - W.a₃ * v') * c' = infinityLineLeading W m) :
    C c * (X - C x₁) * (C (-1 - W.a₁ * u - W.a₃ * v) * X - C u) -
        C c' * (X - C x₃) * (C (-1 - W.a₁ * u' - W.a₃ * v') * X - C u') =
      C (l - m) * infinitySlopeDenominator (W.map C) X
        (C z₂ + C l * (X - C x₂)) (C z₂ + C m * (X - C x₂)) := by
  have h := infinity_inner_pencil_polynomial W hl hm hcl hcm
  rw [← hx, ← hn, ← hx', ← hn', map_mul, map_mul, map_mul, map_mul] at h
  linear_combination h

end FLT.Mazur.WeierstrassIntegralChart
