/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerFormula

/-!
# Smooth residues of smaller-scale branch outputs

When the input scale vanishes faster than the target scale, the terminal
constant forces a unit output abscissa and vertical derivative. The proof
works over arbitrary residue rings, including characteristic two.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K)
  (W : WeierstrassCurve R) (s t w b3 a2 b4' b6' e3 u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "V" => tangentLowerOrdinate W w b3 a2 b4' b6' u₁ v₁ hc
local notation "l" => tangentLowerSlope W w b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentLowerX W t w a2 u₁ u₂ l
local notation "Y" => tangentLowerY W s t w b3 a2 u₁ u₂ v₁ l

/-- The constructed divided ordinate satisfies its inverse-free denominator identity. -/
theorem tangentLowerOrdinate_denominator :
    V * (v₁ + W.a₁ * u₁ + b3) = w * u₁ ^ 3 + a2 * u₁ ^ 2 + b4' * u₁ + b6' := by
  unfold tangentLowerOrdinate
  rw [mul_assoc, hc.val_inv_mul, mul_one]

/-- The constructed divided slope satisfies its inverse-free denominator identity. -/
theorem tangentLowerSlope_denominator :
    l * (v₁ + v₂ + W.a₁ * u₂ + b3) =
      w * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + a2 * (u₁ + u₂) + b4' - W.a₁ * V := by
  unfold tangentLowerSlope
  rw [mul_assoc, hd.val_inv_mul, mul_one]

/-- The terminal constant forces the actual smaller-scale abscissa to be a unit. -/
theorem tangentLowerX_specialized_isUnit
    (ht : f t = 0) (hw : f w = 0) (h3 : f b3 = 0)
    (h2 : f a2 = 0) (h4 : f b4' = 0) (h₁ : f v₁ = 0) (h₂ : f v₂ = 0)
    (h6 : IsUnit (f b6')) : IsUnit (f X) := by
  have hv := congrArg f (tangentLowerOrdinate_denominator W w b3 a2 b4' b6' u₁ v₁ hc)
  have hl := congrArg f
    (tangentLowerSlope_denominator W w b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd)
  simp only [map_add, map_mul, map_pow, map_sub, hw, h2, h4, h3, h₁, h₂,
    zero_mul, zero_add, add_zero, zero_sub] at hv hl
  have hx : f X = f W.a₁ * f l := by
    simp only [tangentLowerX, map_sub, map_add, map_mul, map_pow,
      ht, hw, h2, zero_mul, zero_add, sub_zero]
  have he : f X * (f u₁ * f u₂) = -f b6' := by
    rw [hx]
    linear_combination f u₁ * hl - hv
  exact isUnit_of_mul_isUnit_left (he.symm ▸ h6.neg)

/-- The smaller-scale output is vertically smooth at every terminal specialization. -/
theorem tangentLower_specialized_vertical_isUnit
    (hs : f s = 0) (ht : f t = 0) (hw : f w = 0) (h3 : f b3 = 0)
    (h2 : f a2 = 0) (h4 : f b4' = 0) (he3 : f e3 = 0)
    (h₁ : f v₁ = 0) (h₂ : f v₂ = 0) (h6 : IsUnit (f b6')) :
    IsUnit (f (2 * Y + W.a₁ * X + e3)) := by
  have ha : IsUnit (f W.a₁) := by
    have h := hc.map f
    simp only [map_add, map_mul, h₁, h3, zero_add, add_zero] at h
    exact isUnit_of_mul_isUnit_left h
  have hx := tangentLowerX_specialized_isUnit f W t w b3 a2 b4' b6' u₁ u₂ v₁ v₂
    hc hd ht hw h3 h2 h4 h₁ h₂ h6
  have hy : f Y = -(f W.a₁ * f X) := by
    simp only [tangentLowerY, map_sub, map_add, map_mul, map_neg,
      hs, ht, hw, zero_mul, zero_add, sub_zero, add_zero, neg_mul]
  have he : f (2 * Y + W.a₁ * X + e3) = -(f W.a₁ * f X) := by
    simp only [map_add, map_mul, map_ofNat, he3, add_zero]
    linear_combination 2 * hy
  rw [he]
  exact (ha.mul hx).neg

end FLT.Mazur.WeierstrassDilatation
