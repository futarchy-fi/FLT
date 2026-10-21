/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchFormula

/-!
# Reflected coordinates with the wider numerator scale

When the common ordinate scale is the shallower input scale, the reflected
numerator has scale 2*(k+l)-m. Vieta cancels the relative input scale and
keeps the exact constant quotient, even when the sum-depth datum is absent.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t p w v d3 d6 z3 C x y u q r i L : R) (hxu : IsUnit (x * u))
local notation "b" => sumDepthIntercept 1 x u q r i
local notation "X" => reflectedBranchX v z3 C x u q r i hxu
local notation "Y" => reflectedBranchY W v v z3 C z3 x u q r i L hxu

/-- Factor Vieta using the wider numerator scale and the exact constant quotient. -/
theorem widerReflectedX_scale (ht : IsRegular t)
    (hb : y - L * x = p * b) (hp2 : p ^ 2 = t * w * v)
    (h3 : d3 * p = t * w * z3) (h6 : d6 = t * w * C)
    (hp : x * (t * u) * W.toAffine.addX (s * x) (s * (t * u)) L =
      (y - L * x) ^ 2 + d3 * (y - L * x) - d6) :
    w * X = W.toAffine.addX (s * x) (s * (t * u)) L := by
  apply ht.left
  apply hxu.mul_left_inj.mp
  have hX : X * (x * u) = v * b ^ 2 + z3 * b - C := by
    unfold reflectedBranchX
    rw [mul_assoc, hxu.val_inv_mul, mul_one]
  rw [hb] at hp
  linear_combination t * w * hX - hp - b ^ 2 * hp2 - b * h3 + h6

/-- The same scale contracts the ordinate to the original secant ordinate. -/
theorem widerReflectedY_scale (h3 : W.a₃ = w * z3)
    (hb : y - L * x = p * b) (hv : s * p = w * v)
    (hx : w * X = W.toAffine.addX (s * x) (s * (t * u)) L) :
    w * Y = W.toAffine.addY (s * x) (s * (t * u)) (s * y) L := by
  unfold reflectedBranchY
  simp only [Affine.addY, Affine.negY, Affine.negAddY, h3]
  linear_combination -(L + W.a₁) * hx + s * hb + b * hv

end FLT.Mazur.WeierstrassDilatation
