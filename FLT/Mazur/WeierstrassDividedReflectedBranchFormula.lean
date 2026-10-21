/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonSumFormula

/-!
# Reflected output formulas beyond the middle sum depth

A common ordinate scale may be smaller than the shallower input scale.
Vieta then constructs an output at the product of that scale and the
relative input scale. This is the algebra for depth m - k - l when
k + l exceeds the middle and the deeper input has depth l.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t a c3 c6 z3 x y u q r i L : R) (hxu : IsUnit (x * u))
local notation "b" => sumDepthIntercept 1 x u q r i

/-- The abscissa quotient at the reflected output scale. -/
def reflectedBranchX : R := (a * b ^ 2 + c3 * b - c6) * ↑hxu.unit⁻¹

/-- The reflected ordinate uses the original shallower input scale in its intercept. -/
def reflectedBranchY : R := -(L + W.a₁) *
  reflectedBranchX a c3 c6 x u q r i hxu - s * b - z3

/-- Vieta constructs the abscissa after cancelling only regular source scales. -/
theorem reflectedBranchX_scale (ht : IsRegular t)
    (hb : y - L * x = t * a * b)
    (hp : x * (t * u) * W.toAffine.addX (s * x) (s * (t * u)) L =
      (y - L * x) ^ 2 + (t * c3) * (y - L * x) - (t ^ 2 * a) * c6) :
    (t * a) * reflectedBranchX a c3 c6 x u q r i hxu =
      W.toAffine.addX (s * x) (s * (t * u)) L := by
  apply ht.left
  apply hxu.mul_left_inj.mp
  have hX : reflectedBranchX a c3 c6 x u q r i hxu * (x * u) =
      a * b ^ 2 + c3 * b - c6 := by
    unfold reflectedBranchX
    rw [mul_assoc, hxu.val_inv_mul, mul_one]
  have hp' : t * (x * u) * W.toAffine.addX (s * x) (s * (t * u)) L =
      t ^ 2 * a * (a * b ^ 2 + c3 * b - c6) := by
    rw [hb] at hp
    linear_combination hp
  linear_combination t ^ 2 * a * hX - hp'

/-- The reflected output ordinate contracts to the same original cubic secant. -/
theorem reflectedBranchY_scale
    (h3 : W.a₃ = (t * a) * z3) (hb : y - L * x = t * a * b)
    (hx : (t * a) * reflectedBranchX a c3 c6 x u q r i hxu =
      W.toAffine.addX (s * x) (s * (t * u)) L) :
    (t * a) * reflectedBranchY W s a c3 c6 z3 x u q r i L hxu =
      W.toAffine.addY (s * x) (s * (t * u)) (s * y) L := by
  unfold reflectedBranchY
  simp only [Affine.addY, Affine.negY, Affine.negAddY, h3]
  linear_combination -(L + W.a₁) * hx + s * hb

end FLT.Mazur.WeierstrassDilatation
