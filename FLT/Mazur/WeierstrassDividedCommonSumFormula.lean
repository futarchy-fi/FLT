/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSumDepthFormula

/-!
# Sum-depth formulas from a common-scale ordinate quotient

The deeper ordinate need only be divided by the shallower scale. This
constructs the same sum-depth output without an own-scale deeper quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t c3 c6 x y u v q r i l : R)

local notation "b" => sumDepthIntercept 1 x u q r i

/-- The chord relation proves the extra intercept divisibility. -/
theorem commonSumDepthIntercept_scale
    (hi : i * (x - t * u) = 1) (hl : l * (x - t * u) = y - t * v)
    (hy : s * q = y) (hv : s * r = v) : y - l * x = s * t * b := by
  have hu : IsUnit (x - t * u) := isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩
  apply hu.mul_left_inj.mp
  have hb : b * (x - t * u) = x * r - q * u := by
    simp only [sumDepthIntercept, one_mul, mul_assoc, hi, mul_one]
  linear_combination -x * hl + t * u * hy - t * x * hv - s * t * hb

variable (hxu : IsUnit (x * u))

local notation "X" => sumDepthX 1 c3 c6 x u q r i hxu
local notation "Y" => sumDepthY W 1 c3 c6 x u q r i l hxu

/-- Only the extra scale needs cancellation to recover the abscissa factorization. -/
theorem commonSumDepthX_scale (ht : IsRegular t)
    (hb : y - l * x = s * t * b)
    (hp : x * (t * u) * W.toAffine.addX (s * x) (s * (t * u)) l =
      (y - l * x) ^ 2 + (s * t * c3) * (y - l * x) - (s * t) ^ 2 * c6) :
    (s ^ 2 * t) * X = W.toAffine.addX (s * x) (s * (t * u)) l := by
  apply ht.left
  apply hxu.mul_left_inj.mp
  have hX : X * (x * u) = b ^ 2 + c3 * b - c6 := by
    unfold sumDepthX
    rw [mul_assoc, hxu.val_inv_mul, mul_one]
  rw [hb] at hp
  calc
    t * ((s ^ 2 * t) * X) * (x * u) = s ^ 2 * t ^ 2 * (X * (x * u)) := by ring
    _ = s ^ 2 * t ^ 2 * (b ^ 2 + c3 * b - c6) := by rw [hX]
    _ = t * W.toAffine.addX (s * x) (s * (t * u)) l * (x * u) := by
      linear_combination -hp

/-- The ordinate factorization uses the same constructed line intercept. -/
theorem commonSumDepthY_scale (h3 : W.a₃ = s ^ 2 * t * c3)
    (hb : y - l * x = s * t * b)
    (hx : (s ^ 2 * t) * X = W.toAffine.addX (s * x) (s * (t * u)) l) :
    (s ^ 2 * t) * Y = W.toAffine.addY (s * x) (s * (t * u)) (s * y) l := by
  unfold sumDepthY
  simp only [Affine.addY, Affine.negY, Affine.negAddY, h3]
  linear_combination -(l + W.a₁) * hx + s * hb

end FLT.Mazur.WeierstrassDilatation
