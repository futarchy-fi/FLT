/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantProduct

/-!
# Sum-depth output coordinates on a strict branch

For input scales s and s*t, divide the branch ordinates by their own
scales. The line intercept then has a factor s*s*t. Vieta's identity
constructs the output at that sum depth using only unit abscissae.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t c3 c6 x y u v q r i l : R)

/-- The divided line intercept, using each input's own branch ordinate. -/
def sumDepthIntercept : R := (t * x * r - q * u) * i

local notation "b" => sumDepthIntercept t x u q r i

/-- The chord relation proves the extra intercept divisibility. -/
theorem sumDepthIntercept_scale
    (hi : i * (x - t * u) = 1) (hl : l * (x - t * u) = y - t * v)
    (hy : s * q = y) (hv : s * t * r = v) : y - l * x = s * t * b := by
  have hu : IsUnit (x - t * u) := isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩
  apply hu.mul_left_inj.mp
  have hb : b * (x - t * u) = t * x * r - q * u := by
    unfold sumDepthIntercept
    rw [mul_assoc, hi, mul_one]
  linear_combination -x * hl + t * u * hy - t * x * hv - s * t * hb

variable (hxu : IsUnit (x * u))

/-- The output abscissa at the sum of the two input depths. -/
def sumDepthX : R := (b ^ 2 + c3 * b - c6) * ↑hxu.unit⁻¹

local notation "X" => sumDepthX t c3 c6 x u q r i hxu

/-- The sum-depth ordinate retains the original addition convention. -/
def sumDepthY : R := -(l + W.a₁) * X - b - c3

local notation "Y" => sumDepthY W t c3 c6 x u q r i l hxu

/-- Only the extra scale needs cancellation to recover the abscissa factorization. -/
theorem sumDepthX_scale (ht : IsRegular t)
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
theorem sumDepthY_scale (h3 : W.a₃ = s ^ 2 * t * c3)
    (hb : y - l * x = s * t * b)
    (hx : (s ^ 2 * t) * X = W.toAffine.addX (s * x) (s * (t * u)) l) :
    (s ^ 2 * t) * Y = W.toAffine.addY (s * x) (s * (t * u)) (s * y) l := by
  unfold sumDepthY
  simp only [Affine.addY, Affine.negY, Affine.negAddY, h3]
  linear_combination -(l + W.a₁) * hx + s * hb

end FLT.Mazur.WeierstrassDilatation
