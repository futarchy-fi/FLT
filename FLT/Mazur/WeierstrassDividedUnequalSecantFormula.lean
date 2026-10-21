/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantFormula

/-!
# Secant cancellation between unequal divided depths

If the second input has an additional scale t, the original secant output
has a factor t in both coordinates. The quotient uses only the divided
abscissa difference as denominator; neither scale is inverted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t c3 c4 c6 x y u v : R)

/-- The numerator remaining after cancelling the unequal-depth scale. -/
def unequalSecantNumerator : R :=
  -2 * y * v - W.a₁ * (y * u + x * v) + 2 * W.a₂ * x * u + s * x ^ 2 * u +
    c4 * x - c3 * y + t * (s * x * u ^ 2 + c4 * u + 2 * c6 - c3 * v)

variable (i l : R)
local notation "N" => unequalSecantNumerator W s t c3 c4 c6 x y u v

/-- The output abscissa divided by the extra input scale. -/
def unequalSecantX : R := N * i ^ 2

local notation "X" => unequalSecantX W s t c3 c4 c6 x y u v i

/-- The corresponding divided ordinate, using the same single denominator. -/
def unequalSecantY : R := -(l + W.a₁) * X + s * ((y * u - x * v) * i - c3)

local notation "Y" => unequalSecantY W s t c3 c4 c6 x y u v i l

/-- The abscissa factorization holds over arbitrary commutative rings. -/
theorem unequalSecantX_scale
    (hi : i * (x - t * u) = 1) (hl : l * (x - t * u) = y - t * v)
    (h₁ : y ^ 2 + (W.a₁ * x + t * c3) * y =
      s * x ^ 3 + W.a₂ * x ^ 2 + (t * c4) * x + t ^ 2 * c6)
    (h₂ : v ^ 2 + (W.a₁ * u + c3) * v =
      (s * t) * u ^ 3 + W.a₂ * u ^ 2 + c4 * u + c6) :
    t * X = W.toAffine.addX (s * x) (s * (t * u)) l := by
  have hu : IsUnit (x - t * u) := isUnit_iff_exists_inv.mpr ⟨i, by rwa [mul_comm]⟩
  apply (hu.pow 2).mul_right_inj.mp
  have hinv : (x - t * u) ^ 2 * (t * X) = t * N := by
    unfold unequalSecantX
    calc
      _ = t * N * (i * (x - t * u)) ^ 2 := by ring
      _ = _ := by rw [hi]; ring
  rw [hinv]
  simp only [Affine.addX]
  unfold unequalSecantNumerator
  linear_combination -h₁ - t ^ 2 * h₂ -
    (l * (x - t * u) + (y - t * v) + W.a₁ * (x - t * u)) * hl

/-- The ordinate has the same extra scale, without cancelling it. -/
theorem unequalSecantY_scale
    (hi : i * (x - t * u) = 1) (hl : l * (x - t * u) = y - t * v)
    (h3 : W.a₃ = s * t * c3)
    (hx : t * X = W.toAffine.addX (s * x) (s * (t * u)) l) :
    t * Y = W.toAffine.addY (s * x) (s * (t * u)) (s * y) l := by
  have hc : (l * x - y) * (x - t * u) = t * (y * u - x * v) := by
    linear_combination x * hl
  have hci : l * x - y = t * ((y * u - x * v) * i) := by
    calc
      _ = ((l * x - y) * (x - t * u)) * i := by
        rw [mul_assoc, mul_comm (x - t * u), hi, mul_one]
      _ = _ := by rw [hc]; ring
  unfold unequalSecantY
  simp only [Affine.addY, Affine.negY, Affine.negAddY, h3]
  linear_combination -(l + W.a₁) * hx - s * hci

end FLT.Mazur.WeierstrassDilatation
