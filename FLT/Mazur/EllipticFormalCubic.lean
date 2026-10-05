/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalSecant

/-!
# The cubic cut out by the formal secant

These polynomial identities hold over every commutative ring. The divided-slope
equation supplies the quadratic relation even for a tangent, so no cancellation
of the difference of the two parameters is needed.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R]

/-- Leading coefficient of the line-intersection cubic. -/
def cubicLeading (W : WeierstrassCurve R) (l : R) : R :=
  1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3

/-- Quadratic coefficient of the line-intersection cubic. -/
def cubicQuadratic (W : WeierstrassCurve R) (l n : R) : R :=
  W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n

/-- Linear coefficient of the line-intersection cubic. -/
def cubicLinear (W : WeierstrassCurve R) (l n : R) : R :=
  W.a₁ * n + 2 * W.a₃ * l * n + W.a₄ * n ^ 2 + 3 * W.a₆ * l * n ^ 2 - l

/-- Constant coefficient of the line-intersection cubic. -/
def cubicConstant (W : WeierstrassCurve R) (n : R) : R :=
  W.a₃ * n ^ 2 + W.a₆ * n ^ 3 - n

/-- The line equation converts the chart equation into a cubic in t. -/
theorem equation_line_iff (W : WeierstrassCurve R) (l n t : R) :
    Equation W t (l * t + n) ↔
      cubicLeading W l * t ^ 3 + cubicQuadratic W l n * t ^ 2 +
        cubicLinear W l n * t + cubicConstant W n = 0 := by
  unfold Equation cubicLeading cubicQuadratic cubicLinear cubicConstant
  constructor <;> intro h <;> linear_combination -h

/-- The implicit slope equation supplies the divided cubic relation. -/
theorem cubic_divided_relation (W : WeierstrassCurve R) (l n t v : R)
    (h : l * differenceUnit W t (l * t + n) (l * v + n) =
      secantNumerator W t v (l * v + n)) :
    cubicLeading W l * (t ^ 2 + t * v + v ^ 2) +
      cubicQuadratic W l n * (t + v) + cubicLinear W l n = 0 := by
  unfold differenceUnit secantNumerator at h
  unfold cubicLeading cubicQuadratic cubicLinear
  linear_combination -h

/-- Vieta's third root is a root, using the divided relation rather than cancellation. -/
theorem cubic_third_root (a b c d t v w : R)
    (ht : a * t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hq : a * (t ^ 2 + t * v + v ^ 2) + b * (t + v) + c = 0)
    (hw : a * (w + t + v) + b = 0) :
    a * w ^ 3 + b * w ^ 2 + c * w + d = 0 := by
  linear_combination ht + (w - t) * hq + (w - t) * (w - v) * hw

end FLT.Mazur.FormalInfinity
