/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalCubic
public import FLT.Mazur.EllipticFormalNegation
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

/-!
# Comparison of the chart secant with projective addition

The projective secant formula is a scalar multiple of the negative third
intersection. The scalar is (t-v)^3 times the leading cubic coefficient.
These polynomial identities hold over every commutative ring.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The projective X formula agrees with the Vieta third parameter. -/
theorem secant_projectiveX (l n t v w : R)
    (ht : cubicLeading W l * t ^ 3 + cubicQuadratic W l n * t ^ 2 +
      cubicLinear W l n * t + cubicConstant W n = 0)
    (hq : cubicLeading W l * (t ^ 2 + t * v + v ^ 2) +
      cubicQuadratic W l n * (t + v) + cubicLinear W l n = 0)
    (hw : cubicLeading W l * (w + t + v) + cubicQuadratic W l n = 0) :
    W.toProjective.addX ![t, -1, l * t + n] ![v, -1, l * v + n] =
      (t - v) ^ 3 * cubicLeading W l * w := by
  simp only [WeierstrassCurve.Projective.addX, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  unfold cubicLeading cubicQuadratic cubicLinear cubicConstant at *
  linear_combination (t - v) * (3 * ht + (v - 2 * t) * hq) - (t - v) ^ 3 * hw

/-- The projective Y formula before negation gives the secant's scale. -/
theorem secant_projectiveNegY (l n t v : R)
    (hq : cubicLeading W l * (t ^ 2 + t * v + v ^ 2) +
      cubicQuadratic W l n * (t + v) + cubicLinear W l n = 0) :
    W.toProjective.negAddY ![t, -1, l * t + n] ![v, -1, l * v + n] =
      -((t - v) ^ 3 * cubicLeading W l) := by
  simp only [WeierstrassCurve.Projective.negAddY, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  unfold cubicLeading cubicQuadratic cubicLinear at *
  linear_combination (t - v) * hq

/-- The projective third intersection lies on the chart secant line. -/
theorem secant_projectiveLine (l n t v : R) :
    W.toProjective.addZ ![t, -1, l * t + n] ![v, -1, l * v + n] =
      l * W.toProjective.addX ![t, -1, l * t + n] ![v, -1, l * v + n] -
        n * W.toProjective.negAddY ![t, -1, l * t + n] ![v, -1, l * v + n] := by
  simp only [WeierstrassCurve.Projective.addZ, WeierstrassCurve.Projective.addX,
    WeierstrassCurve.Projective.negAddY, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The full projective secant output is the scaled negative third intersection. -/
theorem secant_projectiveXYZ (l n t v w : R)
    (ht : cubicLeading W l * t ^ 3 + cubicQuadratic W l n * t ^ 2 +
      cubicLinear W l n * t + cubicConstant W n = 0)
    (hq : cubicLeading W l * (t ^ 2 + t * v + v ^ 2) +
      cubicQuadratic W l n * (t + v) + cubicLinear W l n = 0)
    (hw : cubicLeading W l * (w + t + v) + cubicQuadratic W l n = 0) :
    W.toProjective.addXYZ ![t, -1, l * t + n] ![v, -1, l * v + n] =
      ((t - v) ^ 3 * cubicLeading W l) •
        ![w, negationDenominator W w (l * w + n), l * w + n] := by
  have hx := secant_projectiveX W l n t v w ht hq hw
  have hy := secant_projectiveNegY W l n t v hq
  have hz := secant_projectiveLine W l n t v
  rw [hx, hy] at hz
  rw [WeierstrassCurve.Projective.smul_fin3]
  change ![_, _, _] = ![((t - v) ^ 3 * cubicLeading W l) * w,
    ((t - v) ^ 3 * cubicLeading W l) * negationDenominator W w (l * w + n),
    ((t - v) ^ 3 * cubicLeading W l) * (l * w + n)]
  simp only [WeierstrassCurve.Projective.addY, WeierstrassCurve.Projective.negY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hx, hy, hz, negationDenominator]
  congr 1
  ring_nf

end FLT.Mazur.FormalInfinity
