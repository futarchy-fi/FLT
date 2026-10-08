/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleCubicSlopes
public import FLT.Mazur.WeierstrassTripleTangentSlopeAlgebra

/-!
# Mixed ordinary and reciprocal outer slopes

An ordinary outer law forces the opposite reciprocal slope to be a unit.
The inverse is explicit; no field, reducedness, or output-unit assumption is needed.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- An ordinary left outer law supplies the inverse of the right reciprocal slope. -/
theorem mixed_triple_right_inverse {a b c d x z u v l m n s : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hzv : z * v = d - c * m)
    (hn : n * (u - z) = -(l + b) * u - c - m * z)
    (ho : s * (l * x + (m + b) * v + c) = x - v)
    (hoc : s * (x ^ 2 + x * v + v ^ 2 + a * (x + v) + d - b * l * x) =
      l * x - m * v)
    (ht : (l - m) * (n + l + b) = x - z)
    (he : IsUnit (l * x + (m + b) * v + c) ∨
      IsUnit (x ^ 2 + x * v + v ^ 2 + a * (x + v) + d - b * l * x)) :
    s * (n + l - m) = 1 := by
  rcases he with he | he
  · apply he.mul_right_inj.mp
    linear_combination (n + l - m) * ho + (l + m + b) * ht - hn +
      (n + l + b) * (hu - hv)
  · apply he.mul_right_inj.mp
    linear_combination (n + l - m) * hoc +
      (x + m * (b + l + m)) * ht - m * hn + hzv +
      m * (b + l + n) * hu - (x + m * (b + l + n) + v) * hv

/-- An ordinary right outer law supplies the inverse of the left reciprocal slope. -/
theorem mixed_triple_left_inverse {a b c d x z u v l m r o : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hzv : z * v = d - c * m)
    (hn : r * (-(l + b) * u - c - m * z) = u - z)
    (ho : o * (x - v) = l * x + (m + b) * v + c)
    (hoc : o * (l * x - m * v) =
      x ^ 2 + x * v + v ^ 2 + a * (x + v) + d - b * l * x)
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r)
    (he : IsUnit (x - v) ∨ IsUnit (l * x - m * v)) :
    r * (o + m - l) = 1 := by
  rcases he with he | he
  · apply he.mul_right_inj.mp
    linear_combination r * ho - (l + m + b) * ht - hn -
      (1 + (l + b) * r) * (hu - hv)
  · apply he.mul_right_inj.mp
    linear_combination r * hoc -
      (x + m * (b + l + m)) * ht - m * hn - r * hzv -
      m * (1 + (b + l) * r) * hu +
      (r * (x + v) + m * (1 + (b + l) * r)) * hv

end FLT.Mazur.WeierstrassIntegralAddition
