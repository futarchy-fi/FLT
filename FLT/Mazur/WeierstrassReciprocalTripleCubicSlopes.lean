/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleSlopes

/-!
# Reciprocal triple slopes with either outer denominator

The reciprocal tangent equations provide the same homogeneous slope identities
as reciprocal secants. Only the selected reversed denominator is canceled.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- Either reciprocal left chart determines the homogeneous triple parameter. -/
theorem reciprocal_triple_left_parameter_of_cubic {a b c d x z u v l m r : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hxu : x * u = d - c * l) (hzv : z * v = d - c * m)
    (hn : r * (-(l + b) * u - c - m * z) = u - z)
    (hnc : r * (u ^ 2 + u * z + z ^ 2 + a * (u + z) + d +
        b * (l + b) * u + b * c) = -(l + b) * u + (m + b) * z)
    (hd : IsUnit (-(l + b) * u - c - m * z) ∨
      IsUnit (u ^ 2 + u * z + z ^ 2 + a * (u + z) + d +
        b * (l + b) * u + b * c)) :
    (l - m) * (1 + (l + b) * r) = (x - z) * r := by
  rcases hd with hd | hd
  · apply reciprocal_triple_left_parameter hu hv _ hn hd
    linear_combination hxu - hzv
  · apply hd.mul_right_inj.mp
    linear_combination ((l - m) * (l + b) - (x - z)) * hnc +
      (m + b) * hxu - (l + b) * hzv +
      (-b * z + l * u - m * u - m * z) * hu + (b * z + l * z) * hv

/-- Either reciprocal right chart gives the same fractional linear slope change. -/
theorem reciprocal_triple_outer_slopes_of_cubic {a b c d x z u v l m r s : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hzv : z * v = d - c * m)
    (hn : r * (-(l + b) * u - c - m * z) = u - z)
    (ho : s * (l * x + (m + b) * v + c) = x - v)
    (hoc : s * (x ^ 2 + x * v + v ^ 2 + a * (x + v) + d - b * l * x) =
      l * x - m * v)
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r)
    (he : IsUnit (l * x + (m + b) * v + c) ∨
      IsUnit (x ^ 2 + x * v + v ^ 2 + a * (x + v) + d - b * l * x)) :
    s - r + (l - m) * r * s = 0 := by
  rcases he with he | he
  · exact reciprocal_triple_outer_slopes hu hv hn ho ht he
  · apply he.mul_right_inj.mp
    linear_combination (1 + (l - m) * r) * hoc +
      (x + m * (b + l + m)) * ht + m * hn + r * hzv +
      m * (1 + (b + l) * r) * hu -
      (r * (x + v) + m * (1 + (b + l) * r)) * hv

end FLT.Mazur.WeierstrassIntegralAddition
