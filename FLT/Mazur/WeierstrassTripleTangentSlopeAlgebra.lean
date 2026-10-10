/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleSlopeAlgebra

/-!
# Triple slope identities with tangent outer denominators

The outer divided differences replace cancellation of the outer x differences.
Each side may independently use its secant or tangent unit. These identities
supply the missing scalar step for ordinary tangent outer charts.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- The left outer slope determines the triple parameter on either ordinary domain. -/
theorem triple_left_parameter {a b c d x z u v l m n : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hxu : x * u = d - c * l) (hzv : z * v = d - c * m)
    (hn : n * (u - z) = -(l + b) * u - c - m * z)
    (hnc : n * (-(l + b) * u + (m + b) * z) =
      u ^ 2 + u * z + z ^ 2 + a * (u + z) + d + b * (l + b) * u + b * c)
    (hd : IsUnit (u - z) ∨ IsUnit (-(l + b) * u + (m + b) * z)) :
    (l - m) * (n + l + b) = x - z := by
  rcases hd with hd | hd
  · apply hd.mul_right_inj.mp
    linear_combination (l - m) * hn - hxu + hzv + z * (hu - hv)
  · apply hd.mul_right_inj.mp
    linear_combination (l - m) * hnc + (m + b) * hxu - (l + b) * hzv +
      (-b * z + l * u - m * u - m * z) * hu + (b * z + l * z) * hv

/-- The right outer slope agrees with the left parameter on either ordinary domain. -/
theorem triple_outer_slopes {a b c d x z u v l m n o : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hzv : z * v = d - c * m)
    (hn : n * (u - z) = -(l + b) * u - c - m * z)
    (ho : o * (x - v) = l * x + (m + b) * v + c)
    (hoc : o * (l * x - m * v) =
      x ^ 2 + x * v + v ^ 2 + a * (x + v) + d - b * l * x)
    (ht : (l - m) * (n + l + b) = x - z)
    (he : IsUnit (x - v) ∨ IsUnit (l * x - m * v)) :
    n + l = o + m := by
  rcases he with he | he
  · apply he.mul_right_inj.mp
    linear_combination (l + m + b) * ht - hn - ho + (n + l + b) * (hu - hv)
  · apply he.mul_right_inj.mp
    linear_combination (x + m * (b + l + m)) * ht - m * hn + hzv +
      m * (b + l + n) * hu - (x + m * (b + l + n) + v) * hv - hoc

end FLT.Mazur.WeierstrassIntegralAddition
