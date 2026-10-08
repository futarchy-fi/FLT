/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleSlopeAlgebra

/-!
# Reciprocal outer slopes without inverting the output coordinate

When the two inner additions are ordinary, reciprocal outer secants obey a
homogeneous parameter identity. Their slopes differ by an invertible fractional
linear change, even when both slopes vanish or are zero divisors.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- The reciprocal left secant determines the homogeneous triple parameter. -/
theorem reciprocal_triple_left_parameter {a b c x z u v l m r : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hc : x * u - z * v = c * (m - l))
    (hn : r * (-(l + b) * u - c - m * z) = u - z)
    (hd : IsUnit (-(l + b) * u - c - m * z)) :
    (l - m) * (1 + (l + b) * r) = (x - z) * r := by
  apply hd.mul_right_inj.mp
  linear_combination ((l - m) * (l + b) - (x - z)) * hn -
    hc + z * (hu - hv)

/-- Two reciprocal outer secants satisfy a homogeneous slope comparison. -/
theorem reciprocal_triple_outer_slopes {a b c x z u v l m r s : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hn : r * (-(l + b) * u - c - m * z) = u - z)
    (ho : s * (l * x + (m + b) * v + c) = x - v)
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r)
    (he : IsUnit (l * x + (m + b) * v + c)) :
    s - r + (l - m) * r * s = 0 := by
  apply he.mul_right_inj.mp
  linear_combination (1 + (l - m) * r) * ho + (l + m + b) * ht + hn +
    (1 + (l + b) * r) * (hu - hv)

/-- The fractional linear slope change has an explicit inverse. -/
theorem reciprocal_triple_scale_inverse {d r s : R}
    (hs : s - r + d * r * s = 0) :
    (1 + d * r) * (1 - d * s) = 1 := by
  linear_combination -d * hs

/-- The comparison scale is invertible without requiring either slope invertible. -/
theorem reciprocal_triple_scale_isUnit {d r s : R}
    (hs : s - r + d * r * s = 0) : IsUnit (1 + d * r) := by
  exact isUnit_iff_exists_inv.mpr ⟨1 - d * s, reciprocal_triple_scale_inverse hs⟩

/-- Multiplying the right reciprocal slope by the comparison scale gives the left. -/
theorem reciprocal_triple_scale_slope {d r s : R}
    (hs : s - r + d * r * s = 0) : (1 + d * r) * s = r := by
  linear_combination hs

end FLT.Mazur.WeierstrassIntegralAddition
