/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleSlopes

/-!
# Homogeneous numerators for reciprocal triple addition

The two centered abscissa numerators have a common factorization after the
invertible slope change. The ordinate comparison is polynomial and cancels
neither a slope nor an output coordinate.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- The left centered abscissa numerator factors without dividing by the slope. -/
theorem reciprocal_triple_left_numerator {a b x z u l m r : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r) :
    1 + b * r - (a + u + z) * r ^ 2 =
      (1 + (l + b) * r) * (1 - m * r) := by
  linear_combination -r ^ 2 * hu - r * ht

/-- The right numerator has the same factorization after homogenizing the slope change. -/
theorem reciprocal_triple_right_numerator {a b x z v l m r : R}
    (hv : v = m ^ 2 + b * m - a - z)
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r) :
    (1 + (l - m) * r) ^ 2 + b * r * (1 + (l - m) * r) -
        (a + x + v) * r ^ 2 = (1 + (l + b) * r) * (1 - m * r) := by
  linear_combination -r ^ 2 * hv + r * ht

/-- Centered ordinate numerators agree at the common abscissa numerator. -/
theorem reciprocal_triple_ordinate {b c x z u l m r q : R}
    (hq : q = (1 + (l + b) * r) * (1 - m * r))
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r)
    (hn : r * (-(l + b) * u - c - m * z) = u - z) :
    -(1 + b * r) * q + (1 + (l + b) * r) * u * r ^ 2 =
      -(1 + (l - m) * r + b * r) * q +
        x * r ^ 2 * (1 + (l - m) * r) - (c + l * x) * r ^ 3 := by
  linear_combination (l - m) * r * hq + (1 - m * r) * r * ht - r ^ 2 * hn

/-- Homogenizing a reciprocal quadratic numerator commutes with slope scaling. -/
theorem reciprocal_numerator_scale {a b r s t : R} (hs : t * s = r) :
    t ^ 2 * (1 + b * s - a * s ^ 2) = t ^ 2 + b * r * t - a * r ^ 2 := by
  calc
    _ = t ^ 2 + b * (t * s) * t - a * (t * s) ^ 2 := by ring
    _ = _ := by rw [hs]

/-- Cubic homogeneous z-coordinates have the same comparison scale. -/
theorem reciprocal_cube_scale {r s t : R} (hs : t * s = r) :
    t ^ 3 * s ^ 3 = r ^ 3 := by rw [← mul_pow, hs]

end FLT.Mazur.WeierstrassIntegralAddition
