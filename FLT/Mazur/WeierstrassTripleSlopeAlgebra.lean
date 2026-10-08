/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralAdditionFormula

/-!
# Four ordinary slopes in coordinates centered at the middle input

The inner divided differences imply a cross relation between the intermediate
abscissas. Only the two outer secant denominators are canceled. The resulting
identities control both coordinates of the iterated sums over arbitrary rings.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- Four ordinary slopes satisfy the two identities needed for associativity. -/
theorem triple_slope_identities {a b c x z u v l m n o : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hc : x * u - z * v = c * (m - l))
    (hn : n * (u - z) = -(l + b) * u - c - m * z)
    (ho : o * (x - v) = l * x + (m + b) * v + c)
    (hd : IsUnit (u - z)) (he : IsUnit (x - v)) :
    n + l = o + m ∧ (l - m) * (n + l + b) = x - z := by
  have hsum : (u - z) + (x - v) = (l - m) * (l + m + b) := by
    linear_combination hu - hv
  constructor
  · apply hd.mul_right_inj.mp
    apply he.mul_right_inj.mp
    linear_combination (x - v) * hn - (u - z) * ho -
      (l + m + b) * hc - c * hsum
  · apply hd.mul_right_inj.mp
    linear_combination (l - m) * hn - hc + z * hsum

/-- The common abscissa, centered at the middle input, has a factored expression. -/
theorem triple_left_abscissa {a b x z u l m n : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (ht : (l - m) * (n + l + b) = x - z) :
    n ^ 2 + b * n - a - u - z = (n + l + b) * (n - m) := by
  linear_combination -hu - ht

/-- The right abscissa has the same factorization when the slopes agree. -/
theorem triple_right_abscissa {a b x z v l m n o : R}
    (hv : v = m ^ 2 + b * m - a - z)
    (hs : n + l = o + m)
    (ht : (l - m) * (n + l + b) = x - z) :
    o ^ 2 + b * o - a - x - v = (n + l + b) * (n - m) := by
  linear_combination -hv + ht - (n + o + l - m + b) * hs

/-- The two ordinate expressions agree at the common abscissa. -/
theorem triple_ordinate {b c x z u l m n o q : R}
    (hq : q = (n + l + b) * (n - m))
    (hs : n + l = o + m)
    (ht : (l - m) * (n + l + b) = x - z)
    (hn : n * (u - z) = -(l + b) * u - c - m * z) :
    -(n + b) * q + (n + l + b) * u =
      -(o + b) * q + (o - l) * x - c := by
  linear_combination (l - m) * hq + (x - q) * hs + (n - m) * ht + hn

end FLT.Mazur.WeierstrassIntegralAddition
