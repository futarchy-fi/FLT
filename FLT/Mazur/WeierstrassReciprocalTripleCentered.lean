/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalTripleNumerators

/-!
# Centered homogeneous triple-output comparison

The reciprocal outer outputs are proportional by the cube of an explicit unit.
The proof works over arbitrary commutative rings, including at infinity.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralAddition

variable {R : Type*} [CommRing R]

/-- The complete centered homogeneous outputs agree up to their explicit cubic scale. -/
theorem reciprocal_triple_centered_coordinates {a b c x z u v l m r s : R}
    (hu : u = l ^ 2 + b * l - a - x)
    (hv : v = m ^ 2 + b * m - a - z)
    (hn : r * (-(l + b) * u - c - m * z) = u - z)
    (ht : (l - m) * (1 + (l + b) * r) = (x - z) * r)
    (hs : s - r + (l - m) * r * s = 0) :
    let q := 1 + b * r - (a + u + z) * r ^ 2
    let p := 1 + b * s - (a + x + v) * s ^ 2
    let t := 1 + (l - m) * r
    r * q = t ^ 3 * (s * p) ∧
      -(1 + b * r) * q + (1 + (l + b) * r) * u * r ^ 2 =
        t ^ 3 * (-(1 + b * s) * p + x * s ^ 2 - (c + l * x) * s ^ 3) ∧
      r ^ 3 = t ^ 3 * s ^ 3 := by
  dsimp only
  let t := 1 + (l - m) * r
  let q := 1 + b * r - (a + u + z) * r ^ 2
  let p := 1 + b * s - (a + x + v) * s ^ 2
  have hts : t * s = r := reciprocal_triple_scale_slope hs
  have hq : q = (1 + (l + b) * r) * (1 - m * r) :=
    reciprocal_triple_left_numerator hu ht
  have hp : t ^ 2 * p = q := by
    exact (reciprocal_numerator_scale hts).trans
      ((reciprocal_triple_right_numerator hv ht).trans hq.symm)
  change r * q = t ^ 3 * (s * p) ∧ _ ∧ _
  constructor
  · calc
      r * q = (t * s) * (t ^ 2 * p) := by rw [hts, hp]
      _ = t ^ 3 * (s * p) := by ring
  constructor
  · change -(1 + b * r) * q + (1 + (l + b) * r) * u * r ^ 2 =
        t ^ 3 * (-(1 + b * s) * p + x * s ^ 2 - (c + l * x) * s ^ 3)
    rw [reciprocal_triple_ordinate hq ht hn]
    change -(t + b * r) * q + x * r ^ 2 * t - (c + l * x) * r ^ 3 = _
    calc
      _ = -(t + b * (t * s)) * (t ^ 2 * p) +
          x * (t * s) ^ 2 * t - (c + l * x) * (t * s) ^ 3 := by rw [hts, hp]
      _ = _ := by ring
  · exact (reciprocal_cube_scale hts).symm

end FLT.Mazur.WeierstrassIntegralAddition
