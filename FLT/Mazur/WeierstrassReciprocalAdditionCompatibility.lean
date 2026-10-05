/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVerticalAdditionCharts

/-!
# Compatibility of reciprocal and ordinary addition formulas

Where the slope is invertible, the reciprocal formula is the ordinary affine
formula scaled by the cube of its inverse. At reciprocal slope zero, the
normalized chart map takes the value infinity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralAddition

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Ordinary and reciprocal denominator relations determine inverse slopes on an overlap. -/
theorem inverse_slopes_of_relations {d n l m : R} (hd : IsUnit d)
    (hl : l * d = n) (hm : m * n = d) : m * l = 1 := by
  apply hd.mul_left_inj.mp
  linear_combination m * hl + hm

/-- The reciprocal numerator agrees with the usual x-coordinate after scaling. -/
theorem reciprocalH_eq_scaled_addX (x₁ x₂ l m : R) (hm : m * l = 1) :
    m ^ 2 * W.toAffine.addX x₁ x₂ l = reciprocalH W x₁ x₂ m := by
  simp only [Affine.addX, reciprocalH]
  linear_combination (m * l + 1 + W.a₁ * m) * hm

/-- Reciprocal and ordinary addition give the same homogeneous coordinates up to scaling. -/
theorem reciprocalXYZ_eq_scaled_add (x₁ x₂ y₁ l m : R) (hm : m * l = 1) :
    reciprocalXYZ W x₁ x₂ y₁ m =
      m ^ 3 • ![W.toAffine.addX x₁ x₂ l, W.toAffine.addY x₁ x₂ y₁ l, 1] := by
  have hx := reciprocalH_eq_scaled_addX W x₁ x₂ l m hm
  ext i
  fin_cases i
  · change m * reciprocalH W x₁ x₂ m = m ^ 3 * W.toAffine.addX x₁ x₂ l
    linear_combination -m * hx
  · change -(1 + W.a₁ * m) * reciprocalH W x₁ x₂ m + x₁ * m ^ 2 -
        (y₁ + W.a₃) * m ^ 3 = m ^ 3 * W.toAffine.addY x₁ x₂ y₁ l
    simp only [Affine.addY, Affine.negY, Affine.negAddY]
    linear_combination (m * l + W.a₁ * m) * hx +
      (reciprocalH W x₁ x₂ m - x₁ * m ^ 2) * hm
  · change m ^ 3 = m ^ 3 * 1
    exact (mul_one _).symm

end FLT.Mazur.WeierstrassIntegralAddition

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f : AffineProduct W →ₐ[R] S) (m : S)
  (hl : m * (f (productY₁ W) - f (productY₂ W)) = f (productX₁ W) - f (productX₂ W))
  (hc : m * (f (productX₁ W) ^ 2 + f (productX₁ W) * f (productX₂ W) +
      f (productX₂ W) ^ 2 + algebraMap R S W.a₂ * (f (productX₁ W) + f (productX₂ W)) +
      algebraMap R S W.a₄ - algebraMap R S W.a₁ * f (productY₁ W)) =
    f (productY₁ W) + f (productY₂ W) +
      algebraMap R S W.a₁ * f (productX₂ W) + algebraMap R S W.a₃)

/-- Every specialization with reciprocal slope zero has normalized sum infinity. -/
theorem reciprocalAddition_at_zero {T : Type*} [CommRing T] [Algebra R T]
    (g : ReciprocalTargetOpen W f m →ₐ[R] T)
    (hm : g (reciprocalTargetRestriction W f m m) = 0) (i : Fin 3) :
    g (reciprocalAddition W f m hl hc (coord W 1 i)) = ![0, 1, 0] i := by
  have hy : g (reciprocalTargetRestriction W f m (reciprocalCoordinates W f m 1)) = -1 := by
    change g (reciprocalTargetRestriction W f m
      (-(1 + (W.map (algebraMap R S)).a₁ * m) *
          reciprocalH (W.map (algebraMap R S))
            (f (productX₁ W)) (f (productX₂ W)) m + f (productX₁ W) * m ^ 2 -
        (f (productY₁ W) + (W.map (algebraMap R S)).a₃) * m ^ 3)) = -1
    simp only [reciprocalH, map_sub, map_add, map_mul, map_pow, map_neg, map_one, hm,
      zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero,
      sub_zero, mul_one, neg_mul]
  have hi : g (reciprocalTargetInverse W f m) * -1 = 1 := by
    simpa only [map_mul, map_one, hy] using congrArg g (reciprocalTargetInverse_mul W f m)
  rw [reciprocalAddition_coord, map_mul]
  fin_cases i
  · change g (reciprocalTargetInverse W f m) *
      g (reciprocalTargetRestriction W f m (m * _)) = 0
    rw [map_mul, map_mul, hm, zero_mul, mul_zero]
  · change g (reciprocalTargetInverse W f m) *
      g (reciprocalTargetRestriction W f m (reciprocalCoordinates W f m 1)) = 1
    rw [hy]
    exact hi
  · change g (reciprocalTargetInverse W f m) *
      g (reciprocalTargetRestriction W f m (m ^ 3)) = 0
    rw [map_pow, map_pow, hm, zero_pow (by decide : 3 ≠ 0), mul_zero]

end FLT.Mazur.WeierstrassIntegralChart
