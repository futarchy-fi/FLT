/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginPoleBounds
public import FLT.Mazur.WeierstrassOriginIdeal

/-!
# Exact pole orders of the original affine monomials

The weight of x^i y^j is 2i+3j. A nonzero base coefficient, even a nilpotent
one, cannot lower this order. The proof uses the actual local parameter and
its value on the actual zero section, not geometric-point equality.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- A scalar monomial of the original affine coordinates. -/
def originPoleMonomial (r : R) (i j : ℕ) : Coordinate W 2 :=
  algebraMap R _ r * coord W 2 0 ^ i * coord W 2 1 ^ j

/-- Exact numerator of an original affine monomial at its natural weight. -/
theorem originPoleMonomial_numerator (r : R) (i j : ℕ) :
    algebraMap (OriginNeighborhood W) (OriginPuncture W)
      (algebraMap R _ r *
        algebraMap (Coordinate W 1) (OriginNeighborhood W) (originDenominator W) ^ (i + j)) =
      originPunctureAffine W (originPoleMonomial W r i j) *
        originPunctureChart W (coord W 1 0) ^ (2 * i + 3 * j) := by
  have h : originPunctureAffine W (coord W 2 0) ^ i *
      originPunctureAffine W (coord W 2 1) ^ j *
      originPunctureChart W (coord W 1 0) ^ (2 * i + 3 * j) =
        originPunctureChart W (originDenominator W) ^ (i + j) := by
    calc
      _ = (originPunctureAffine W (coord W 2 0) *
          originPunctureChart W (coord W 1 0) ^ 2) ^ i *
          (originPunctureAffine W (coord W 2 1) *
          originPunctureChart W (coord W 1 0) ^ 3) ^ j := by
        simp only [mul_pow, pow_add, pow_mul]
        ring
      _ = _ := by rw [originPunctureAffine_x_pole, originPunctureAffine_y_pole, ← pow_add]
  simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply,
    originPoleMonomial, AlgHom.commutes]
  change algebraMap R _ r * originPunctureChart W (originDenominator W) ^ (i + j) = _
  linear_combination -(algebraMap R (OriginPuncture W) r) * h

/-- Every original scalar monomial extends after multiplication by its weight power. -/
theorem originPoleMonomial_bound (r : R) (i j : ℕ) :
    HasOriginPoleBound W (originPoleMonomial W r i j) (2 * i + 3 * j) :=
  ⟨_, originPoleMonomial_numerator W r i j⟩

/-- A bound strictly below the monomial weight forces its original base coefficient to vanish. -/
theorem originPoleMonomial_lower (r : R) (i j n : ℕ) (hn : n < 2 * i + 3 * j)
    (h : HasOriginPoleBound W (originPoleMonomial W r i j) n) : r = 0 := by
  obtain ⟨b, hb⟩ := h
  have he : b * originCoordinate W 0 ^ (2 * i + 3 * j - n) =
      algebraMap R _ r *
        algebraMap (Coordinate W 1) (OriginNeighborhood W) (originDenominator W) ^ (i + j) := by
    apply originPunctureRestriction_injective W
    calc
      _ = originPunctureAffine W (originPoleMonomial W r i j) *
          originPunctureChart W (coord W 1 0) ^ (2 * i + 3 * j) := by
        rw [map_mul, map_pow, originPuncture_parameter, hb, mul_assoc, ← pow_add,
          Nat.add_sub_of_le hn.le]
      _ = _ := (originPoleMonomial_numerator W r i j).symm
  have heval := congrArg (originEvaluation W) he
  have hpos : 2 * i + 3 * j - n ≠ 0 := by omega
  simpa only [map_mul, map_pow, originEvaluation_x, zero_pow hpos, mul_zero,
    AlgHom.commutes, originEvaluation_restrict, originDenominator_at_zero, one_pow, mul_one,
    Algebra.algebraMap_self, RingHom.id_apply]
    using heval.symm

/-- The weight is the exact pole order for every nonzero original scalar coefficient. -/
theorem originPoleMonomial_bound_iff (r : R) (i j n : ℕ) :
    HasOriginPoleBound W (originPoleMonomial W r i j) n ↔ r = 0 ∨ 2 * i + 3 * j ≤ n := by
  constructor
  · intro h
    by_cases hn : 2 * i + 3 * j ≤ n
    · exact Or.inr hn
    · exact Or.inl (originPoleMonomial_lower W r i j n (Nat.lt_of_not_ge hn) h)
  · rintro (rfl | hn)
    · exact ⟨0, by simp [originPoleMonomial]⟩
    · exact originPole_mono W _ hn (originPoleMonomial_bound W r i j)

end FLT.Mazur.WeierstrassIntegralChart
