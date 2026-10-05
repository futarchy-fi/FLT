/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticWeightedScaling
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Unit coefficients of a short equation give semistable invariants

When two and three are units, a short equation with either a₄ or a₆ a
unit has unit discriminant or unit c₄. These are the invariant tests needed
after ramified weighted scaling. The scaling exponents can always be
cleared by a fourth or sixth root of the base uniformizer.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A unit coefficient in short normal form prevents additive special-fiber invariants. -/
theorem short_unit_discriminant_or_c₄ (W : WeierstrassCurve R) [W.IsShortNF]
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (h : IsUnit W.a₄ ∨ IsUnit W.a₆) : IsUnit W.Δ ∨ IsUnit W.c₄ := by
  have h16 : IsUnit (16 : R) := by convert h2.pow 4 using 1; norm_num
  have h27 : IsUnit (27 : R) := by convert h3.pow 3 using 1; norm_num
  have h48 : IsUnit (48 : R) := by convert (h2.pow 4).mul h3 using 1; norm_num
  by_cases h4 : IsUnit W.a₄
  · right
    rw [c₄_of_isShortNF]
    exact h48.neg.mul h4
  · have h6 : IsUnit W.a₆ := h.resolve_left h4
    left
    have hz : residue R W.a₄ = 0 := by
      by_contra hz
      exact h4 ((residue_ne_zero_iff_isUnit _).mp hz)
    rw [← residue_ne_zero_iff_isUnit, Δ_of_isShortNF]
    simp only [map_mul, map_add, map_pow, map_neg, hz,
      zero_pow (by decide : 3 ≠ 0), mul_zero, zero_add]
    exact mul_ne_zero (neg_ne_zero.mpr ((residue_ne_zero_iff_isUnit _).mpr h16))
      (mul_ne_zero ((residue_ne_zero_iff_isUnit _).mpr h27)
        (pow_ne_zero 2 ((residue_ne_zero_iff_isUnit _).mpr h6)))

/-- Fourth or sixth root ramification clears the smaller of the two weighted coefficient depths. -/
theorem short_scaling_exponents (a b : ℕ) :
    ∃ e m : ℕ, (e = 4 ∨ e = 6) ∧ 4 * m ≤ e * a ∧ 6 * m ≤ e * b ∧
      (4 * m = e * a ∨ 6 * m = e * b) := by
  by_cases h : 3 * a ≤ 2 * b
  · exact ⟨4, a, Or.inl rfl, le_rfl, by omega, Or.inl rfl⟩
  · exact ⟨6, b, Or.inr rfl, by omega, le_rfl, Or.inr rfl⟩

end FLT.Mazur
