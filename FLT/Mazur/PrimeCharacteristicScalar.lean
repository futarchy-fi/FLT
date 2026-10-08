/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Scalars detecting degrees below the residue characteristic

For 1 < k < p there is an integer scalar m for which m^k - m is a unit in
every ring of characteristic p. This detects the first nonlinear coefficient
of a formal endomorphism commuting with integer multiplication.
-/

@[expose] public section

namespace FLT.Mazur

/-- A nontrivial degree below p is detected by a scalar in the prime field. -/
theorem exists_prime_scalar_pow_sub_unit (p k : ℕ) [Fact p.Prime]
    (hk : 1 < k) (hkp : k < p) (R : Type*) [CommRing R] [CharP R p] :
    ∃ m : ℕ, IsUnit ((m : R) ^ k - m) := by
  have hc : k - 1 < Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
    omega
  obtain ⟨u, hu⟩ := exists_pow_ne_one_of_isCyclic (G := (ZMod p)ˣ)
    (show k - 1 ≠ 0 by omega) hc
  have hpow : (u : ZMod p) ^ k ≠ u := by
    intro h
    apply hu
    apply Units.ext
    have he : (u : ZMod p) ^ (k - 1) * u = 1 * u := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k), one_mul]
      exact h
    exact mul_right_cancel₀ u.ne_zero he
  have hv : IsUnit (((u : ZMod p).val : ZMod p) ^ k - (u : ZMod p).val) := by
    rw [ZMod.natCast_zmod_val]
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hpow)
  refine ⟨(u : ZMod p).val, ?_⟩
  simpa only [map_sub, map_pow, map_natCast] using hv.map (ZMod.castHom (dvd_refl p) R)

end FLT.Mazur
