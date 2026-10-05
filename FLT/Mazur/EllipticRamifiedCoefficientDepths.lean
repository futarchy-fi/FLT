/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticShortWeightedModel

/-!
# Coefficient depths after ramification

Adjoining a uniformizer root multiplies every coefficient valuation by
the ramification degree. The fourth/sixth-power selection also handles
zero coefficients, whose additive valuation is infinite.
-/

@[expose] public section

namespace FLT.Mazur

open IsDiscreteValuationRing

/-- Ramification multiplies every additive valuation, including that of zero. -/
theorem addVal_map_of_uniformizer {R S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) {π : R} (hπ : Irreducible π) {e : ℕ} (he : 0 < e)
    (hval : addVal S (f π) = (e : ℕ∞)) (a : R) :
    addVal S (f a) = e • addVal R a := by
  by_cases ha : a = 0
  · simp [ha, nsmul_eq_mul, Nat.ne_of_gt he]
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, addVal_mul, addVal_pow,
      addVal_eq_zero_iff.mpr (u.isUnit.map f), zero_add, hval, addVal_def' u hπ n]
    simp [nsmul_eq_mul, mul_comm]

/-- Choose a fourth or sixth root so that integral weighted scaling reaches a unit coefficient. -/
theorem short_ramified_depths (a b : ℕ∞) (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    ∃ e m : ℕ, (e = 4 ∨ e = 6) ∧ (4 * m : ℕ) ≤ e • a ∧
      (6 * m : ℕ) ≤ e • b ∧ (e • a = (4 * m : ℕ) ∨ e • b = (6 * m : ℕ)) := by
  by_cases ha : a = ⊤
  · have hb := h.resolve_left (by simp only [ha, ne_self_iff_false, not_false_eq_true])
    lift b to ℕ using hb with b
    refine ⟨6, b, Or.inr rfl, ?_, ?_, Or.inr ?_⟩
    · simp [ha]
    · simp [nsmul_eq_mul, Nat.cast_mul]
    · simp [nsmul_eq_mul, Nat.cast_mul]
  · lift a to ℕ using ha with a
    by_cases hb : b = ⊤
    · refine ⟨4, a, Or.inl rfl, ?_, ?_, Or.inl ?_⟩
      · simp [nsmul_eq_mul, Nat.cast_mul]
      · simp [hb]
      · simp [nsmul_eq_mul, Nat.cast_mul]
    · lift b to ℕ using hb with b
      obtain ⟨e, m, he, h4, h6, hs⟩ := short_scaling_exponents a b
      refine ⟨e, m, he, ?_, ?_, ?_⟩
      · simpa only [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le] using h4
      · simpa only [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_le] using h6
      · rcases hs with hs | hs
        · apply Or.inl
          simpa only [nsmul_eq_mul, ← Nat.cast_mul] using
            congrArg (Nat.cast : ℕ → ℕ∞) hs.symm
        · apply Or.inr
          simpa only [nsmul_eq_mul, ← Nat.cast_mul] using
            congrArg (Nat.cast : ℕ → ℕ∞) hs.symm

end FLT.Mazur
