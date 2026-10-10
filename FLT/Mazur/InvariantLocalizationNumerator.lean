/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantLocalizationAction

/-!
# Clearing denominators in invariant principal localizations

A fixed fraction admits a fixed numerator after multiplying numerator and
denominator by one common power. Finiteness of the group supplies that power;
no division by the group order is used, even when the denominator is a zero divisor.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  (r : invariantRing G A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away (r : A) S] [MulSemiringAction G S]
  (he : ∀ (g : G) a, g • algebraMap A S a = algebraMap A S (g • a))

include he in
/-- A fixed fraction has an invariant numerator with a power of the fixed denominator. -/
theorem exists_invariant_numerator (x : S) (hx : ∀ g : G, g • x = x) :
    ∃ (n : ℕ) (a : invariantRing G A),
      x * algebraMap A S (r : A) ^ n = algebraMap A S (a : A) := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (r : A) x
  have hga (g : G) : algebraMap A S (g • a) = algebraMap A S a := by
    rw [← he, ← ha, smul_mul', smul_pow', hx, he, r.property g]
  choose m hm using fun g ↦ IsLocalization.Away.exists_of_eq (r : A) (hga g)
  let N := Finset.univ.sup m
  have hN (g : G) : m g ≤ N := Finset.le_sup (f := m) (Finset.mem_univ g)
  have hb : ∀ g : G, g • ((r : A) ^ N * a) = (r : A) ^ N * a := by
    intro g
    rw [smul_mul', smul_pow', r.property g]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hN g)
    calc
      (r : A) ^ N * (g • a) = (r : A) ^ k * ((r : A) ^ m g * (g • a)) := by
        rw [hk, pow_add]
        ring
      _ = (r : A) ^ k * ((r : A) ^ m g * a) := by rw [hm g]
      _ = (r : A) ^ N * a := by rw [hk, pow_add]; ring
  refine ⟨n + N, ⟨(r : A) ^ N * a, hb⟩, ?_⟩
  change x * algebraMap A S (r : A) ^ (n + N) =
    algebraMap A S ((r : A) ^ N * a)
  rw [map_mul, map_pow, pow_add, ← mul_assoc, ha, mul_comm]

end FLT.Mazur.FiniteGroupQuotient
