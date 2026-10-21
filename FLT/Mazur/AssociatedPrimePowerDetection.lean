/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# Power detection at associated primes

An element of a module over a Noetherian ring is zero if, at every associated
prime, some scalar outside that prime kills a power multiple of the element.
The scalar and exponent may vary with the prime. Embedded primes are retained,
so this detects nilpotent coefficients as well as reduced ones.
-/

@[expose] public section
namespace FLT.Mazur.AssociatedPrimePowerDetection
variable {R M : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M]

/-- Associated primes detect elements annihilated by locally invertible powers. -/
theorem eq_zero_of_associated_powers (z : M)
    (h : ∀ P ∈ associatedPrimes R M,
      ∃ a : R, a ∉ P ∧ ∃ k : ℕ, a ^ k • z = 0) : z = 0 := by
  by_contra hz
  obtain ⟨P, hP, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R z hz
  obtain ⟨a, ha, k, hk⟩ := h P hP
  have hmem : a ^ k ∈ P := hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact hk)
  exact ha (hP.isPrime.mem_of_pow_mem k hmem)

/-- Different denominators at the associated primes detect an entire submodule. -/
theorem eq_bot_of_associated_powers (N : Submodule R M)
    (h : ∀ P ∈ associatedPrimes R M,
      ∃ a : R, a ∉ P ∧ ∀ z ∈ N, ∃ k : ℕ, a ^ k • z = 0) : N = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  apply eq_zero_of_associated_powers (R := R) z
  intro P hP
  obtain ⟨a, ha, hk⟩ := h P hP
  exact ⟨a, ha, hk z hz⟩

end FLT.Mazur.AssociatedPrimePowerDetection
