/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Extracting normalized exponents from characters

A character factoring through a surjective prime-field unit character has an
exponent in 1,...,p-1. Trivial characters use p-1. The kernel containment is
an explicit ramification obligation; it is not a Serre-weight evaluation or
a classification of arbitrary inertia representations.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.SerreWeight

/-- Every endomorphism of a finite cyclic group is a power map. -/
theorem cyclicEndomorphism_eq_pow {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    (ψ : C →* C) : ∃ n : ℕ, ∀ x, ψ x = x ^ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := C)
  obtain ⟨n, hn⟩ := hg (ψ g)
  refine ⟨n, fun x ↦ ?_⟩
  obtain ⟨m, rfl⟩ := hg x
  rw [map_pow, ← hn, ← pow_mul, ← pow_mul, Nat.mul_comm]

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
  (θ χ : G →* (ZMod p)ˣ) (hθ : Function.Surjective θ) (hker : θ.ker ≤ χ.ker)

include hθ hker

/-- Kernel containment constructs the factor character and hence an exponent. -/
theorem exists_character_pow : ∃ n : ℕ, ∀ g, χ g = θ g ^ n := by
  let ψ := θ.liftOfSurjective hθ ⟨χ, hker⟩
  obtain ⟨n, hn⟩ := cyclicEndomorphism_eq_pow ψ
  refine ⟨n, fun g ↦ ?_⟩
  have h := hn (θ g)
  simpa [ψ] using h

/-- The normalized exponent is extracted, rather than supplied with an asserted weight. -/
theorem exists_normalized_character_pow :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ p - 1 ∧ ∀ g, χ g = θ g ^ b := by
  obtain ⟨n, hn⟩ := exists_character_pow θ χ hθ hker
  have hp : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  let m := n % (p - 1)
  have hm : m < p - 1 := Nat.mod_lt _ hp
  have hpow (g : G) : θ g ^ m = θ g ^ n := by
    simpa only [m, Nat.card_eq_fintype_card, ZMod.card_units] using pow_mod_card (θ g) n
  by_cases hzero : m = 0
  · refine ⟨p - 1, hp, le_rfl, fun g ↦ ?_⟩
    rw [hn, ← hpow, hzero, pow_zero]
    exact (ZMod.units_pow_card_sub_one_eq_one p (θ g)).symm
  · exact ⟨m, by omega, by omega, fun g ↦ (hn g).trans (hpow g).symm⟩

/-- A selected normalized exponent with the convention that the trivial one is p-1. -/
def normalizedCharacterExponent : ℕ :=
  (exists_normalized_character_pow θ χ hθ hker).choose

/-- The selected exponent lies in the required nonzero interval and recovers the character. -/
theorem normalizedCharacterExponent_spec :
    1 ≤ normalizedCharacterExponent θ χ hθ hker ∧
      normalizedCharacterExponent θ χ hθ hker ≤ p - 1 ∧
      ∀ g, χ g = θ g ^ normalizedCharacterExponent θ χ hθ hker :=
  (exists_normalized_character_pow θ χ hθ hker).choose_spec

/-- In this interval, the trivial character has exponent p-1, not zero. -/
theorem normalizedCharacterExponent_eq_card_sub_one_iff :
    normalizedCharacterExponent θ χ hθ hker = p - 1 ↔ χ = 1 := by
  obtain ⟨hb, hb', he⟩ := normalizedCharacterExponent_spec θ χ hθ hker
  constructor
  · intro h
    apply MonoidHom.ext
    intro g
    rw [he, h]
    exact ZMod.units_pow_card_sub_one_eq_one p (θ g)
  · intro h
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
    obtain ⟨g, hg⟩ := hθ u
    have hp : u ^ normalizedCharacterExponent θ χ hθ hker = 1 := by
      rw [← hg, ← he, h]; rfl
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hu, Nat.card_eq_fintype_card, ZMod.card_units] at hd
    exact le_antisymm hb' (Nat.le_of_dvd (by omega) hd)

end GaloisRepresentation.SerreWeight
