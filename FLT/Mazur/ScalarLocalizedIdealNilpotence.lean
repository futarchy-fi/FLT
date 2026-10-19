/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIdealLocalizationDenominators
public import FLT.Mazur.OriginalScalarFiberRadical

/-!
# Full ideal nilpotence over an original scalar prime

Localizing only at scalar denominators retains all product primes whose
contractions are contained in the scalar prime. Vanishing at those primes
supplies one original scalar denominator annihilating an entire ideal power.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (I : Ideal B) (P : Ideal R) [P.IsPrime]
local notation "S" => P.primeCompl.map s
local notation "L" => Localization S
local notation "l" => algebraMap B L

/-- The contraction of every prime in the full scalar localization lies below its center. -/
theorem localized_prime_comap_le (Q : Ideal L) [Q.IsPrime] :
    (Q.comap l).comap s ≤ P := by
  intro r hr
  by_contra hp
  have hu : IsUnit (l (s r)) :=
    IsLocalization.map_units (M := S) L ⟨s r, ⟨r, hp, rfl⟩⟩
  exact (show Q.IsPrime from inferInstance).ne_top (Q.eq_top_of_isUnit_mem hr hu)

/-- All primes with contraction below the center survive scalar localization. -/
theorem prime_disjoint_of_comap_le (Q : Ideal B) (hQ : Q.comap s ≤ P) :
    Disjoint (S : Set B) (Q : Set B) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨r, hr, rfl⟩ h
  exact hr (hQ h)

/-- Nilpotence in the full scalar localization tests every generizing original product prime. -/
theorem nilpotent_iff_primes (hI : I.FG) :
    IsNilpotent (I.map l) ↔
      ∀ Q : PrimeSpectrum B, Q.asIdeal.comap s ≤ P → I ≤ Q.asIdeal := by
  rw [(hI.map l).isNilpotent_iff_le_nilradical]
  constructor
  · intro h Q hQ
    have hd := prime_disjoint_of_comap_le s P Q.asIdeal hQ
    let _ := IsLocalization.isPrime_of_isPrime_disjoint S L Q.asIdeal Q.isPrime hd
    have hn : nilradical L ≤ Q.asIdeal.map l :=
      (show (Q.asIdeal.map l).IsPrime from inferInstance).radical_le_iff.mpr bot_le
    have he := IsLocalization.under_map_of_isPrime_disjoint S L Q.isPrime hd
    intro x hx
    have hm := hn (h (Ideal.mem_map_of_mem l hx))
    exact he ▸ hm
  · intro h
    rw [nilradical, Ideal.radical_eq_sInf]
    apply le_sInf
    intro Q hQ
    let _ := hQ.2
    apply Ideal.map_le_iff_le_comap.mpr
    exact h (PrimeSpectrum.comap l ⟨Q, hQ.2⟩) (localized_prime_comap_le s P Q)

/-- Minimal original components suffice, including components with strictly smaller centers. -/
theorem nilpotent_iff_components (hI : I.FG) :
    IsNilpotent (I.map l) ↔
      ∀ Q : minimalPrimes B, Q.val.comap s ≤ P → I ≤ Q.val := by
  rw [nilpotent_iff_primes s I P hI]
  constructor
  · intro h Q hQ
    exact h ⟨Q.val, Q.property.1.1⟩ hQ
  · intro h Q hQ
    obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le
      (show (⊥ : Ideal B) ≤ Q.asIdeal from bot_le)
    exact (h ⟨q, hq⟩ ((Ideal.comap_mono hle).trans hQ)).trans hle

/-- Full scalar-local nilpotence supplies a scalar outside the specified original prime. -/
theorem nilpotent_iff_scalar_annihilator (hI : I.FG) :
    IsNilpotent (I.map l) ↔
      ∃ k : ℕ, ∃ r : R, r ∉ P ∧ s r ∈ (I ^ k).annihilator := by
  constructor
  · intro h
    obtain ⟨k, u, hu⟩ :=
      FiniteIdealLocalizationDenominators.exists_power_annihilator I hI S h
    obtain ⟨r, hr, he⟩ := u.property
    exact ⟨k, r, hr, he ▸ hu⟩
  · rintro ⟨k, r, hr, ha⟩
    refine ⟨k, ?_⟩
    change (I.map l) ^ k = ⊥
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    apply (IsLocalization.map_eq_zero_iff S L x).mpr
    exact ⟨⟨s r, ⟨r, hr, rfl⟩⟩, Submodule.mem_annihilator.mp ha x hx⟩

/-- A single scalar neighborhood preserves all coefficients while killing the full test power. -/
theorem exists_scalar_neighborhood (hI : I.FG)
    (h : ∀ Q : minimalPrimes B, Q.val.comap s ≤ P → I ≤ Q.val) :
    ∃ (k : ℕ) (r : R), r ∉ P ∧ s r ∈ (I ^ k).annihilator ∧
      (I.map (algebraMap B (Localization.Away (s r)))) ^ k = ⊥ := by
  obtain ⟨k, r, hr, ha⟩ := (nilpotent_iff_scalar_annihilator s I P hI).mp
    ((nilpotent_iff_components s I P hI).mpr h)
  exact ⟨k, r, hr, ha, FiniteIdealLocalizationDenominators.away_power_eq_bot I k (s r) ha⟩

end FLT.Mazur.ScalarLocalizedIdealNilpotence
