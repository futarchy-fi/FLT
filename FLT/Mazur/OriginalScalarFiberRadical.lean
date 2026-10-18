/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Equations detecting the whole original scalar fiber

Vanishing on every prime above the original prime is equivalent to a power
certificate with a denominator outside that prime. Neither integrality nor
finite type is needed, and all equations live in the original target ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalScalarFiberRadical
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (P : Ideal R) [P.IsPrime]
local notation "T" => Localization (P.primeCompl.map s)
local notation "l" => algebraMap B T

/-- A localized prime containing the original scalar ideal has exactly the original center. -/
theorem localized_prime_center (Q : Ideal T) [Q.IsPrime]
    (hQ : (P.map s).map l ≤ Q) : (Q.comap l).comap s = P := by
  apply le_antisymm
  · intro r hr
    by_contra hp
    have hu : IsUnit (l (s r)) :=
      IsLocalization.map_units (M := P.primeCompl.map s) T ⟨s r, ⟨r, hp, rfl⟩⟩
    exact (show Q.IsPrime from inferInstance).ne_top (Q.eq_top_of_isUnit_mem hr hu)
  · exact (Ideal.map_le_iff_le_comap).mp ((Ideal.map_le_iff_le_comap).mp hQ)

/-- Every original fiber prime extends to a prime of the same scalar localization. -/
theorem fiber_prime_disjoint (Q : Ideal B) (hQ : Q.comap s = P) :
    Disjoint (P.primeCompl.map s : Set B) (Q : Set B) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨r, hr, rfl⟩ h
  exact hr (show r ∈ P from hQ ▸ h)

/-- Vanishing at every original fiber prime is exactly membership in the localized radical. -/
theorem forall_fiber_primes_iff_localized_radical (b : B) :
    (∀ Q : PrimeSpectrum B, Q.asIdeal.comap s = P → b ∈ Q.asIdeal) ↔
      l b ∈ ((P.map s).map l).radical := by
  constructor
  · intro h
    rw [Ideal.radical_eq_sInf]
    apply Ideal.mem_sInf.mpr
    intro Q hQ
    let _ := hQ.2
    exact h (PrimeSpectrum.comap l ⟨Q, hQ.2⟩) (localized_prime_center s P Q hQ.1)
  · intro h Q hQ
    have hd := fiber_prime_disjoint s P Q.asIdeal hQ
    let _ := IsLocalization.isPrime_of_isPrime_disjoint
      (P.primeCompl.map s) T Q.asIdeal Q.isPrime hd
    have hle : (P.map s).map l ≤ Q.asIdeal.map l :=
      Ideal.map_mono ((Ideal.map_le_iff_le_comap).mpr hQ.ge)
    have hb : l b ∈ Q.asIdeal.map l :=
      (show (Q.asIdeal.map l).IsPrime from inferInstance).radical_le_iff.mpr hle h
    have he := IsLocalization.under_map_of_isPrime_disjoint
      (P.primeCompl.map s) T Q.isPrime hd
    exact he ▸ hb

/-- A localized radical membership clears to an exact original power equation. -/
theorem localized_radical_iff_power (b : B) :
    l b ∈ ((P.map s).map l).radical ↔
      ∃ (n : ℕ) (r : R), r ∉ P ∧ s r * b ^ n ∈ P.map s := by
  rw [Ideal.mem_radical_iff]
  simp_rw [← map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff
    (P.primeCompl.map s)]
  constructor
  · rintro ⟨n, _, ⟨r, hr, rfl⟩, h⟩
    exact ⟨n, r, hr, h⟩
  · rintro ⟨n, r, hr, h⟩
    exact ⟨n, s r, ⟨r, hr, rfl⟩, h⟩

/-- Whole original scalar fibers, including nonclosed primes, have exact power certificates. -/
theorem forall_fiber_primes_iff_power (b : B) :
    (∀ Q : PrimeSpectrum B, Q.asIdeal.comap s = P → b ∈ Q.asIdeal) ↔
      ∃ (n : ℕ) (r : R), r ∉ P ∧ s r * b ^ n ∈ P.map s :=
  (forall_fiber_primes_iff_localized_radical s P b).trans (localized_radical_iff_power s P b)

/-- Failure of a power certificate constructs an actual point of the unchanged scalar fiber. -/
theorem exists_fiber_prime_of_no_power (b : B)
    (h : ∀ (n : ℕ) (r : R), r ∉ P → s r * b ^ n ∉ P.map s) :
    ∃ Q : PrimeSpectrum B, Q.asIdeal.comap s = P ∧ b ∉ Q.asIdeal := by
  by_contra hn
  push Not at hn
  have hv : ∀ Q : PrimeSpectrum B, Q.asIdeal.comap s = P → b ∈ Q.asIdeal := by
    intro Q hQ
    exact hn Q hQ
  obtain ⟨n, r, hr, hp⟩ := (forall_fiber_primes_iff_power s P b).mp hv
  exact h n r hr hp

end FLT.Mazur.OriginalScalarFiberRadical
