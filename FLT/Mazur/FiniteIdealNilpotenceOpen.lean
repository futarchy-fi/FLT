/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIdealLocalizationDenominators
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The open locus of actual local ideal nilpotence

The union of principal opens of power annihilators records exactly where a
finite ideal is nilpotent in the full local ring. At a minimal prime, membership
is equivalent to containment of the original ideal in that prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteIdealLocalizationDenominators
variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Each open comes with an original denominator annihilating a specified ideal power. -/
def nilpotenceOpen : TopologicalSpace.Opens (PrimeSpectrum R) :=
  ⨆ (k : ℕ) (u : (I ^ k).annihilator), PrimeSpectrum.basicOpen (u : R)

/-- Membership includes an actual power and an original annihilating denominator. -/
theorem mem_nilpotenceOpen (P : PrimeSpectrum R) :
    P ∈ nilpotenceOpen I ↔ ∃ k : ℕ, ∃ u : R, u ∉ P.asIdeal ∧
      u ∈ (I ^ k).annihilator := by
  simp only [nilpotenceOpen, TopologicalSpace.Opens.mem_iSup, PrimeSpectrum.mem_basicOpen]
  exact ⟨fun ⟨k, u, hu⟩ ↦ ⟨k, u, hu, u.property⟩,
    fun ⟨k, u, hu, ha⟩ ↦ ⟨k, ⟨u, ha⟩, hu⟩⟩

/-- This is nilpotence in the full local coefficient ring, rather than its residue field. -/
theorem mem_nilpotenceOpen_iff_localized (hI : I.FG) (P : PrimeSpectrum R) :
    P ∈ nilpotenceOpen I ↔
      IsNilpotent (I.map (algebraMap R (Localization.AtPrime P.asIdeal))) := by
  rw [mem_nilpotenceOpen]
  constructor
  · rintro ⟨k, u, hu, ha⟩
    refine ⟨k, ?_⟩
    change (I.map (algebraMap R (Localization.AtPrime P.asIdeal))) ^ k = ⊥
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    apply (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) x).mpr
    exact ⟨⟨u, hu⟩, Submodule.mem_annihilator.mp ha x hx⟩
  · intro h
    obtain ⟨k, u, hu⟩ := exists_power_annihilator I hI P.asIdeal.primeCompl h
    exact ⟨k, u, u.property, hu⟩

/-- Actual local nilpotence implies all original equations vanish at the point. -/
theorem nilpotenceOpen_subset_zeroLocus :
    (nilpotenceOpen I : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  intro P hP x hx
  obtain ⟨k, u, hu, ha⟩ := (mem_nilpotenceOpen I P).mp hP
  apply P.isPrime.mem_of_pow_mem k
  apply (P.isPrime.mem_or_mem ?_).resolve_left hu
  have he : u * x ^ k = 0 :=
    Submodule.mem_annihilator.mp ha (x ^ k) (Ideal.pow_mem_pow hx k)
  rw [he]
  exact P.asIdeal.zero_mem

/-- Every matching minimal component lies in a principal open with an exact power equation. -/
theorem minimal_mem_nilpotenceOpen_iff (hI : I.FG) (Q : minimalPrimes R) :
    (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum R) ∈ nilpotenceOpen I ↔ I ≤ Q.val := by
  rw [mem_nilpotenceOpen_iff_localized I hI]
  exact MinimalPrimeLocalizedIdeal.localized_nilpotent_iff I hI Q

/-- Coverage by these open neighborhoods is exactly global nilpotence of the finite ideal. -/
theorem nilpotenceOpen_eq_top_iff (hI : I.FG) :
    nilpotenceOpen I = ⊤ ↔ IsNilpotent I := by
  constructor
  · intro h
    apply (MinimalPrimeLocalizedIdeal.nilpotent_iff_all_localized I hI).mpr
    intro Q
    apply (mem_nilpotenceOpen_iff_localized I hI ⟨Q.val, Q.property.1.1⟩).mp
    rw [h]
    trivial
  · rintro ⟨k, hk⟩
    apply top_unique
    intro P _
    apply (mem_nilpotenceOpen I P).mpr
    refine ⟨k, 1, P.isPrime.one_notMem, ?_⟩
    rw [hk, Submodule.mem_annihilator]
    intro x hx
    rw [Ideal.mem_bot.mp hx, smul_zero]

end FLT.Mazur.FiniteIdealLocalizationDenominators
