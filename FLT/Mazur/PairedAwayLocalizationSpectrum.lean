/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PairedAwayLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exact coverage of a common denominator localization

The common localization covers precisely the intersection of the two
original denominator opens. Its second localization covers every prime
where its actual coefficient stays nonzero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PairedAwayLocalization
variable {A B : Type*} [CommRing A] [CommRing B] (f g : A →+* B) (d : A)
local notation "Z" => Ring f g d
local notation "ι" => algebraMap B (Z)

/-- The common localization has precisely the two original denominator conditions. -/
theorem mem_range_comap_iff (p : PrimeSpectrum B) :
    p ∈ Set.range (PrimeSpectrum.comap (ι)) ↔ f d ∉ p.asIdeal ∧ g d ∉ p.asIdeal := by
  rw [PrimeSpectrum.localization_away_comap_range (Z) (f d * g d)]
  change f d * g d ∉ p.asIdeal ↔ _
  rw [p.isPrime.mul_mem_iff_mem_or_mem, not_or]

/-- The common neighborhood retains every original prime satisfying both conditions. -/
theorem exists_prime_over (p : PrimeSpectrum B)
    (hf : f d ∉ p.asIdeal) (hg : g d ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Z), PrimeSpectrum.comap (ι) q = p :=
  (mem_range_comap_iff f g d p).mpr ⟨hf, hg⟩

/-- A second localization preserves any such prime where the actual coefficient is nonzero. -/
theorem exists_prime_over_away (p : PrimeSpectrum B)
    (hf : f d ∉ p.asIdeal) (hg : g d ∉ p.asIdeal) (c : Z)
    (hc : ∀ q : PrimeSpectrum (Z), PrimeSpectrum.comap (ι) q = p → c ∉ q.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away c),
      PrimeSpectrum.comap ((algebraMap (Z) (Localization.Away c)).comp (ι)) q = p := by
  obtain ⟨q, hq⟩ := exists_prime_over f g d p hf hg
  obtain ⟨r, hr⟩ : q ∈ Set.range
      (PrimeSpectrum.comap (algebraMap (Z) (Localization.Away c))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away c) c]
    exact hc q hq
  refine ⟨r, ?_⟩
  change PrimeSpectrum.comap (ι)
    (PrimeSpectrum.comap (algebraMap (Z) (Localization.Away c)) r) = p
  rw [hr, hq]

end FLT.Mazur.PairedAwayLocalization
