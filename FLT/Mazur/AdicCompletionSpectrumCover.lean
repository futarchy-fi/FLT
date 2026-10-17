/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Completion and the complementary principal open cover the original spectrum

The completion map covers every prime containing its ideal, using the actual
first quotient. For a principal ideal the complementary localization supplies
all remaining points. No completeness or Jacobson hypothesis is imposed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicCompletionSpectrumCover
variable {R : Type*} [CommRing R]

/-- Every prime containing the ideal lifts to its actual adic completion. -/
theorem mem_range_of_le (I : Ideal R) (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (AdicCompletion I R))) := by
  have hq : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact hp
  obtain ⟨q, hq⟩ := hq
  refine ⟨PrimeSpectrum.comap (AdicCompletion.evalOneₐ I).toRingHom q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply,
    AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
  exact hq

/-- The completion at a parameter and its generic localization jointly cover every prime. -/
theorem principal_cover (t : R) (p : PrimeSpectrum R) :
    p ∈ Set.range (PrimeSpectrum.comap
        (algebraMap R (AdicCompletion (Ideal.span {t}) R))) ∨
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away t))) := by
  by_cases ht : t ∈ p.asIdeal
  · exact Or.inl (mem_range_of_le _ p (Ideal.span_le.mpr (by simpa using ht)))
  · right
    rw [PrimeSpectrum.localization_away_comap_range _ t]
    exact ht

end FLT.Mazur.AdicCompletionSpectrumCover
