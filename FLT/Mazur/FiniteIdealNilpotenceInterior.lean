/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIdealNilpotenceOpen

/-!
# Nilpotence neighborhoods and the interior of the equation locus

For a finite ideal, the largest open on which the full local ideals are
nilpotent is exactly the interior of its zero locus. Its complement is the
closure of the failed-test locus, including its specializations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteIdealLocalizationDenominators
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
include hI

/-- A principal open satisfying the equations has a nilpotent ideal over its full ring. -/
theorem away_nilpotent_of_basicOpen_subset (u : R)
    (h : (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum R)) ⊆
      PrimeSpectrum.zeroLocus (I : Set R)) :
    IsNilpotent (I.map (algebraMap R (Localization.Away u))) := by
  apply (hI.map _).isNilpotent_iff_le_nilradical.mpr
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change IsNilpotent (algebraMap R (Localization.Away u) x)
  have hn : IsNilpotent (u * x) := by
    apply (PrimeSpectrum.basicOpen_eq_bot_iff _).mp
    apply bot_unique
    intro P hP
    have hp := (PrimeSpectrum.basicOpen_mul_le_left u x) hP
    have hq := (PrimeSpectrum.basicOpen_mul_le_right u x) hP
    exact hq (h hp hx)
  have hu : IsUnit (algebraMap R (Localization.Away u) u) :=
    IsLocalization.map_units (Localization.Away u) ⟨u, Submonoid.mem_powers u⟩
  apply (hu.isNilpotent_unit_mul_of_commute_iff (Commute.all _ _)).mp
  simpa only [map_mul] using hn.map (algebraMap R (Localization.Away u))

/-- The original denominator can be raised to give a certificate for an entire ideal power. -/
theorem exists_power_denominator_of_basicOpen_subset (u : R)
    (h : (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum R)) ⊆
      PrimeSpectrum.zeroLocus (I : Set R)) :
    ∃ k l : ℕ, u ^ l ∈ (I ^ k).annihilator := by
  obtain ⟨k, v, hv⟩ := exists_power_annihilator I hI (Submonoid.powers u)
    (away_nilpotent_of_basicOpen_subset I hI u h)
  obtain ⟨l, hl⟩ := v.property
  refine ⟨k, l, ?_⟩
  change u ^ l = (v : R) at hl
  rw [hl]
  exact hv

/-- The constructed nilpotence locus is the largest open satisfying the original equations. -/
theorem nilpotenceOpen_eq_interior :
    (nilpotenceOpen I : Set (PrimeSpectrum R)) =
      interior (PrimeSpectrum.zeroLocus (I : Set R)) := by
  apply Set.Subset.antisymm
  · exact interior_maximal (nilpotenceOpen_subset_zeroLocus I) (nilpotenceOpen I).isOpen
  · intro P hP
    obtain ⟨_, ⟨u, rfl⟩, hu, hs⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP isOpen_interior
    obtain ⟨k, l, hl⟩ := exists_power_denominator_of_basicOpen_subset I hI u
      (hs.trans interior_subset)
    apply (mem_nilpotenceOpen I P).mpr
    refine ⟨k, u ^ l, ?_, hl⟩
    exact fun hp ↦ hu (P.isPrime.mem_of_pow_mem l hp)

/-- The residual closed set is exactly the closure of the actual failed equations. -/
theorem nilpotenceOpen_compl :
    (nilpotenceOpen I : Set (PrimeSpectrum R))ᶜ =
      closure (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
  rw [nilpotenceOpen_eq_interior I hI, closure_compl]

end FLT.Mazur.FiniteIdealLocalizationDenominators
