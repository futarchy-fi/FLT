/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Finite ideals on full generic local rings

A finite ideal is nilpotent after localization at a minimal prime exactly when
it lies in that prime. Otherwise its localized ideal is the unit ideal. Testing
all such full local rings detects nilpotence in the original ring; it does not
detect equality with zero in the presence of embedded components.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.MinimalPrimeLocalizedIdeal
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) (Q : minimalPrimes R)
local instance componentPrime : Q.val.IsPrime := Q.property.1.1
local notation "L" => Localization.AtPrime Q.val

/-- The full minimal-prime local ring has precisely the extended prime as its nilradical. -/
theorem localized_nilradical : nilradical L = Q.val.map (algebraMap R L) := by
  simpa only [Ideal.map_bot, nilradical, Ideal.zero_eq_bot] using
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := L) Q.val ⊥ Q.property

include hI in
/-- Finite ideal nilpotence on a full generic local ring is exact prime containment. -/
theorem localized_nilpotent_iff : IsNilpotent (I.map (algebraMap R L)) ↔ I ≤ Q.val := by
  rw [(hI.map (algebraMap R L)).isNilpotent_iff_le_nilradical,
    localized_nilradical, Ideal.map_le_iff_le_comap,
    IsLocalization.AtPrime.map_eq_maximalIdeal Q.val L]
  change I ≤ (IsLocalRing.maximalIdeal L).under R ↔ I ≤ Q.val
  rw [IsLocalization.AtPrime.under_maximalIdeal L Q.val]

/-- A failed generic containment makes the ideal a unit on the full local ring. -/
theorem localized_eq_top (h : ¬ I ≤ Q.val) : I.map (algebraMap R L) = ⊤ :=
  IsLocalization.AtPrime.map_eq_top_of_not_le L h

include hI in
/-- Each generic local component has an actual nilpotent or unit ideal, with no reduction. -/
theorem localized_nilpotent_or_top :
    IsNilpotent (I.map (algebraMap R L)) ∨ I.map (algebraMap R L) = ⊤ := by
  by_cases h : I ≤ Q.val
  · exact Or.inl ((localized_nilpotent_iff I hI Q).mpr h)
  · exact Or.inr (localized_eq_top I Q h)

include hI in
/-- Full generic local rings jointly detect nilpotence of every finite original ideal. -/
theorem nilpotent_iff_all_localized :
    IsNilpotent I ↔ ∀ Q : minimalPrimes R,
      let _ := Q.property.1.1
      IsNilpotent (I.map (algebraMap R (Localization.AtPrime Q.val))) := by
  constructor
  · intro h P
    let _ := P.property.1.1
    apply (localized_nilpotent_iff I hI P).mpr
    exact ((hI.isNilpotent_iff_le_nilradical).mp h).trans (nilradical_le_prime P.val)
  · intro h
    apply hI.isNilpotent_iff_le_nilradical.mpr
    rw [nilradical, ← Ideal.sInf_minimalPrimes]
    apply le_sInf
    intro P hP
    exact (localized_nilpotent_iff I hI ⟨P, hP⟩).mp (h ⟨P, hP⟩)

end FLT.Mazur.MinimalPrimeLocalizedIdeal
