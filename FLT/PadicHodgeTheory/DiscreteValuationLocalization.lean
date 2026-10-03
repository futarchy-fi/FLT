/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Inverting a uniformizer of a discrete valuation ring gives its fraction field -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing S] [Algebra R S]

/-- Any nonzero denominator is cleared by a power of the uniformizer. -/
theorem discreteValuation_isFractionRing {M : Submonoid R} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R) {t : R} (ht : Irreducible t) (htM : t ∈ M) :
    IsFractionRing R S := by
  apply IsLocalization.of_le_of_exists_dvd (S := S) M (nonZeroDivisors R) hM
  intro x hx
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero hx) ht
  exact ⟨t ^ n, M.pow_mem htM n, hn.dvd⟩

/-- In particular the ordinary localization away from the uniformizer is a fraction field. -/
theorem discreteValuation_away_isFractionRing {t : R} (ht : Irreducible t)
    [IsLocalization.Away t S] : IsFractionRing R S :=
  discreteValuation_isFractionRing (S := S)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht.ne_zero) ht (Submonoid.mem_powers t)

end PadicHodgeTheory
