/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarIdealNilpotenceOpen

/-!
# The exact closed scalar obstruction to coefficient nilpotence

The scalar obstruction is the closure of the image of failed coefficient
tests. Every obstructed scalar prime has a failing original minimal component
whose scalar center generizes it. No closed-image hypothesis is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (I : Ideal B) (hI : I.FG)
include hI

/-- Every excluded scalar prime has an actual failing minimal component above a generization. -/
theorem not_mem_scalarNilpotenceOpen_iff (P : PrimeSpectrum R) :
    P ∉ scalarNilpotenceOpen s I ↔
      ∃ Q : minimalPrimes B, Q.val.comap s ≤ P.asIdeal ∧ ¬ I ≤ Q.val := by
  rw [mem_scalarNilpotenceOpen_iff_components s I hI]
  push Not
  rfl

/-- The whole scalar obstruction is the closure of the image of actual failed tests. -/
theorem scalarNilpotenceOpen_compl :
    (scalarNilpotenceOpen s I : Set (PrimeSpectrum R))ᶜ =
      closure (PrimeSpectrum.comap s '' (PrimeSpectrum.zeroLocus (I : Set B))ᶜ) := by
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨Q, hQ, hf⟩ := (not_mem_scalarNilpotenceOpen_iff s I hI P).mp hP
    have hc : PrimeSpectrum.comap s ⟨Q.val, Q.property.1.1⟩ ⤳ P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hQ
    apply hc.mem_closed isClosed_closure
    apply subset_closure
    exact ⟨⟨Q.val, Q.property.1.1⟩, hf, rfl⟩
  · apply closure_minimal
    · rintro _ ⟨Q, hQ, rfl⟩ hP
      have hn := preimage_scalarNilpotenceOpen_subset s I hP
      exact hQ (FiniteIdealLocalizationDenominators.nilpotenceOpen_subset_zeroLocus I hn)
    · exact (scalarNilpotenceOpen s I).isOpen.isClosed_compl

/-- Any open scalar region satisfying the tests on its whole inverse image is certified. -/
theorem open_subset_scalarNilpotenceOpen (V : TopologicalSpace.Opens (PrimeSpectrum R))
    (hV : PrimeSpectrum.comap s ⁻¹' (V : Set (PrimeSpectrum R)) ⊆
      PrimeSpectrum.zeroLocus (I : Set B)) : V ≤ scalarNilpotenceOpen s I := by
  intro P hP
  by_contra hn
  have hc : P ∈ closure
      (PrimeSpectrum.comap s '' (PrimeSpectrum.zeroLocus (I : Set B))ᶜ) := by
    rw [← scalarNilpotenceOpen_compl s I hI]
    exact hn
  obtain ⟨_, hv, Q, hQ, rfl⟩ := mem_closure_iff.mp hc V V.isOpen hP
  exact hQ (hV hv)

/-- This is the largest scalar open whose entire inverse image has full local nilpotence. -/
theorem le_scalarNilpotenceOpen_iff (V : TopologicalSpace.Opens (PrimeSpectrum R)) :
    V ≤ scalarNilpotenceOpen s I ↔
      PrimeSpectrum.comap s ⁻¹' (V : Set (PrimeSpectrum R)) ⊆
        FiniteIdealLocalizationDenominators.nilpotenceOpen I := by
  constructor
  · intro h Q hQ
    exact preimage_scalarNilpotenceOpen_subset s I (h hQ)
  · intro h
    exact open_subset_scalarNilpotenceOpen s I hI V
      (h.trans (FiniteIdealLocalizationDenominators.nilpotenceOpen_subset_zeroLocus I))

end FLT.Mazur.ScalarLocalizedIdealNilpotence
