/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedIdealNilpotence
public import FLT.Mazur.FiniteIdealNilpotenceInterior

/-!
# Scalar neighborhoods for full coefficient ideal nilpotence

The open is built from scalars, not arbitrary coefficient denominators.
Its inverse image lies in the coefficient nilpotence open; the defining
certificates kill one whole ideal power on every point above the neighborhood.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (I : Ideal B)

/-- Scalar basic opens certified by an annihilator of a full coefficient ideal power. -/
def scalarNilpotenceOpen : TopologicalSpace.Opens (PrimeSpectrum R) :=
  ⨆ (k : ℕ) (r : (I ^ k).annihilator.comap s), PrimeSpectrum.basicOpen (r : R)

/-- A member has a denominator in the original scalar ring outside its original prime. -/
theorem mem_scalarNilpotenceOpen (P : PrimeSpectrum R) :
    P ∈ scalarNilpotenceOpen s I ↔
      ∃ k : ℕ, ∃ r : R, r ∉ P.asIdeal ∧ s r ∈ (I ^ k).annihilator := by
  simp only [scalarNilpotenceOpen, TopologicalSpace.Opens.mem_iSup, PrimeSpectrum.mem_basicOpen]
  exact ⟨fun ⟨k, r, hr⟩ ↦ ⟨k, r, hr, r.property⟩,
    fun ⟨k, r, hr, ha⟩ ↦ ⟨k, ⟨r, ha⟩, hr⟩⟩

/-- The scalar open tests nilpotence in the full scalar localization of the coefficient ring. -/
theorem mem_scalarNilpotenceOpen_iff_localized (hI : I.FG) (P : PrimeSpectrum R) :
    P ∈ scalarNilpotenceOpen s I ↔ IsNilpotent
      (I.map (algebraMap B (Localization (P.asIdeal.primeCompl.map s)))) := by
  rw [mem_scalarNilpotenceOpen, nilpotent_iff_scalar_annihilator s I P.asIdeal hI]

/-- Minimal components with all generizing scalar centers detect the scalar open exactly. -/
theorem mem_scalarNilpotenceOpen_iff_components (hI : I.FG) (P : PrimeSpectrum R) :
    P ∈ scalarNilpotenceOpen s I ↔
      ∀ Q : minimalPrimes B, Q.val.comap s ≤ P.asIdeal → I ≤ Q.val := by
  rw [mem_scalarNilpotenceOpen_iff_localized s I hI,
    nilpotent_iff_components s I P.asIdeal hI]

/-- A scalar power annihilator certifies its whole scalar basic open. -/
theorem basicOpen_le_scalarNilpotenceOpen (k : ℕ) (r : R)
    (hr : s r ∈ (I ^ k).annihilator) :
    PrimeSpectrum.basicOpen r ≤ scalarNilpotenceOpen s I := by
  intro P hP
  exact (mem_scalarNilpotenceOpen s I P).mpr ⟨k, r, hP, hr⟩

/-- Scalar neighborhoods pull back into actual full coefficient nilpotence neighborhoods. -/
theorem preimage_scalarNilpotenceOpen_subset :
    PrimeSpectrum.comap s ⁻¹' (scalarNilpotenceOpen s I : Set (PrimeSpectrum R)) ⊆
      FiniteIdealLocalizationDenominators.nilpotenceOpen I := by
  intro Q hQ
  obtain ⟨k, r, hr, ha⟩ := (mem_scalarNilpotenceOpen s I (PrimeSpectrum.comap s Q)).mp hQ
  exact (FiniteIdealLocalizationDenominators.mem_nilpotenceOpen I Q).mpr ⟨k, s r, hr, ha⟩

/-- A scalar basic open whose entire inverse image satisfies the tests has a scalar certificate. -/
theorem exists_scalar_power_of_basicOpen (hI : I.FG) (r : R)
    (h : (PrimeSpectrum.basicOpen (s r) : Set (PrimeSpectrum B)) ⊆
      PrimeSpectrum.zeroLocus (I : Set B)) :
    ∃ k l : ℕ, s (r ^ l) ∈ (I ^ k).annihilator := by
  simpa only [map_pow] using
    FiniteIdealLocalizationDenominators.exists_power_denominator_of_basicOpen_subset I hI (s r) h

/-- Full scalar coverage is equivalent to nilpotence in the unchanged coefficient ring. -/
theorem scalarNilpotenceOpen_eq_top_iff (hI : I.FG) :
    scalarNilpotenceOpen s I = ⊤ ↔ IsNilpotent I := by
  constructor
  · intro h
    apply (FiniteIdealLocalizationDenominators.nilpotenceOpen_eq_top_iff I hI).mp
    apply top_unique
    intro Q _
    apply preimage_scalarNilpotenceOpen_subset s I
    change PrimeSpectrum.comap s Q ∈ scalarNilpotenceOpen s I
    rw [h]
    trivial
  · rintro ⟨k, hk⟩
    apply top_unique
    intro P _
    apply (mem_scalarNilpotenceOpen s I P).mpr
    refine ⟨k, 1, P.isPrime.one_notMem, ?_⟩
    rw [hk, Submodule.mem_annihilator]
    intro x hx
    rw [Ideal.mem_bot.mp hx, smul_zero]

end FLT.Mazur.ScalarLocalizedIdealNilpotence
