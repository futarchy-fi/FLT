/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarConstructibleStrata
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Actual infinitesimal scalar tests for a principal closed stratum

Quotient by a positive power of the stratum equations and invert its denominator.
The resulting ring keeps that infinitesimal order, while its spectrum maps onto
exactly the prescribed scalar piece. No reduced scalar replacement is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarConstructibleStrata
variable {R : Type} [CommRing R] (a : R × Finset R) (order : ℕ)

/-- The scalar equations to the requested positive infinitesimal order. -/
def stratumPowerIdeal : Ideal R := Ideal.span (a.2 : Set R) ^ (order + 1)

/-- An actual scalar algebra retaining the chosen power of the closed equations. -/
abbrev stratumThickeningRing : Type :=
  Localization.Away (Ideal.Quotient.mk (stratumPowerIdeal a order) a.1)

/-- The unchanged scalar action on the constructed infinitesimal test algebra. -/
def stratumThickeningMap : R →+* stratumThickeningRing a order :=
  (algebraMap (R ⧸ stratumPowerIdeal a order) (stratumThickeningRing a order)).comp
    (Ideal.Quotient.mk (stratumPowerIdeal a order))

/-- The denominator becomes a unit in the constructed test ring. -/
theorem stratumThickening_denominator_unit : IsUnit (stratumThickeningMap a order a.1) :=
  IsLocalization.Away.algebraMap_isUnit
    (S := stratumThickeningRing a order) (Ideal.Quotient.mk (stratumPowerIdeal a order) a.1)

/-- Closed equations vanish to the specified order, before any reduction. -/
theorem stratumThickening_equation_power (r : R) (hr : r ∈ a.2) :
    stratumThickeningMap a order r ^ (order + 1) = 0 := by
  rw [← map_pow]
  change algebraMap (R ⧸ stratumPowerIdeal a order) _
    (Ideal.Quotient.mk (stratumPowerIdeal a order) (r ^ (order + 1))) = 0
  have h : r ^ (order + 1) ∈ stratumPowerIdeal a order :=
    Ideal.pow_mem_pow (Ideal.subset_span hr) _
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- Every point of the infinitesimal test lies in the intended scalar stratum. -/
theorem stratumThickening_support (Q : PrimeSpectrum (stratumThickeningRing a order)) :
    a.1 ∉ (PrimeSpectrum.comap (stratumThickeningMap a order) Q).asIdeal ∧
      ∀ r ∈ a.2, r ∈ (PrimeSpectrum.comap (stratumThickeningMap a order) Q).asIdeal := by
  refine ⟨fun h ↦ Q.isPrime.ne_top
    (Q.asIdeal.eq_top_of_isUnit_mem h (stratumThickening_denominator_unit a order)), ?_⟩
  intro r hr
  apply Q.isPrime.mem_of_pow_mem (order + 1)
  rw [stratumThickening_equation_power a order r hr]
  exact Q.asIdeal.zero_mem

/-- Every scalar prime in the piece lifts to every constructed infinitesimal order. -/
theorem stratumThickening_range (P : PrimeSpectrum R) :
    P ∈ Set.range (PrimeSpectrum.comap (stratumThickeningMap a order)) ↔
      a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal := by
  constructor
  · rintro ⟨Q, rfl⟩
    exact stratumThickening_support a order Q
  · rintro ⟨ht, he⟩
    let J := stratumPowerIdeal a order
    let π := Ideal.Quotient.mk J
    have hJ : J ≤ P.asIdeal :=
      (Ideal.pow_le_self (Nat.succ_ne_zero order)).trans (Ideal.span_le.mpr he)
    have hP : P ∈ Set.range (PrimeSpectrum.comap π) := by
      rw [range_comap_of_surjective _ π Ideal.Quotient.mk_surjective]
      simpa only [π, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe] using hJ
    obtain ⟨q, hq⟩ := hP
    have hqt : π a.1 ∉ q.asIdeal := by
      change a.1 ∉ (PrimeSpectrum.comap π q).asIdeal
      rwa [hq]
    have hqL : q ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (R ⧸ J) (stratumThickeningRing a order))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ (π a.1)]
      exact hqt
    obtain ⟨Q, hQ⟩ := hqL
    refine ⟨Q, ?_⟩
    change PrimeSpectrum.comap π (PrimeSpectrum.comap
      (algebraMap (R ⧸ J) (stratumThickeningRing a order)) Q) = P
    rw [hQ, hq]

end FLT.Mazur.ScalarConstructibleStrata
