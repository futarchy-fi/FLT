/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Actual local scalar thickenings at a prescribed prime

Localize the original scalar ring at the prime, then quotient by a positive
power of its maximal ideal. Every such test has exactly the prescribed scalar
support, with no Noetherian or finite-presentation hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarPrimeThickenings
variable {R : Type} [CommRing R] (P : PrimeSpectrum R) (order : ℕ)
local notation "S" => Localization.AtPrime P.asIdeal

/-- The requested positive infinitesimal power in the actual original local ring. -/
def primePowerIdeal : Ideal S := IsLocalRing.maximalIdeal S ^ (order + 1)

/-- A local infinitesimal test retaining the specified maximal-ideal power. -/
abbrev primeThickeningRing : Type := S ⧸ primePowerIdeal P order

/-- The unchanged original scalar action on its local infinitesimal test. -/
def primeThickeningMap : R →+* primeThickeningRing P order :=
  (Ideal.Quotient.mk (primePowerIdeal P order)).comp (algebraMap R S)

/-- Every scalar in the prescribed prime vanishes at the requested positive power. -/
theorem primeThickening_power (r : R) (hr : r ∈ P.asIdeal) :
    primeThickeningMap P order r ^ (order + 1) = 0 := by
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change algebraMap R S (r ^ (order + 1)) ∈ primePowerIdeal P order
  rw [map_pow]
  exact Ideal.pow_mem_pow ((IsLocalization.AtPrime.to_map_mem_maximal_iff S P.asIdeal r).mpr hr) _

/-- Every scalar outside the prime remains a unit at every infinitesimal order. -/
theorem primeThickening_unit (r : R) (hr : r ∉ P.asIdeal) :
    IsUnit (primeThickeningMap P order r) :=
  ((IsLocalization.AtPrime.isUnit_to_map_iff S P.asIdeal r).mpr hr).map
    (Ideal.Quotient.mk (primePowerIdeal P order))

/-- Every point of the constructed test has exactly the unchanged original scalar prime. -/
theorem primeThickening_center (Q : PrimeSpectrum (primeThickeningRing P order)) :
    PrimeSpectrum.comap (primeThickeningMap P order) Q = P := by
  apply PrimeSpectrum.ext
  ext r
  constructor
  · intro hr
    by_contra hn
    exact Q.isPrime.ne_top
      (Q.asIdeal.eq_top_of_isUnit_mem hr (primeThickening_unit P order r hn))
  · intro hr
    apply Q.isPrime.mem_of_pow_mem (order + 1)
    rw [primeThickening_power P order r hr]
    exact Q.asIdeal.zero_mem

/-- Every order is nonempty and reaches the prescribed scalar prime. -/
theorem primeThickening_range :
    Set.range (PrimeSpectrum.comap (primeThickeningMap P order)) = {P} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨Q, rfl⟩
    exact primeThickening_center P order Q
  · intro Q hQ
    have hQP : Q = P := hQ
    subst Q
    let m : PrimeSpectrum S := ⟨IsLocalRing.maximalIdeal S, inferInstance⟩
    have hm : m ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk
        (primePowerIdeal P order))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
      change RingHom.ker (Ideal.Quotient.mk (primePowerIdeal P order)) ≤ m.asIdeal
      rw [Ideal.mk_ker]
      exact Ideal.pow_le_self (Nat.succ_ne_zero order)
    obtain ⟨q, _⟩ := hm
    exact ⟨q, primeThickening_center P order q⟩

end FLT.Mazur.ScalarPrimeThickenings
