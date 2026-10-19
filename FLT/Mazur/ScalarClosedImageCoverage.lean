/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Actual scalar images of closed invariant branches

Minimal primes over the contracted defining ideal always lie in the actual
image. If the scalar spectrum map is closed, the entire zero locus of that
contraction is the image. Integrality is one sufficient hypothesis for this
second statement; finite type alone is not used as a substitute.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarClosedImageCoverage
variable {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S)

/-- Minimal primes of a contracted branch have actual primes on that same branch above them. -/
theorem exists_prime_over_minimal_contraction (J : Ideal S) (P : PrimeSpectrum R)
    (hP : P.asIdeal ∈ (J.comap σ).minimalPrimes) :
    ∃ Q : PrimeSpectrum S, J ≤ Q.asIdeal ∧ PrimeSpectrum.comap σ Q = P := by
  obtain ⟨q, hq, hJ, he⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes σ P.asIdeal hP
  exact ⟨⟨q, hq⟩, hJ, PrimeSpectrum.ext he⟩

/-- Closedness upgrades the closure-of-image formula to an exact image formula. -/
theorem image_zeroLocus_of_closedMap (hc : IsClosedMap (PrimeSpectrum.comap σ))
    (J : Ideal S) :
    PrimeSpectrum.comap σ '' PrimeSpectrum.zeroLocus (J : Set S) =
      PrimeSpectrum.zeroLocus (J.comap σ : Set R) := by
  rw [← PrimeSpectrum.closure_image_comap_zeroLocus σ J,
    (hc _ (PrimeSpectrum.isClosed_zeroLocus _)).closure_eq]

/-- Every specialization of a contracted closed branch lifts when its scalar map is closed. -/
theorem exists_prime_over_contraction (hc : IsClosedMap (PrimeSpectrum.comap σ))
    (J : Ideal S) (P : PrimeSpectrum R) (hP : J.comap σ ≤ P.asIdeal) :
    ∃ Q : PrimeSpectrum S, J ≤ Q.asIdeal ∧ PrimeSpectrum.comap σ Q = P := by
  have hm : P ∈ PrimeSpectrum.comap σ '' PrimeSpectrum.zeroLocus (J : Set S) := by
    rw [image_zeroLocus_of_closedMap σ hc]
    exact hP
  exact hm

/-- Integrality supplies the needed closedness, with no scalar-flatness assumption. -/
theorem exists_prime_over_contraction_of_integral (hi : σ.IsIntegral)
    (J : Ideal S) (P : PrimeSpectrum R) (hP : J.comap σ ≤ P.asIdeal) :
    ∃ Q : PrimeSpectrum S, J ≤ Q.asIdeal ∧ PrimeSpectrum.comap σ Q = P :=
  exists_prime_over_contraction σ (PrimeSpectrum.isClosedMap_comap_of_isIntegral σ hi) J P hP

/-- The minimal contracted primes of any closed subset belong to its actual scalar image. -/
theorem mem_image_of_minimal_contracted_closed (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z)
    (P : PrimeSpectrum R)
    (hP : P.asIdeal ∈ ((PrimeSpectrum.vanishingIdeal Z).comap σ).minimalPrimes) :
    P ∈ PrimeSpectrum.comap σ '' Z := by
  obtain ⟨Q, hQ, he⟩ := exists_prime_over_minimal_contraction σ _ P hP
  refine ⟨Q, ?_, he⟩
  rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact hQ

/-- For a closed scalar map, containment in the contracted ideal is the exact image test. -/
theorem mem_image_closed_iff (hc : IsClosedMap (PrimeSpectrum.comap σ))
    (Z : Set (PrimeSpectrum S)) (hZ : IsClosed Z) (P : PrimeSpectrum R) :
    P ∈ PrimeSpectrum.comap σ '' Z ↔ (PrimeSpectrum.vanishingIdeal Z).comap σ ≤ P.asIdeal := by
  conv_lhs => rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  rw [image_zeroLocus_of_closedMap σ hc]
  rfl

end FLT.Mazur.ScalarClosedImageCoverage
