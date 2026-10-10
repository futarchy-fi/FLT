/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The topological quotient on prime spectra

The fixed-ring inclusion gives a closed surjection of spectra. Its fibers
are precisely finite-group orbits of prime ideals. These are statements
about underlying points, not yet about algebraically closed field points.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]

/-- Every prime in the actual invariant ring has a prime above it. -/
theorem spectrum_surjective : Function.Surjective (PrimeSpectrum.comap (inclusion G A)) :=
  (inclusion_isIntegral G A).comap_surjective (inclusion_injective G A)

/-- The affine quotient map on prime spectra is closed. -/
theorem spectrum_isClosedMap : IsClosedMap (PrimeSpectrum.comap (inclusion G A)) :=
  PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (inclusion_isIntegral G A)

/-- The topology on the fixed-ring spectrum is the quotient topology. -/
theorem spectrum_isQuotientMap :
    Topology.IsQuotientMap (PrimeSpectrum.comap (inclusion G A)) :=
  (spectrum_isClosedMap G A).isQuotientMap
    (PrimeSpectrum.continuous_comap _) (spectrum_surjective G A)

/-- Two primes have the same image exactly when their ideals lie in the same orbit. -/
theorem spectrum_eq_iff_orbit (P Q : PrimeSpectrum A) :
    PrimeSpectrum.comap (inclusion G A) P = PrimeSpectrum.comap (inclusion G A) Q ↔
      ∃ g : G, Q.asIdeal = g • P.asIdeal := by
  constructor
  · intro h
    apply Algebra.IsInvariant.exists_smul_of_under_eq (invariantRing G A) A G
    exact congrArg PrimeSpectrum.asIdeal h
  · rintro ⟨g, hg⟩
    apply PrimeSpectrum.ext
    change P.asIdeal.under (invariantRing G A) = Q.asIdeal.under (invariantRing G A)
    rw [hg, Ideal.under_smul]

end FLT.Mazur.FiniteGroupQuotient
