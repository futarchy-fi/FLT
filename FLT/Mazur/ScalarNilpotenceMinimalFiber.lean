/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryScalarObstructionGeometry

/-!
# Exact fibers suffice at minimal scalar centers

A minimal scalar prime has no strictly generizing scalar prime. Thus its
exact fiber tests control the full scalar localization and construct a power
annihilator before reduction. This does not extend to nonminimal residual
centers, where higher components may escape the exact fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (I : Ideal B) (hI : I.FG)
  (P : PrimeSpectrum R) (hP : P.asIdeal ∈ minimalPrimes R)
include hI hP

/-- At a minimal scalar prime the exact fiber already sees every surviving coefficient prime. -/
theorem mem_scalarNilpotenceOpen_iff_minimal_fiber :
    P ∈ scalarNilpotenceOpen s I ↔
      ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap s Q = P → I ≤ Q.asIdeal := by
  rw [mem_scalarNilpotenceOpen_iff_localized s I hI, nilpotent_iff_primes s I P.asIdeal hI]
  constructor
  · intro h Q hQ
    exact h Q (le_of_eq (congrArg PrimeSpectrum.asIdeal hQ))
  · intro h Q hQ
    apply h Q
    apply PrimeSpectrum.ext
    exact le_antisymm hQ (hP.2 ⟨Q.isPrime.comap s, bot_le⟩ hQ)

/-- Matching exact generic fibers construct an original denominator for an entire ideal power. -/
theorem minimal_fiber_power_denominator
    (h : ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap s Q = P → I ≤ Q.asIdeal) :
    ∃ (k : ℕ) (r : R), r ∉ P.asIdeal ∧ s r ∈ (I ^ k).annihilator :=
  (mem_scalarNilpotenceOpen s I P).mp
    ((mem_scalarNilpotenceOpen_iff_minimal_fiber s I hI P hP).mpr h)

end FLT.Mazur.ScalarLocalizedIdealNilpotence

namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarLocalizedIdealNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
  (P : PrimeSpectrum T) (hP : P.asIdeal ∈ minimalPrimes T)
include hP

/-- Actual boundary tests on a minimal exact scalar fiber give full scalar neighborhood coverage. -/
theorem boundaryScalar_mem_of_minimal_fiber
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply (mem_scalarNilpotenceOpen_iff_minimal_fiber (boundaryScalarHom s κ)
    (boundaryTestIdeal s κ a) (boundaryTestIdeal_fg s κ a) P hP).mpr
  intro Q hQ
  let z := (boundaryProduct s κ).isoSpec.inv Q
  have hz : (boundaryProduct s κ).isoSpec.hom z = Q :=
    congrArg (fun f ↦ f Q) (boundaryProduct s κ).isoSpec.inv_hom_id
  have hp : boundaryScalarProjection s κ z = P := by
    apply PrimeSpectrum.ext
    rw [← boundaryScalarHom_comap_point, hz]
    exact congrArg PrimeSpectrum.asIdeal hQ
  have ht := (boundaryTestIdeal_le_point_iff s κ a z).mpr (hf z hp)
  simpa only [hz] using ht

end FLT.Mazur.AffineScalarBoundaryNilpotence
