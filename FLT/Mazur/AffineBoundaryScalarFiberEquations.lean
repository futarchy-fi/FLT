/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryScalarNilpotence
public import FLT.Mazur.OriginalScalarFiberFiniteEquations

/-!
# Exact original fiber equations from scalar nilpotence neighborhoods

Scalar-local product nilpotence implies all finite tests on the entire
original invariant fiber. Their equations share a denominator in the original
base ring, avoiding the contracted prime. No integrality of either map is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)

/-- All invariant primes with the original contracted center satisfy every finite test. -/
theorem boundaryScalar_mem_fiber_tests (P : PrimeSpectrum T)
    (hP : P ∈ boundaryScalarNilpotenceOpen s κ a) (Q : PrimeSpectrum B)
    (hQ : PrimeSpectrum.comap s Q = PrimeSpectrum.comap κ P) :
    ∀ t ∈ a, t ∈ Q.asIdeal := by
  obtain ⟨z, hz, hp⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Spec.map (CommRingCat.ofHom s)) (g := Spec.map (CommRingCat.ofHom κ)) Q P hQ
  change boundaryProjection s κ z = Q at hz
  change boundaryScalarProjection s κ z = P at hp
  have hm : boundaryScalarProjection s κ z ∈ boundaryScalarNilpotenceOpen s κ a := by
    rwa [hp]
  have hn := boundaryScalarNilpotenceOpen_preimage s κ a hm
  have hi := FiniteIdealLocalizationDenominators.nilpotenceOpen_subset_zeroLocus
    (boundaryTestIdeal s κ a) hn
  have ht := (boundaryTestIdeal_le_point_iff s κ a z).mp hi
  rwa [hz] at ht

/-- These full original fiber equations have one base-ring denominator avoiding the scalar prime. -/
theorem boundaryScalar_mem_common_fiber_equations (P : PrimeSpectrum T)
    (hP : P ∈ boundaryScalarNilpotenceOpen s κ a) :
    ∃ r : R, κ r ∉ P.asIdeal ∧ ∀ t ∈ a, ∃ k : ℕ,
      s r * t ^ k ∈ (P.asIdeal.comap κ).map s := by
  apply OriginalScalarFiberRadical.exists_common_power_denominator s (P.asIdeal.comap κ) a
  intro t ht
  apply (OriginalScalarFiberRadical.forall_fiber_primes_iff_power
    s (P.asIdeal.comap κ) t).mp
  intro Q hQ
  exact boundaryScalar_mem_fiber_tests s κ a P hP Q (PrimeSpectrum.ext hQ) t ht

end FLT.Mazur.AffineScalarBoundaryNilpotence
