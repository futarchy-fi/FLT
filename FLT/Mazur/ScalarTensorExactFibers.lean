/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarIntegralTests
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constructing original exact fibers from a specified scalar branch

Every original fiber prime lifts over any prescribed branch prime with the
same scalar center. Consequently branch fiber tests detect all original
fiber tests. This uses the full tensor algebra, without flatness, reducedness
or algebraicity of the branch residue extension.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (S : Type u) [CommRing S] [Algebra R S]
local notation "B'" => S ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)

/-- Lift an original prime over a prescribed branch prime, retaining both contractions. -/
theorem exists_tensor_fiber_prime (Q : PrimeSpectrum S) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q) :
    ∃ z : PrimeSpectrum B', PrimeSpectrum.comap (algebraMap S B') z = Q ∧
      PrimeSpectrum.comap (j).toRingHom z = q := by
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _
    (IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit R S B))
  exact Scheme.exists_preimage_of_isPullback hp Q q hq.symm

/-- A selected branch fiber detects the entire unchanged original fiber. -/
theorem original_fiber_test_of_tensor (Q : PrimeSpectrum S) (b : B)
    (hf : ∀ z : PrimeSpectrum B', PrimeSpectrum.comap (algebraMap S B') z = Q →
      j b ∈ z.asIdeal) :
    ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → b ∈ q.asIdeal := by
  intro q hq
  obtain ⟨z, hz, he⟩ := exists_tensor_fiber_prime S Q q hq
  have hb : b ∈ (PrimeSpectrum.comap (j).toRingHom z).asIdeal := hf z hz
  rwa [he] at hb

/-- Exact original fiber tests are equivalent to tests on any one scalar branch fiber. -/
theorem original_fiber_test_iff_tensor (Q : PrimeSpectrum S) (b : B) :
    (∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → b ∈ q.asIdeal) ↔
    ∀ z : PrimeSpectrum B', PrimeSpectrum.comap (algebraMap S B') z = Q →
      j b ∈ z.asIdeal :=
  ⟨flatTensor_fiber_test S Q b, original_fiber_test_of_tensor S Q b⟩

/-- A failed original test has a failed point above the specified branch prime. -/
theorem exists_tensor_fiber_failure (Q : PrimeSpectrum S) (q : PrimeSpectrum B) (b : B)
    (hq : PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q) (hb : b ∉ q.asIdeal) :
    ∃ z : PrimeSpectrum B', PrimeSpectrum.comap (algebraMap S B') z = Q ∧
      PrimeSpectrum.comap (j).toRingHom z = q ∧ j b ∉ z.asIdeal := by
  obtain ⟨z, hz, he⟩ := exists_tensor_fiber_prime S Q q hq
  refine ⟨z, hz, he, ?_⟩
  intro h
  apply hb
  change b ∈ (PrimeSpectrum.comap (j).toRingHom z).asIdeal at h
  rwa [he] at h

end FLT.Mazur.ScalarTestLocalization
