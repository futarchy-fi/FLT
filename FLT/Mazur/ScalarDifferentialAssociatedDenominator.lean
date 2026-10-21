/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarDifferentialPrincipalRigidity
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Regular test denominators from the differential locus

Prime avoidance constructs a regular element of the pulled differential
annihilator ideal when all associated test primes are unramified. The element
can be a test-linear combination of pulled annihilators; it need not descend
to a single source scalar. No reducedness of the test is imposed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarDifferentialAssociatedDenominator
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [IsNoetherianRing B]

/-- Avoiding every associated prime constructs a regular member of the ideal. -/
theorem exists_regular_mem (I : Ideal B)
    (h : ∀ P ∈ associatedPrimes B B, ¬ I ≤ P) :
    ∃ b ∈ I, IsRegular b := by
  classical
  by_contra hn
  have hs : (I : Set B) ⊆ ⋃ P ∈ associatedPrimes B B, (P : Set B) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    intro b hb hreg
    exact hn ⟨b, hb, isRegular_iff_mem_nonZeroDivisors.mpr hreg⟩
  obtain ⟨P, hP, hIP⟩ :=
    (I.subset_union_prime_finite (associatedPrimes.finite B B)
      (f := id) 0 0 (fun _ hP _ _ ↦ hP.isPrime)).mp hs
  exact h P hP hIP

/-- Unramified associated endpoints construct a regular differential combination on the test. -/
theorem exists_regular_differential_combination [Algebra.EssFiniteType R A]
    (φ : A →+* B)
    (h : ∀ P : PrimeSpectrum B, P.asIdeal ∈ associatedPrimes B B →
      PrimeSpectrum.comap φ P ∈ Algebra.unramifiedLocus R A) :
    ∃ b ∈ (Module.annihilator A (KaehlerDifferential R A)).map φ, IsRegular b := by
  apply exists_regular_mem
  intro P hP hle
  obtain ⟨a, ha, hPa⟩ := ScalarDifferentialPrincipalRigidity.exists_annihilator
    (PrimeSpectrum.comap φ ⟨P, hP.isPrime⟩) (h ⟨P, hP.isPrime⟩ hP)
  exact hPa (hle (Ideal.mem_map_of_mem φ ha))

end FLT.Mazur.ScalarDifferentialAssociatedDenominator
