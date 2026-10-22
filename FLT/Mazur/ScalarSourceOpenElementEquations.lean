/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarSourceOpenRigidity

/-!
# Constructing source-open primes and finite tests from elementwise equations

An avoiding denominator constructs the actual prime in the source localization.
Finite differentials there select finitely many elementwise equations and yield
a rigidity neighborhood in the original source. No global finiteness is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenElementEquations
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]

omit [Algebra R A] in
/-- Avoidance constructs a source-localized prime lying over the exact test inverse image. -/
theorem exists_prime (φ : A →+* B) (Q : PrimeSpectrum B) (s : A) (hs : φ s ∉ Q.asIdeal) :
    ∃ P : PrimeSpectrum (Localization.Away s),
      PrimeSpectrum.comap (algebraMap A (Localization.Away s)) P =
        PrimeSpectrum.comap φ Q := by
  change PrimeSpectrum.comap φ Q ∈
    Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away s)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
  exact hs

/-- Finite differentials on an open choose the finite local equations needed for rigidity. -/
theorem exists_neighborhood (φ : A →+* B) (Q : PrimeSpectrum B) (s : A)
    (hs : φ s ∉ Q.asIdeal)
    [Module.Finite (Localization.Away s) (KaehlerDifferential R (Localization.Away s))]
    (h : ∀ P : PrimeSpectrum (Localization.Away s),
      PrimeSpectrum.comap (algebraMap A (Localization.Away s)) P = PrimeSpectrum.comap φ Q →
      ∀ z : Localization.Away s, ∃ F : Polynomial R,
        ScalarLocalPolynomialTests.Equation (algebraMap R (Localization.Away s))
          (RingHom.id (Localization.Away s)) P z F) :
    ∃ a : A, φ a ∉ Q.asIdeal ∧
      PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen s ∧
      Algebra.FormallyUnramified R (Localization.Away a) := by
  obtain ⟨P, hP⟩ := exists_prime φ Q s hs
  have hfg : let _ := (algebraMap R (Localization.Away s)).toAlgebra
      Module.Finite (Localization.Away s) (KaehlerDifferential R (Localization.Away s)) := by
    rw [toAlgebra_algebraMap]
    infer_instance
  have ht := ScalarLocalPolynomialTests.test_of_finite_differentials
    (algebraMap R (Localization.Away s)) (RingHom.id _) P hfg (h P hP)
  have hu := ScalarLocalPolynomialTests.mem_unramifiedLocus
    (algebraMap R (Localization.Away s)) (RingHom.id _) P ht
  dsimp only at hu
  rw [toAlgebra_algebraMap] at hu
  obtain ⟨a, ha, haU, haR⟩ := ScalarSourceOpenRigidity.exists_principal_neighborhood s P hu
  refine ⟨a, ?_, haU, haR⟩
  change a ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact ha

end FLT.Mazur.ScalarSourceOpenElementEquations
