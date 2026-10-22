/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarSourceOpenRigidity

/-!
# Original-source neighborhoods from equations on a finite-differential source open

The chosen source open may depend on the test prime. Polynomial or coupled
Jacobian tests there produce an actual principal neighborhood in the original
source, contained in that open and avoiding the original test prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenEquationNeighborhoods
variable {R A S B : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra A S] [Algebra R S] [IsScalarTower R A S]

/-- Coupled stalk equations on a source open construct an original-source rigidity neighborhood. -/
theorem of_jacobian (s : A) [IsLocalization.Away s S]
    [Module.Finite S (KaehlerDifferential R S)] (φ : S →+* B) (Q : PrimeSpectrum B)
    (h : ScalarStalkJacobianTests.Test (algebraMap R S) φ Q) :
    ∃ a : A, φ (algebraMap A S a) ∉ Q.asIdeal ∧
      PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen s ∧
      Algebra.FormallyUnramified R (Localization.Away a) := by
  have hP : PrimeSpectrum.comap φ Q ∈ Algebra.unramifiedLocus R S := by
    have hu := ScalarStalkJacobianTests.isUnramifiedAt (algebraMap R S) φ Q h
    dsimp only at hu
    rw [toAlgebra_algebraMap] at hu
    exact hu
  exact ScalarSourceOpenRigidity.exists_principal_neighborhood s
    (PrimeSpectrum.comap φ Q) hP

/-- Separable stalk equations also need finiteness only on the chosen source open. -/
theorem of_polynomial (s : A) [IsLocalization.Away s S]
    [Module.Finite S (KaehlerDifferential R S)] (φ : S →+* B) (Q : PrimeSpectrum B)
    (h : ScalarStalkPolynomialTests.Test (algebraMap R S) φ Q) :
    ∃ a : A, φ (algebraMap A S a) ∉ Q.asIdeal ∧
      PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen s ∧
      Algebra.FormallyUnramified R (Localization.Away a) := by
  have hu : let _ := (algebraMap R S).toAlgebra
      Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal := by
    let _ := (algebraMap R S).toAlgebra
    obtain ⟨n, z, P, hz, hP⟩ := h
    exact ScalarStalkDifferentialPolynomialRigidity.isUnramifiedAt φ Q z P hz hP
  dsimp only at hu
  rw [toAlgebra_algebraMap] at hu
  exact ScalarSourceOpenRigidity.exists_principal_neighborhood s
    (PrimeSpectrum.comap φ Q) hu

end FLT.Mazur.ScalarSourceOpenEquationNeighborhoods
