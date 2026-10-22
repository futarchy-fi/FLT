/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedJacobianTests
public import FLT.Mazur.ScalarSourceOpenBaseFiniteness
public import FLT.Mazur.ScalarSourceOpenJacobianTests

/-!
# Original source opens from localized coupled equations

Source neighborhoods and scalar localizations may vary independently at each
test prime. Clearing scalar coefficients constructs the exact coupled test on
the chosen source open. Essential finite type over a smaller base supplies
finite differentials without any Noetherianity assumption on the scalar ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenLocalizedJacobians
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Finite differentials and localized equations on a specified principal source open. -/
def OnOpen [Algebra R A] (M : Submonoid R) (a : A)
    (P : PrimeSpectrum (Localization.Away a)) : Prop :=
  Module.Finite (Localization.Away a) (KaehlerDifferential R (Localization.Away a)) ∧
    ScalarLocalizedJacobianTests.Condition (T := Localization M) M
      (algebraMap R (Localization.Away a)) (RingHom.id _) P

/-- Localized coupled equations on a finite-differential source open at the exact source prime. -/
def Test (M : Submonoid R) (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (a : A) (P : PrimeSpectrum (Localization.Away a)),
    PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q ∧
    OnOpen M a P

/-- Clear coefficients on the chosen open, retaining its full stalk and exact source prime. -/
theorem source_open_test (M : Submonoid R) (σ : R →+* A) (φ : A →+* B)
    (Q : PrimeSpectrum B) (h : Test M σ φ Q) :
    ScalarSourceOpenJacobianTests.Test σ φ Q := by
  let _ := σ.toAlgebra
  obtain ⟨a, P, hP, hfg, hJ⟩ := h
  exact ⟨a, P, hP, hfg, ScalarLocalizedJacobianTests.stalk_test M
    (algebraMap R (Localization.Away a)) (RingHom.id _) P hJ⟩

/-- Construct an avoiding rigidity open in the original source from the localized system. -/
theorem exists_principal (M : Submonoid R) (σ : R →+* A) (φ : A →+* B)
    (Q : PrimeSpectrum B) (h : Test M σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) :=
  ScalarSourceOpenJacobianTests.exists_principal σ φ Q (source_open_test M σ φ Q h)

variable {k : Type} [CommRing k] [Algebra k R] [Algebra k A] [Algebra R A]
  [IsScalarTower k R A]

/-- Smaller-base finiteness and denominator avoidance construct the source-open test. -/
theorem test_of_avoidance (M : Submonoid R) (φ : A →+* B) (Q : PrimeSpectrum B)
    (a : A) (ha : φ a ∉ Q.asIdeal) [Algebra.EssFiniteType k (Localization.Away a)]
    (hJ : ∀ P : PrimeSpectrum (Localization.Away a),
      PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q →
      ScalarLocalizedJacobianTests.Condition (T := Localization M) M
        (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    Test M (algebraMap R A) φ Q := by
  obtain ⟨P, hP⟩ := ScalarSourceOpenElementEquations.exists_prime φ Q a ha
  dsimp -zeta only [Test]
  rw [toAlgebra_algebraMap]
  exact ⟨a, P, hP, ScalarSourceOpenBaseFiniteness.finite_differentials (k := k), hJ P hP⟩

/-- The constructed neighborhood lies inside the supplied source open and avoids the test prime. -/
theorem exists_neighborhood (M : Submonoid R) (φ : A →+* B) (Q : PrimeSpectrum B)
    (a : A) (ha : φ a ∉ Q.asIdeal) [Algebra.EssFiniteType k (Localization.Away a)]
    (hJ : ∀ P : PrimeSpectrum (Localization.Away a),
      PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q →
      ScalarLocalizedJacobianTests.Condition (T := Localization M) M
        (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    ∃ b : A, φ b ∉ Q.asIdeal ∧
      PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a ∧
      Algebra.FormallyUnramified R (Localization.Away b) := by
  obtain ⟨P, hP⟩ := ScalarSourceOpenElementEquations.exists_prime φ Q a ha
  let _ := ScalarSourceOpenBaseFiniteness.finite_differentials
    (k := k) (R := R) (S := Localization.Away a)
  obtain ⟨b, hb, hba, hu⟩ := ScalarSourceOpenEquationNeighborhoods.of_jacobian
    (R := R) a (RingHom.id _) P (ScalarLocalizedJacobianTests.stalk_test M
      (algebraMap R (Localization.Away a)) (RingHom.id _) P (hJ P hP))
  refine ⟨b, ?_, hba, hu⟩
  change b ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact hb

end FLT.Mazur.ScalarSourceOpenLocalizedJacobians
