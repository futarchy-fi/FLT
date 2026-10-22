/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFiniteTypeFiberTests
public import FLT.Mazur.ScalarSourceOpenBaseFiniteness

/-!
# Source-open rigidity constructed from vanishing differential fibers

Finite type is required only on a chosen source open. The test constructs
its polynomial presentation and kernel equations, and then a smaller
principal rigidity neighborhood in the unchanged original source.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenFiberTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- A source open of finite type with zero differential fiber at the exact test inverse image. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (a : A) (P : PrimeSpectrum (Localization.Away a)),
    PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q ∧
    Algebra.FiniteType R (Localization.Away a) ∧
    ScalarFiniteTypeFiberTests.FiberVanishes
      (algebraMap R (Localization.Away a)) (RingHom.id _) P

/-- Construct the rigidity neighborhood inside the chosen original source open. -/
theorem neighborhood [Algebra R A] (a : A) (P : PrimeSpectrum (Localization.Away a))
    [Algebra.FiniteType R (Localization.Away a)]
    (h : ScalarFiniteTypeFiberTests.FiberVanishes
      (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    ∃ b : A, algebraMap A (Localization.Away a) b ∉ P.asIdeal ∧
      PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a ∧
      Algebra.FormallyUnramified R (Localization.Away b) := by
  have hft : let _ := (algebraMap R (Localization.Away a)).toAlgebra
      Algebra.FiniteType R (Localization.Away a) := by
    rw [toAlgebra_algebraMap]
    infer_instance
  have hu := ScalarFiniteTypeFiberTests.isUnramifiedAt
    (algebraMap R (Localization.Away a)) (RingHom.id _) P hft h
  dsimp only at hu
  rw [toAlgebra_algebraMap] at hu
  exact ScalarSourceOpenRigidity.exists_principal_neighborhood a P hu

/-- The constructed original-source principal open avoids the actual target prime. -/
theorem exists_principal (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨a, P, hP, hft, h⟩ := h
  let _ := hft
  obtain ⟨b, hb, _, hu⟩ := neighborhood a P h
  refine ⟨b, ?_, hu⟩
  change b ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact hb

variable {k : Type} [CommRing k] [Algebra k R] [Algebra k A] [Algebra R A]
  [IsScalarTower k R A]

/-- Avoidance constructs the prime, and smaller-base finite type supplies the presentation. -/
theorem test_of_avoidance (φ : A →+* B) (Q : PrimeSpectrum B) (a : A)
    (ha : φ a ∉ Q.asIdeal) [Algebra.FiniteType k (Localization.Away a)]
    (h : ∀ P : PrimeSpectrum (Localization.Away a),
      PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q →
      ScalarFiniteTypeFiberTests.FiberVanishes
        (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    Test (algebraMap R A) φ Q := by
  obtain ⟨P, hP⟩ := ScalarSourceOpenElementEquations.exists_prime φ Q a ha
  dsimp -zeta only [Test]
  rw [toAlgebra_algebraMap]
  exact ⟨a, P, hP, Algebra.FiniteType.of_restrictScalars_finiteType k R _, h P hP⟩

end FLT.Mazur.ScalarSourceOpenFiberTests
