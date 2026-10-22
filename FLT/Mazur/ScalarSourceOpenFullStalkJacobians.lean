/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFullStalkPresentation
public import FLT.Mazur.ScalarSourceOpenBaseFiniteness

/-!
# Original source opens from fractional full-stalk presentations

Coordinates may be arbitrary elements of the stalk of a chosen source open.
Only differentials on that source open need be finite. The annihilator
numerator constructs a smaller principal neighborhood in the original source.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenFullStalkJacobians
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Finite local differentials and exact fractional full-stalk equations on a source open. -/
def OnOpen [Algebra R A] (M : Submonoid R) (a : A)
    (P : PrimeSpectrum (Localization.Away a)) : Prop :=
  Module.Finite (Localization.Away a) (KaehlerDifferential R (Localization.Away a)) ∧
    ScalarFullStalkJacobianTests.Condition (T := Localization M) M
      (algebraMap R (Localization.Away a)) (RingHom.id _) P

/-- The chosen source open contains the exact inverse image of the associated test prime. -/
def Test (M : Submonoid R) (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (a : A) (P : PrimeSpectrum (Localization.Away a)),
    PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q ∧
    OnOpen M a P

/-- Fractional full-stalk equations construct an avoiding neighborhood inside the source open. -/
theorem neighborhood [Algebra R A] (M : Submonoid R) (a : A)
    (P : PrimeSpectrum (Localization.Away a)) (h : OnOpen M a P) :
    ∃ b : A, algebraMap A (Localization.Away a) b ∉ P.asIdeal ∧
      PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a ∧
      Algebra.FormallyUnramified R (Localization.Away b) := by
  obtain ⟨hfg, hJ⟩ := h
  let _ := hfg
  have hu := ScalarFullStalkJacobianTests.isUnramifiedAt M
    (algebraMap R (Localization.Away a)) (RingHom.id _) P hJ
  dsimp only at hu
  rw [toAlgebra_algebraMap] at hu
  exact ScalarSourceOpenRigidity.exists_principal_neighborhood a P hu

/-- The original-source principal open avoids the actual test prime. -/
theorem exists_principal (M : Submonoid R) (σ : R →+* A) (φ : A →+* B)
    (Q : PrimeSpectrum B) (h : Test M σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨a, P, hP, hJ⟩ := h
  obtain ⟨b, hb, _, hu⟩ := neighborhood M a P hJ
  refine ⟨b, ?_, hu⟩
  change b ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact hb

variable {k : Type} [CommRing k] [Algebra k R] [Algebra k A] [Algebra R A]
  [IsScalarTower k R A]

/-- Smaller-base finite type and denominator avoidance construct the local finiteness and prime. -/
theorem test_of_avoidance (M : Submonoid R) (φ : A →+* B) (Q : PrimeSpectrum B)
    (a : A) (ha : φ a ∉ Q.asIdeal) [Algebra.EssFiniteType k (Localization.Away a)]
    (hJ : ∀ P : PrimeSpectrum (Localization.Away a),
      PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q →
      ScalarFullStalkJacobianTests.Condition (T := Localization M) M
        (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    Test M (algebraMap R A) φ Q := by
  obtain ⟨P, hP⟩ := ScalarSourceOpenElementEquations.exists_prime φ Q a ha
  dsimp -zeta only [Test]
  rw [toAlgebra_algebraMap]
  exact ⟨a, P, hP, ScalarSourceOpenBaseFiniteness.finite_differentials (k := k), hJ P hP⟩

end FLT.Mazur.ScalarSourceOpenFullStalkJacobians
