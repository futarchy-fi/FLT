/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedSourceOpenTests

/-!
# Constructing source-open differential finiteness from a smaller base

Essential finite type over a smaller base supplies finite differentials over
the exact scalar ring. The scalar ring need not be Noetherian or finite type.
Avoidance constructs the source prime, and separability over localized scalars
then gives an original-source rigidity neighborhood without supplying equations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenBaseFiniteness
variable {k R A S B : Type} [CommRing k] [CommRing R] [CommRing A]
  [CommRing S] [CommRing B] [Algebra k R]

/-- Essential finite type over a smaller base constructs finite exact-scalar differentials. -/
theorem finite_differentials [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.EssFiniteType k S] : Module.Finite S (KaehlerDifferential R S) := by
  let _ : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_comp k R S
  infer_instance

variable [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- Local base finiteness and localized scalar separability construct original rigidity opens. -/
theorem exists_neighborhood (M : Submonoid R) (a : A)
    [Algebra.EssFiniteType k (Localization.Away a)]
    (P : PrimeSpectrum (Localization.Away a))
    (hs : ScalarLocalizedSourceOpenTests.Condition M
      (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    ∃ b : A, algebraMap A (Localization.Away a) b ∉ P.asIdeal ∧
      PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a ∧
      Algebra.FormallyUnramified R (Localization.Away b) := by
  let _ := finite_differentials (k := k) (R := R) (S := Localization.Away a)
  obtain ⟨hM, hsep⟩ := hs
  exact ScalarLocalizedSeparableTests.exists_neighborhood M a P hM hsep

/-- Avoidance constructs the source prime; local base finiteness supplies its differentials. -/
theorem exists_neighborhood_of_avoidance (M : Submonoid R) (φ : A →+* B)
    (Q : PrimeSpectrum B) (a : A) (ha : φ a ∉ Q.asIdeal)
    [Algebra.EssFiniteType k (Localization.Away a)]
    (hs : ∀ P : PrimeSpectrum (Localization.Away a),
      PrimeSpectrum.comap (algebraMap A (Localization.Away a)) P = PrimeSpectrum.comap φ Q →
      ScalarLocalizedSourceOpenTests.Condition M
        (algebraMap R (Localization.Away a)) (RingHom.id _) P) :
    ∃ b : A, φ b ∉ Q.asIdeal ∧
      PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a ∧
      Algebra.FormallyUnramified R (Localization.Away b) := by
  obtain ⟨P, hP⟩ := ScalarSourceOpenElementEquations.exists_prime φ Q a ha
  obtain ⟨b, hb, hba, hu⟩ := exists_neighborhood (k := k) M a P (hs P hP)
  refine ⟨b, ?_, hba, hu⟩
  change b ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact hb

end FLT.Mazur.ScalarSourceOpenBaseFiniteness
