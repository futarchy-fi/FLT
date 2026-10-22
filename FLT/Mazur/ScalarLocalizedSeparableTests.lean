/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedSeparableEquations
public import FLT.Mazur.ScalarSourceOpenElementEquations

/-!
# Finite tests and source neighborhoods from localized scalar separability

Finite differentials select finitely many normalized minimal polynomials.
When finiteness is known only on a principal source open, the resulting
rigidity neighborhood is constructed inside that open in the original source.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedSeparableTests
open ScalarLocalizedSeparableEquations
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]

/-- Localized scalar separability constructs a finite exact scalar polynomial test. -/
theorem test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (hs : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      ∀ z : A, IsSeparable T
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)) :
    ScalarLocalPolynomialTests.Test σ φ Q := by
  apply ScalarLocalPolynomialTests.test_of_finite_differentials σ φ Q hfg
  intro z
  exact exists_equation M σ φ Q hM z (hs z)

/-- The constructed test supplies an avoiding annihilator of the entire differential module. -/
theorem exists_annihilator (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (hs : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      ∀ z : A, IsSeparable T
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal :=
  ScalarLocalPolynomialTests.exists_annihilator σ φ Q (test M σ φ Q hM hfg hs)

variable [Algebra R A]

/-- On a finite-differential source open, localized scalar separability constructs rigidity. -/
theorem exists_neighborhood (s : A)
    [Module.Finite (Localization.Away s) (KaehlerDifferential R (Localization.Away s))]
    (P : PrimeSpectrum (Localization.Away s))
    (hM : ∀ m ∈ M, algebraMap R (Localization.Away s) m ∉ P.asIdeal)
    (hs : let _ := (stalkMap (T := T) M (algebraMap R (Localization.Away s))
      (RingHom.id _) P hM).toAlgebra
      ∀ z : Localization.Away s, IsSeparable T
        (algebraMap (Localization.Away s)
          (Localization.AtPrime (PrimeSpectrum.comap (RingHom.id _) P).asIdeal) z)) :
    ∃ a : A, algebraMap A (Localization.Away s) a ∉ P.asIdeal ∧
      PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen s ∧
      Algebra.FormallyUnramified R (Localization.Away a) := by
  have hfg : let _ := (algebraMap R (Localization.Away s)).toAlgebra
      Module.Finite (Localization.Away s) (KaehlerDifferential R (Localization.Away s)) := by
    rw [toAlgebra_algebraMap]
    infer_instance
  have ht := test M (algebraMap R (Localization.Away s)) (RingHom.id _) P hM hfg hs
  have hu := ScalarLocalPolynomialTests.mem_unramifiedLocus
    (algebraMap R (Localization.Away s)) (RingHom.id _) P ht
  dsimp only at hu
  rw [toAlgebra_algebraMap] at hu
  exact ScalarSourceOpenRigidity.exists_principal_neighborhood s P hu

end FLT.Mazur.ScalarLocalizedSeparableTests
