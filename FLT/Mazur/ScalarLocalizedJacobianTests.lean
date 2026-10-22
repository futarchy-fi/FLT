/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedJacobianDescent

/-!
# Localized coupled tests for full source stalks

The test supplies a finite coupled system over an avoiding scalar localization.
Clearing coefficients constructs the exact original-scalar stalk test. The
result detects the full differential module, including nonreduced structure;
no assumption on separability of individual source elements is imposed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedJacobianTests
open ScalarLocalizedSeparableEquations
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)

/-- Coupled localized equations, spanning differentials, and an invertible residue Jacobian. -/
def Condition : Prop :=
  let _ := σ.toAlgebra
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  ∃ hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal,
    ∃ (n : ℕ) (z : Fin n → A) (F : Fin n → MvPolynomial (Fin n) T),
      Submodule.span L (Set.range fun i ↦
        KaehlerDifferential.D R L (algebraMap A L (z i))) = ⊤ ∧
      (∀ i, MvPolynomial.eval₂ (stalkMap M σ φ Q hM)
        (fun j ↦ algebraMap A L (z j)) (F i) = 0) ∧
      Matrix.det (fun i j ↦ MvPolynomial.eval₂ (residueMap M σ φ Q hM)
        (fun k ↦ algebraMap B Q.asIdeal.ResidueField (φ (z k)))
        (MvPolynomial.pderiv j (F i))) ≠ 0

/-- Denominator clearing constructs the exact original-scalar coupled stalk test. -/
theorem stalk_test (h : Condition (T := T) M σ φ Q) :
    ScalarStalkJacobianTests.Test σ φ Q := by
  let _ := σ.toAlgebra
  obtain ⟨hM, n, z, F, hz, hF, hJ⟩ := h
  obtain ⟨P, hP, hdet⟩ := ScalarLocalizedJacobianDescent.exists_equations
    M σ φ Q hM z F hF hJ
  exact ⟨n, z, P, hz, hP, hdet⟩

/-- The constructed equations prove unramifiedness at the actual full source stalk. -/
theorem isUnramifiedAt (h : Condition (T := T) M σ φ Q) :
    let _ := σ.toAlgebra
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal :=
  ScalarStalkJacobianTests.isUnramifiedAt σ φ Q (stalk_test M σ φ Q h)

/-- Finite source differentials spread the localized coupled test to an avoiding annihilator. -/
theorem exists_annihilator
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : Condition (T := T) M σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal :=
  ScalarStalkJacobianTests.exists_annihilator σ φ Q hfg (stalk_test M σ φ Q h)

/-- The resulting principal neighborhood remains in the unchanged source ring. -/
theorem exists_principal
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : Condition (T := T) M σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨a, ha, hQa⟩ := exists_annihilator M σ φ Q hfg h
  exact ⟨a, hQa, ScalarDifferentialPrincipalRigidity.away_formallyUnramified a ha⟩

end FLT.Mazur.ScalarLocalizedJacobianTests
