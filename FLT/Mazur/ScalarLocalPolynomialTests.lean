/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalPolynomialResidueRigidity

/-!
# Finite scalar equation tests constructed from essential finite type

A test consists of finitely many differential generators and separable
polynomial equations in the source stalk. Finite differentials construct the
generators from pointwise equations. Essential finite type supplies this
finiteness without any Noetherian assumption on the scalar ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalPolynomialTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- A polynomial over the exact scalar map, vanishing in the specified source stalk. -/
def Equation (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (x : A) (P : Polynomial R) : Prop :=
  algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (P.eval₂ σ x) = 0 ∧
  (P.map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp σ)).Separable

/-- Finite differential generators with local equations; algebra generation is not required. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (n : ℕ) (z : Fin n → A) (P : Fin n → Polynomial R),
    Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤ ∧
    ∀ i, Equation σ φ Q (z i) (P i)

/-- The finite equation test constructs a global differential annihilator avoiding the prime. -/
theorem exists_annihilator (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  obtain ⟨n, z, P, hz, hP⟩ := h
  exact ScalarLocalPolynomialResidueRigidity.exists_annihilator_of_local φ Q z P hz
    (fun i ↦ (hP i).1) (fun i ↦ (hP i).2)

/-- Finite differentials choose the needed finite source elements from pointwise local equations. -/
theorem test_of_finite_differentials (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : ∀ x : A, ∃ P : Polynomial R, Equation σ φ Q x P) : Test σ φ Q := by
  let _ := σ.toAlgebra
  let _ := hfg
  obtain ⟨n, z, hz⟩ := ScalarFiniteDifferentialGenerators.exists_generators (R := R) (A := A)
  choose P hP using fun i ↦ h (z i)
  exact ⟨n, z, P, hz, hP⟩

/-- Essential finite type is sufficient; finite algebra generation is not an input. -/
theorem test_of_essFiniteType (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hft : let _ := σ.toAlgebra; Algebra.EssFiniteType R A)
    (h : ∀ x : A, ∃ P : Polynomial R, Equation σ φ Q x P) : Test σ φ Q := by
  let _ := σ.toAlgebra
  let _ := hft
  exact test_of_finite_differentials σ φ Q inferInstance h

/-- These equations prove actual membership in the unramified locus. -/
theorem mem_unramifiedLocus (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    PrimeSpectrum.comap φ Q ∈ Algebra.unramifiedLocus R A := by
  let _ := σ.toAlgebra
  obtain ⟨a, ha, hQ⟩ := exists_annihilator σ φ Q h
  change PrimeSpectrum.comap φ Q ∈ Algebra.unramifiedLocus R A
  rw [Algebra.unramifiedLocus_eq_compl_support]
  intro hp
  exact hQ (Module.annihilator_le_of_mem_support hp ha)

end FLT.Mazur.ScalarLocalPolynomialTests
