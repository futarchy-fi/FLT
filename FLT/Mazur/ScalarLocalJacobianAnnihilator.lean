/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFiniteDifferentialGenerators
public import FLT.Mazur.ScalarDifferentialJacobianAnnihilator

/-!
# Jacobian annihilators from equations valid only in source stalks

Clearing each equation multiplies its differential row by the square of the
clearing element. The adjugate then gives the Jacobian determinant times the
product of those squares as an annihilator of all relative differentials.
At a test prime with nonsingular residue Jacobian this annihilator is nonzero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalJacobianAnnihilator
open MvPolynomial ScalarDifferentialJacobianAnnihilator
variable {R A B ι : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Clearing a coupled equation kills its differential row after multiplying by a square. -/
theorem cleared_row_eq_zero (z : ι → A) (t : A) (P : MvPolynomial ι R)
    (hP : t * aeval z P = 0) :
    ∑ j, (t ^ 2 * aeval z (pderiv j P)) • KaehlerDifferential.D R A (z j) = 0 := by
  have h := congrArg (fun a ↦ t • KaehlerDifferential.D R A a) hP
  rw [Derivation.leibniz, smul_add] at h
  simp only [smul_smul, hP, zero_smul, add_zero, map_zero, smul_zero] at h
  have h' : t ^ 2 • KaehlerDifferential.D R A (aeval z P) = 0 := by
    simpa only [pow_two] using h
  rw [map_aeval_sum] at h'
  simpa only [Finset.smul_sum, smul_smul] using h'

/-- The explicit cleared Jacobian determinant annihilates the full differential module. -/
theorem cleared_jacobian_mem_annihilator (z t : ι → A) (P : ι → MvPolynomial ι R)
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, t i * aeval z (P i) = 0) :
    ((∏ i, t i ^ 2) * Matrix.det (fun i j ↦ aeval z (pderiv j (P i)))) ∈
      Module.annihilator A (KaehlerDifferential R A) := by
  rw [← Matrix.det_mul_column (fun i ↦ t i ^ 2) (fun i j ↦ aeval z (pderiv j (P i)))]
  apply ScalarFiniteDifferentialGenerators.mem_annihilator z hz
  intro i
  apply det_smul_eq_zero _ (fun j ↦ KaehlerDifferential.D R A (z j)) _ i
  intro j
  exact cleared_row_eq_zero z (t j) (P j) (hP j)

/-- Clearing elements outside the test prime preserve a nonzero residue Jacobian. -/
theorem exists_annihilator_of_cleared (φ : A →+* B) (Q : PrimeSpectrum B)
    (z t : ι → A) (P : ι → MvPolynomial ι R)
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, t i * aeval z (P i) = 0) (ht : ∀ i, φ (t i) ∉ Q.asIdeal)
    (hJ : Matrix.det (Matrix.map (fun i j ↦ aeval z (pderiv j (P i)))
      ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  refine ⟨_, cleared_jacobian_mem_annihilator z t P hz hP, ?_⟩
  rw [map_mul]
  intro h
  rcases Q.isPrime.mem_or_mem h with h | h
  · rw [map_prod] at h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rw [map_pow] at hi
    exact ht i (Q.isPrime.mem_of_pow_mem 2 hi)
  · exact determinant_not_mem φ Q _ hJ h

/-- Source-stalk equations construct their own clearing elements and full annihilator. -/
theorem exists_annihilator_of_local (φ : A →+* B) (Q : PrimeSpectrum B)
    (z : ι → A) (P : ι → MvPolynomial ι R)
    (hz : Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤)
    (hP : ∀ i, algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (aeval z (P i)) = 0)
    (hJ : Matrix.det (Matrix.map (fun i j ↦ aeval z (pderiv j (P i)))
      ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  have hc (i : ι) : ∃ t : (PrimeSpectrum.comap φ Q).asIdeal.primeCompl,
      (t : A) * aeval z (P i) = 0 :=
    (IsLocalization.map_eq_zero_iff (PrimeSpectrum.comap φ Q).asIdeal.primeCompl
      (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) _).mp (hP i)
  choose t ht using hc
  exact exists_annihilator_of_cleared φ Q z (fun i ↦ t i) P hz ht
    (fun i ↦ (t i).property) hJ

end FLT.Mazur.ScalarLocalJacobianAnnihilator

namespace FLT.Mazur.ScalarLocalJacobianTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Finite differential generators and coupled scalar equations in the actual source stalk. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (n : ℕ) (z : Fin n → A) (P : Fin n → MvPolynomial (Fin n) R),
    Submodule.span A (Set.range fun i ↦ KaehlerDifferential.D R A (z i)) = ⊤ ∧
    (∀ i, algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (MvPolynomial.eval₂ σ z (P i)) = 0) ∧
    Matrix.det (Matrix.map (fun i j ↦ MvPolynomial.eval₂ σ z (MvPolynomial.pderiv j (P i)))
      ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0

/-- A coupled local equation test constructs an annihilator avoiding the specified prime. -/
theorem exists_annihilator (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  obtain ⟨n, z, P, hz, hP, hJ⟩ := h
  exact ScalarLocalJacobianAnnihilator.exists_annihilator_of_local φ Q z P hz hP hJ

end FLT.Mazur.ScalarLocalJacobianTests
