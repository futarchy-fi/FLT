/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarDifferentialPolynomialAnnihilator
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Jacobian determinants annihilate the full relative differential module

Coupled equations for algebra generators give a matrix killing their universal
differentials. Multiplication by its adjugate constructs an annihilator of the
entire module. This works over arbitrary scalar rings and nonreduced algebras;
it requires neither a complete-intersection presentation nor monic equations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarDifferentialJacobianAnnihilator
open MvPolynomial
variable {R A M ι : Type} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M]
  [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
/-- The finite multivariable chain rule holds for any relative derivation. -/
theorem map_aeval_sum (d : Derivation R A M) (x : ι → A) (P : MvPolynomial ι R) :
    d (aeval x P) = ∑ i, aeval x (pderiv i P) • d (x i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp only [aeval_C, Derivation.map_algebraMap, pderiv_C, map_zero,
      zero_smul, Finset.sum_const_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hP, pderiv_X, smul_eq_mul,
      map_add, map_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, ite_smul, one_smul,
      zero_smul, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The adjugate turns matrix relations in any module into determinant annihilation. -/
theorem det_smul_eq_zero (N : Matrix ι ι A) (v : ι → M)
    (h : ∀ i, ∑ j, N i j • v j = 0) (i : ι) : N.det • v i = 0 := by
  have H : ∑ j, N.adjugate i j • (∑ k, N j k • v k) = 0 := by
    simp only [h, smul_zero, Finset.sum_const_zero]
  have E : ∑ j, N.adjugate i j • (∑ k, N j k • v k) =
      ∑ k, (N.adjugate * N) i k • v k := by
    simp only [Finset.smul_sum, ← mul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  rw [E, Matrix.adjugate_mul] at H
  simpa only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using H

/-- A nonzero residue determinant excludes the original test prime. -/
theorem determinant_not_mem {B : Type} [CommRing B] (φ : A →+* B)
    (Q : PrimeSpectrum B) (N : Matrix ι ι A)
    (h : Matrix.det (N.map ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0) :
    φ N.det ∉ Q.asIdeal := by
  intro hQ
  apply h
  exact (((algebraMap B Q.asIdeal.ResidueField).comp φ).map_det N).symm.trans
    (Ideal.algebraMap_residueField_eq_zero.mpr hQ)

/-- A square family of equations gives a concrete annihilator of all source differentials. -/
theorem jacobian_mem_annihilator (x : ι → A) (P : ι → MvPolynomial ι R)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) (hP : ∀ i, aeval x (P i) = 0) :
    Matrix.det (fun i j ↦ aeval x (pderiv j (P i))) ∈
      Module.annihilator A (KaehlerDifferential R A) := by
  apply ScalarDifferentialPolynomialAnnihilator.mem_annihilator_of_generators (Set.range x) hx
  rintro _ ⟨i, rfl⟩
  apply det_smul_eq_zero _ (fun j ↦ KaehlerDifferential.D R A (x j)) _ i
  intro j
  rw [← map_aeval_sum, hP, map_zero]

/-- The Jacobian principal localization is formally unramified over the exact scalar ring. -/
theorem jacobian_away_formallyUnramified (x : ι → A) (P : ι → MvPolynomial ι R)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) (hP : ∀ i, aeval x (P i) = 0) :
    Algebra.FormallyUnramified R
      (Localization.Away (Matrix.det (fun i j ↦ aeval x (pderiv j (P i))))) :=
  ScalarDifferentialPrincipalRigidity.away_formallyUnramified _
    (jacobian_mem_annihilator x P hx hP)

end FLT.Mazur.ScalarDifferentialJacobianAnnihilator
