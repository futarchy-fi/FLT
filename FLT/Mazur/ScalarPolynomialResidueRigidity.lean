/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarDifferentialPolynomialAnnihilator
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Residue separability constructs nonvanishing differential denominators

The polynomial equations are over the actual scalar ring. Separability is
checked after mapping to the residue field of a specified test prime. This
constructs a source differential annihilator avoiding that test prime; the
prime need not be minimal. The test ring may have nilpotents.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarPolynomialResidueRigidity
open Polynomial
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]

/-- Separability after a coefficient map makes the root's evaluated derivative nonzero. -/
theorem derivative_image_ne_zero {K : Type} [CommRing K] [Nontrivial K]
    (φ : A →+* K) (x : A) (P : R[X]) (hP : aeval x P = 0)
    (hs : (P.map (φ.comp (algebraMap R A))).Separable) :
    φ (aeval x P.derivative) ≠ 0 := by
  have he (Q : R[X]) : (Q.map (φ.comp (algebraMap R A))).eval (φ x) =
      φ (aeval x Q) := by
    rw [eval_map, ← hom_eval₂]
    rfl
  have hz : (P.map (φ.comp (algebraMap R A))).eval (φ x) = 0 := by
    rw [he, hP, map_zero]
  have hn := hs.eval₂_derivative_ne_zero (RingHom.id K) hz
  simpa only [eval₂_id, derivative_map, he] using hn

/-- A residue-separable equation avoids the specified prime, including embedded primes. -/
theorem derivative_not_mem (φ : A →+* B) (Q : PrimeSpectrum B)
    (x : A) (P : R[X]) (hP : aeval x P = 0)
    (hs : (P.map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp
      (algebraMap R A))).Separable) : φ (aeval x P.derivative) ∉ Q.asIdeal := by
  intro h
  exact derivative_image_ne_zero ((algebraMap B Q.asIdeal.ResidueField).comp φ)
    x P hP hs (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- Finitely many residue-separable equations give one product avoiding the test prime. -/
theorem product_not_mem {ι : Type} [Fintype ι] (φ : A →+* B) (Q : PrimeSpectrum B)
    (x : ι → A) (P : ι → R[X]) (hP : ∀ i, aeval (x i) (P i) = 0)
    (hs : ∀ i, ((P i).map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp
      (algebraMap R A))).Separable) :
    φ (∏ i, aeval (x i) (P i).derivative) ∉ Q.asIdeal := by
  rw [map_prod]
  intro h
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact derivative_not_mem φ Q (x i) (P i) (hP i) (hs i) hi

/-- Actual equations and residue separability construct the required source annihilator. -/
theorem exists_annihilator {ι : Type} [Finite ι] (φ : A →+* B) (Q : PrimeSpectrum B)
    (x : ι → A) (P : ι → R[X]) (hx : Algebra.adjoin R (Set.range x) = ⊤)
    (hP : ∀ i, aeval (x i) (P i) = 0)
    (hs : ∀ i, ((P i).map (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp
      (algebraMap R A))).Separable) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := Fintype.ofFinite ι
  exact ⟨_, ScalarDifferentialPolynomialAnnihilator.product_mem_annihilator x P hx hP,
    product_not_mem φ Q x P hP hs⟩

end FLT.Mazur.ScalarPolynomialResidueRigidity
