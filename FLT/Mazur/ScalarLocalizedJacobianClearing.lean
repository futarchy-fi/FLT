/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedMvPolynomialClearing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Coupled Jacobians after clearing localized scalar coefficients

Clearing each polynomial scales the corresponding Jacobian row by a unit.
The determinant scales by the product of these units. Consequently a system
with nonsingular residue Jacobian descends to the unchanged scalar ring,
without reducedness or separability assumptions on individual elements.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedJacobianClearing
open MvPolynomial ScalarLocalizedMvPolynomialClearing
variable {R T K ι : Type} [CommRing R] [CommRing T] [CommRing K]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  [Fintype ι] [DecidableEq ι]

omit [IsLocalization M T] in
/-- Clearing each equation multiplies its Jacobian determinant by the product of its factors. -/
theorem det_multiple (μ : T →+* K) (z : ι → K) (b : ι → M)
    (P : ι → MvPolynomial ι R) (F : ι → MvPolynomial ι T)
    (hP : ∀ i, map (algebraMap R T) (P i) = C (algebraMap R T (b i)) * F i) :
    Matrix.det (fun i j ↦ eval₂ (μ.comp (algebraMap R T)) z (pderiv j (P i))) =
      (∏ i, μ (algebraMap R T (b i))) *
        Matrix.det (fun i j ↦ eval₂ μ z (pderiv j (F i))) := by
  have he : (fun i j ↦ eval₂ (μ.comp (algebraMap R T)) z (pderiv j (P i))) =
      (fun i j ↦ μ (algebraMap R T (b i)) * eval₂ μ z (pderiv j (F i))) := by
    funext i j
    exact eval_pderiv_multiple M μ z (b i) (P i) (F i) (hP i) j
  rw [he]
  exact Matrix.det_mul_column _ _

/-- A nonzero residue determinant stays nonzero after clearing all scalar denominators. -/
theorem det_multiple_ne_zero (μ : T →+* K) (z : ι → K) (b : ι → M)
    (P : ι → MvPolynomial ι R) (F : ι → MvPolynomial ι T)
    (hP : ∀ i, map (algebraMap R T) (P i) = C (algebraMap R T (b i)) * F i)
    (hJ : Matrix.det (fun i j ↦ eval₂ μ z (pderiv j (F i))) ≠ 0) :
    Matrix.det (fun i j ↦ eval₂ (μ.comp (algebraMap R T)) z (pderiv j (P i))) ≠ 0 := by
  rw [det_multiple M μ z b P F hP]
  have hu : IsUnit (∏ i, μ (algebraMap R T (b i))) :=
    IsUnit.prod_iff.mpr (fun i _ ↦ factor_isUnit M μ (b i))
  exact fun h ↦ hJ (hu.mul_right_eq_zero.mp h)

/-- Construct a full original-scalar system with its nonsingular residue Jacobian preserved. -/
theorem exists_system (μ : T →+* K) (z : ι → K) (F : ι → MvPolynomial ι T)
    (hJ : Matrix.det (fun i j ↦ eval₂ μ z (pderiv j (F i))) ≠ 0) :
    ∃ (b : ι → M) (P : ι → MvPolynomial ι R),
      (∀ i, map (algebraMap R T) (P i) = C (algebraMap R T (b i)) * F i) ∧
      Matrix.det (fun i j ↦ eval₂ (μ.comp (algebraMap R T)) z (pderiv j (P i))) ≠ 0 := by
  choose b P hP using fun i ↦ exists_multiple M (F i)
  exact ⟨b, P, hP, det_multiple_ne_zero M μ z b P F hP hJ⟩

end FLT.Mazur.ScalarLocalizedJacobianClearing
