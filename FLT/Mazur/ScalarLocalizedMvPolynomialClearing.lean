/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Clearing scalar denominators in coupled equations

Every multivariate polynomial over localized scalars has an original-scalar
multiple. Evaluation and all partial derivatives scale by the same scalar.
The scalar becomes a unit under every map out of the localization, so this
construction also applies over nonreduced scalar rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedMvPolynomialClearing
open MvPolynomial
variable {R T K ι : Type} [CommRing R] [CommRing T] [CommRing K]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Construct an original-scalar polynomial by clearing a single finite set of coefficients. -/
theorem exists_multiple (F : MvPolynomial ι T) :
    ∃ (b : M) (P : MvPolynomial ι R),
      map (algebraMap R T) P = C (algebraMap R T b) * F := by
  obtain ⟨⟨_, b, hb, rfl⟩, P, hP⟩ :=
    IsLocalization.exists_integer_multiple (M.map (C (σ := ι))) F
  refine ⟨⟨b, hb⟩, P, ?_⟩
  simpa only [Algebra.smul_def, algebraMap_def, map_C] using hP

omit [IsLocalization M T] in
/-- Evaluation of a cleared equation scales by its original scalar denominator. -/
theorem eval_multiple (μ : T →+* K) (z : ι → K) (b : M)
    (P : MvPolynomial ι R) (F : MvPolynomial ι T)
    (hP : map (algebraMap R T) P = C (algebraMap R T b) * F) :
    eval₂ (μ.comp (algebraMap R T)) z P =
      μ (algebraMap R T b) * eval₂ μ z F := by
  rw [← eval₂_map, hP, eval₂_mul, eval₂_C]

omit [IsLocalization M T] in
/-- Every partial derivative scales by that same denominator, without extra error terms. -/
theorem pderiv_multiple (b : M) (P : MvPolynomial ι R) (F : MvPolynomial ι T)
    (hP : map (algebraMap R T) P = C (algebraMap R T b) * F) (j : ι) :
    map (algebraMap R T) (pderiv j P) =
      C (algebraMap R T b) * pderiv j F := by
  rw [← pderiv_map, hP, pderiv_C_mul]

omit [IsLocalization M T] in
/-- The evaluated derivative of a cleared equation differs by an invertible scalar factor. -/
theorem eval_pderiv_multiple (μ : T →+* K) (z : ι → K) (b : M)
    (P : MvPolynomial ι R) (F : MvPolynomial ι T)
    (hP : map (algebraMap R T) P = C (algebraMap R T b) * F) (j : ι) :
    eval₂ (μ.comp (algebraMap R T)) z (pderiv j P) =
      μ (algebraMap R T b) * eval₂ μ z (pderiv j F) :=
  eval_multiple M μ z b _ _ (pderiv_multiple M b P F hP j)

/-- The clearing factor remains a unit after every scalar-localization coefficient map. -/
theorem factor_isUnit (μ : T →+* K) (b : M) : IsUnit (μ (algebraMap R T b)) :=
  (IsLocalization.map_units T b).map μ

end FLT.Mazur.ScalarLocalizedMvPolynomialClearing
