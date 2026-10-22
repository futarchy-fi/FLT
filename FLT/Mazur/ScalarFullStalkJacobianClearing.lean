/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFullStalkResidue
public import FLT.Mazur.ScalarLocalizedJacobianClearing

/-!
# Exact original equations for arbitrary full-stalk coordinates

The coordinates may be fractions in the full source stalk. Clearing only
scalar denominators constructs original-scalar equations for these same
coordinates. Their Jacobian remains a unit of the full stalk, not just a
nonzero element in a reduced quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFullStalkJacobianClearing
open MvPolynomial ScalarLocalizedSeparableEquations ScalarFullStalkResidue
variable {R T A B ι : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  [Fintype ι] [DecidableEq ι]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)

omit [Fintype ι] [DecidableEq ι] in
/-- Evaluation of arbitrary stalk coordinates commutes with the exact test residue map. -/
theorem eval_toResidue (z : ι → Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (F : MvPolynomial ι T) :
    toResidue φ Q (eval₂ (stalkMap M σ φ Q hM) z F) =
      eval₂ (residueMap M σ φ Q hM) (fun i ↦ toResidue φ Q (z i)) F := by
  rw [hom_eval₂, toResidue_stalkMap]

/-- A nonsingular residue Jacobian gives an invertible determinant in the full source stalk. -/
theorem jacobian_isUnit (z : ι → Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (F : ι → MvPolynomial ι T)
    (hJ : Matrix.det (fun i j ↦ eval₂ (residueMap M σ φ Q hM)
      (fun k ↦ toResidue φ Q (z k)) (pderiv j (F i))) ≠ 0) :
    IsUnit (Matrix.det (fun i j ↦ eval₂ (stalkMap M σ φ Q hM) z (pderiv j (F i)))) := by
  apply (det_isUnit_iff φ Q _).mpr
  change Matrix.det (fun i j ↦ toResidue φ Q
    (eval₂ (stalkMap M σ φ Q hM) z (pderiv j (F i)))) ≠ 0
  simpa only [eval_toResidue] using hJ

/-- Construct exact original-scalar equations and a unit Jacobian without lifting coordinates. -/
theorem exists_equations (z : ι → Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (F : ι → MvPolynomial ι T)
    (hF : ∀ i, eval₂ (stalkMap M σ φ Q hM) z (F i) = 0)
    (hJ : Matrix.det (fun i j ↦ eval₂ (residueMap M σ φ Q hM)
      (fun k ↦ toResidue φ Q (z k)) (pderiv j (F i))) ≠ 0) :
    ∃ P : ι → MvPolynomial ι R,
      (∀ i, eval₂ ((algebraMap A
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)).comp σ) z (P i) = 0) ∧
      IsUnit (Matrix.det (fun i j ↦ eval₂ ((algebraMap A
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)).comp σ) z
        (pderiv j (P i)))) := by
  choose b P hP using fun i ↦ ScalarLocalizedMvPolynomialClearing.exists_multiple M (F i)
  refine ⟨P, ?_, ?_⟩
  · intro i
    rw [← stalkMap_comp (T := T) M σ φ Q hM,
      ScalarLocalizedMvPolynomialClearing.eval_multiple M _ z (b i) (P i) (F i) (hP i),
      hF i, mul_zero]
  · rw [← stalkMap_comp (T := T) M σ φ Q hM,
      ScalarLocalizedJacobianClearing.det_multiple M _ z b P F hP]
    exact (IsUnit.prod_iff.mpr (fun i _ ↦
      ScalarLocalizedMvPolynomialClearing.factor_isUnit M (stalkMap M σ φ Q hM) (b i))).mul
      (jacobian_isUnit M σ φ Q hM z F hJ)

end FLT.Mazur.ScalarFullStalkJacobianClearing
