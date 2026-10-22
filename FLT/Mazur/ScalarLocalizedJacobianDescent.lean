/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedJacobianClearing
public import FLT.Mazur.ScalarLocalizedSeparableEquations
public import FLT.Mazur.ScalarStalkJacobianTests

/-!
# Exact coupled equations from localized scalar coefficients

A coupled system over localized scalars descends to the original scalar ring.
Its equations still vanish in the full source stalk, and its residue Jacobian
stays nonsingular. Only denominator avoidance is required to construct the
coefficient maps; neither source reducedness nor a field of scalars is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedJacobianDescent
open MvPolynomial ScalarLocalizedSeparableEquations
variable {R T A B ι : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  [Fintype ι] [DecidableEq ι]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)

/-- Construct full original equations and their nonsingular residue determinant simultaneously. -/
theorem exists_equations (z : ι → A) (F : ι → MvPolynomial ι T)
    (hF : ∀ i, eval₂ (stalkMap M σ φ Q hM)
      (fun j ↦ algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
        (z j)) (F i) = 0)
    (hJ : Matrix.det (fun i j ↦ eval₂ (residueMap M σ φ Q hM)
      (fun k ↦ algebraMap B Q.asIdeal.ResidueField (φ (z k))) (pderiv j (F i))) ≠ 0) :
    ∃ P : ι → MvPolynomial ι R,
      (∀ i, algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
        (eval₂ σ z (P i)) = 0) ∧
      Matrix.det (Matrix.map (fun i j ↦ eval₂ σ z (pderiv j (P i)))
        ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0 := by
  obtain ⟨b, P, hP, hdet⟩ := ScalarLocalizedJacobianClearing.exists_system M
    (residueMap M σ φ Q hM)
    (fun k ↦ algebraMap B Q.asIdeal.ResidueField (φ (z k))) F hJ
  refine ⟨P, ?_, ?_⟩
  · intro i
    rw [hom_eval₂, ← stalkMap_comp (T := T) M σ φ Q hM,
      ScalarLocalizedMvPolynomialClearing.eval_multiple M _ _ (b i) (P i) (F i) (hP i),
      hF i, mul_zero]
  · rw [residueMap_comp] at hdet
    have he : Matrix.map (fun i j ↦ eval₂ σ z (pderiv j (P i)))
        ((algebraMap B Q.asIdeal.ResidueField).comp φ) =
        (fun i j ↦ eval₂ (((algebraMap B Q.asIdeal.ResidueField).comp φ).comp σ)
          (fun k ↦ algebraMap B Q.asIdeal.ResidueField (φ (z k))) (pderiv j (P i))) := by
      funext i j
      exact hom_eval₂ (pderiv j (P i)) σ
        ((algebraMap B Q.asIdeal.ResidueField).comp φ) z
    rw [he]
    exact hdet

end FLT.Mazur.ScalarLocalizedJacobianDescent
