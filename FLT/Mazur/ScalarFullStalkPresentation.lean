/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFullStalkJacobianTests
public import FLT.Mazur.ScalarUnramifiedBaseDifferentials

/-!
# Constructing coupled tests from arbitrary full-stalk presentations

A presentation over localized scalars supplies original-base differential
spanning. A surjective polynomial map supplies both the coordinates and their
generation; relations in its kernel supply the exact full-stalk equations.
No coordinates in the unlocalized source ring are required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFullStalkPresentation
open MvPolynomial ScalarLocalizedSeparableEquations ScalarFullStalkResidue
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)

/-- Full-stalk algebra generators construct the differential spanning in the coupled test. -/
theorem condition (n : ℕ)
    (z : Fin n → Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (F : Fin n → MvPolynomial (Fin n) T)
    (hz : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      Algebra.adjoin T (Set.range z) = ⊤)
    (hF : ∀ i, eval₂ (stalkMap M σ φ Q hM) z (F i) = 0)
    (hJ : Matrix.det (fun i j ↦ eval₂ (residueMap M σ φ Q hM)
      (fun k ↦ toResidue φ Q (z k)) (pderiv j (F i))) ≠ 0) :
    ScalarFullStalkJacobianTests.Condition (T := T) M σ φ Q := by
  let _ := σ.toAlgebra
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
  let _ : IsScalarTower R T L :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_comp (T := T) M σ φ Q hM).symm
  let _ : Algebra.FormallyUnramified R T := Algebra.FormallyUnramified.of_isLocalization M
  exact ⟨hM, n, z, F, ScalarUnramifiedBaseDifferentials.span_eq_top (R := R) z hz, hF, hJ⟩

/-- A surjective presentation and actual kernel relations construct the entire coupled test. -/
theorem of_surjective (n : ℕ)
    (α : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      MvPolynomial (Fin n) T →ₐ[T]
        Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (hα : Function.Surjective α) (F : Fin n → MvPolynomial (Fin n) T)
    (hF : ∀ i, α (F i) = 0)
    (hJ : Matrix.det (fun i j ↦ toResidue φ Q (α (pderiv j (F i)))) ≠ 0) :
    ScalarFullStalkJacobianTests.Condition (T := T) M σ φ Q := by
  let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
  have he (G : MvPolynomial (Fin n) T) :
      eval₂ (stalkMap M σ φ Q hM) (fun i ↦ α (X i)) G = α G :=
    DFunLike.congr_fun (aeval_unique α).symm G
  apply condition M σ φ Q hM n (fun i ↦ α (X i)) F
  · dsimp only
    rw [Algebra.adjoin_range_eq_range_aeval]
    apply (AlgHom.range_eq_top _).mpr
    intro y
    obtain ⟨G, rfl⟩ := hα y
    exact ⟨G, he G⟩
  · intro i
    rw [he, hF]
  · have hj (i j : Fin n) : eval₂ (residueMap M σ φ Q hM)
        (fun k ↦ toResidue φ Q (α (X k))) (pderiv j (F i)) =
        toResidue φ Q (α (pderiv j (F i))) := by
      rw [← ScalarFullStalkJacobianClearing.eval_toResidue, he]
    simpa only [hj] using hJ

end FLT.Mazur.ScalarFullStalkPresentation
