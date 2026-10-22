/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalJacobianAnnihilator
public import FLT.Mazur.ScalarStalkDifferentialPolynomialRigidity

/-!
# Coupled equations with differential generation only in the source stalk

A residue Jacobian determinant which avoids the test prime becomes a unit in
the source stalk. The adjugate kills its differential generators, hence the
whole stalk module. Finite source differentials spread this to an annihilator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarStalkDifferentialJacobianRigidity
open MvPolynomial ScalarDifferentialJacobianAnnihilator
variable {R A B ι : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

/-- A nonsingular residue Jacobian and local spanning prove source-stalk rigidity. -/
theorem isUnramifiedAt (φ : A →+* B) (Q : PrimeSpectrum B)
    (z : ι → A) (P : ι → MvPolynomial ι R)
    (hz : Submodule.span (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (Set.range fun i ↦ KaehlerDifferential.D R
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) (z i))) = ⊤)
    (hP : ∀ i, algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (aeval z (P i)) = 0)
    (hJ : Matrix.det (Matrix.map (fun i j ↦ aeval z (pderiv j (P i)))
      ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0) :
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal := by
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  let N : Matrix ι ι A := fun i j ↦ aeval z (pderiv j (P i))
  have hu : IsUnit (algebraMap A L N.det) :=
    IsLocalization.map_units (M := (PrimeSpectrum.comap φ Q).asIdeal.primeCompl)
      L ⟨N.det, determinant_not_mem φ Q N hJ⟩
  have he (F : MvPolynomial ι R) :
      aeval (fun i ↦ algebraMap A L (z i)) F = algebraMap A L (aeval z F) := by
    exact (comp_aeval_apply z (IsScalarTower.toAlgHom R A L) F).symm
  have hd (i : ι) :
      KaehlerDifferential.D R L (algebraMap A L (z i)) = 0 := by
    apply hu.smul_eq_zero.mp
    rw [(algebraMap A L).map_det]
    apply det_smul_eq_zero _ (fun j ↦
      KaehlerDifferential.D R L (algebraMap A L (z j))) _ i
    intro j
    have h := congrArg (KaehlerDifferential.D R L) (hP j)
    rw [← he, map_aeval_sum, map_zero] at h
    change (∑ k, algebraMap A L (aeval z (pderiv k (P j))) •
      KaehlerDifferential.D R L (algebraMap A L (z k))) = 0
    simpa only [he] using h
  have h1 : (1 : L) ∈ Module.annihilator L (KaehlerDifferential R L) := by
    apply ScalarFiniteDifferentialGenerators.mem_annihilator
      (fun i ↦ algebraMap A L (z i)) hz
    intro i
    simpa only [one_smul] using hd i
  exact (Algebra.formallyUnramified_iff R L).mpr
    (Module.annihilator_eq_top_iff.mp ((Ideal.eq_top_iff_one _).mpr h1))

/-- Finite source differentials spread the coupled stalk equations to an avoiding annihilator. -/
theorem exists_annihilator [Module.Finite A (KaehlerDifferential R A)]
    (φ : A →+* B) (Q : PrimeSpectrum B) (z : ι → A) (P : ι → MvPolynomial ι R)
    (hz : Submodule.span (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (Set.range fun i ↦ KaehlerDifferential.D R
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) (z i))) = ⊤)
    (hP : ∀ i, algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (aeval z (P i)) = 0)
    (hJ : Matrix.det (Matrix.map (fun i j ↦ aeval z (pderiv j (P i)))
      ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  have h : PrimeSpectrum.comap φ Q ∈ Algebra.unramifiedLocus R A :=
    isUnramifiedAt φ Q z P hz hP hJ
  rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus] at h
  exact Set.not_subset.mp h

end FLT.Mazur.ScalarStalkDifferentialJacobianRigidity
