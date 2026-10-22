/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalPolynomialTests

/-!
# Polynomial rigidity with differential generation only in the source stalk

The selected differentials need generate only after localization at the inverse
image of the test prime. Their separable local equations make their derivatives
units, hence kill the entire localized differential module. Finite source
differentials then give a global annihilator avoiding the test prime.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarStalkDifferentialPolynomialRigidity
open Polynomial
variable {R A B ι : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]

/-- A source-stalk equation with separable residue has a unit evaluated derivative in that stalk. -/
theorem derivative_isUnit (φ : A →+* B) (Q : PrimeSpectrum B) (z : A) (P : R[X])
    (h : ScalarLocalPolynomialTests.Equation (algebraMap R A) φ Q z P) :
    IsUnit (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (aeval z P.derivative)) := by
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
    (PrimeSpectrum.comap φ Q).asIdeal.primeCompl
    (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) _).mp h.1
  have hn := ScalarLocalPolynomialResidueRigidity.cleared_derivative_not_mem
    φ Q z t P ht t.property h.2
  have hd : φ (aeval z P.derivative) ∉ Q.asIdeal := by
    intro hd
    apply hn
    rw [map_mul]
    exact Q.asIdeal.mul_mem_left _ hd
  exact IsLocalization.map_units (M := (PrimeSpectrum.comap φ Q).asIdeal.primeCompl)
    (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) ⟨_, hd⟩

/-- Local differential generation and separable local equations prove actual stalk rigidity. -/
theorem isUnramifiedAt (φ : A →+* B) (Q : PrimeSpectrum B)
    (z : ι → A) (P : ι → R[X])
    (hz : Submodule.span (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (Set.range fun i ↦ KaehlerDifferential.D R
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) (z i))) = ⊤)
    (hP : ∀ i, ScalarLocalPolynomialTests.Equation (algebraMap R A) φ Q (z i) (P i)) :
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal := by
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  have he (i : ι) (F : R[X]) : aeval (algebraMap A L (z i)) F =
      algebraMap A L (aeval (z i) F) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom R A L) (z i) F
  have hd (i : ι) : KaehlerDifferential.D R L (algebraMap A L (z i)) = 0 := by
    have h := ScalarDifferentialPolynomialAnnihilator.derivative_smul_d_eq_zero
      (algebraMap A L (z i)) (P i) (by rw [he]; exact (hP i).1)
    rw [he] at h
    exact (derivative_isUnit φ Q (z i) (P i) (hP i)).smul_eq_zero.mp h
  have h1 : (1 : L) ∈ Module.annihilator L (KaehlerDifferential R L) := by
    apply ScalarFiniteDifferentialGenerators.mem_annihilator
      (fun i ↦ algebraMap A L (z i)) hz
    intro i
    simpa only [one_smul] using hd i
  exact (Algebra.formallyUnramified_iff R L).mpr
    (Module.annihilator_eq_top_iff.mp ((Ideal.eq_top_iff_one _).mpr h1))

/-- Finite source differentials spread the stalk rigidity to an actual avoiding annihilator. -/
theorem exists_annihilator [Module.Finite A (KaehlerDifferential R A)]
    (φ : A →+* B) (Q : PrimeSpectrum B) (z : ι → A) (P : ι → R[X])
    (hz : Submodule.span (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (Set.range fun i ↦ KaehlerDifferential.D R
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) (z i))) = ⊤)
    (hP : ∀ i, ScalarLocalPolynomialTests.Equation (algebraMap R A) φ Q (z i) (P i)) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  have h : PrimeSpectrum.comap φ Q ∈ Algebra.unramifiedLocus R A :=
    isUnramifiedAt φ Q z P hz hP
  rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus] at h
  exact Set.not_subset.mp h

end FLT.Mazur.ScalarStalkDifferentialPolynomialRigidity

namespace FLT.Mazur.ScalarStalkPolynomialTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Local equations whose chosen source elements generate only the stalk differentials. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  ∃ (n : ℕ) (z : Fin n → A) (P : Fin n → Polynomial R),
    Submodule.span L (Set.range fun i ↦
      KaehlerDifferential.D R L (algebraMap A L (z i))) = ⊤ ∧
    ∀ i, ScalarLocalPolynomialTests.Equation σ φ Q (z i) (P i)

/-- Finite relative differentials turn stalk generator tests into source annihilators. -/
theorem exists_annihilator (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  let _ := hfg
  obtain ⟨n, z, P, hz, hP⟩ := h
  exact ScalarStalkDifferentialPolynomialRigidity.exists_annihilator φ Q z P hz hP

end FLT.Mazur.ScalarStalkPolynomialTests
