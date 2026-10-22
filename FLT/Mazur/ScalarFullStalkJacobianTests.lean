/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFullStalkJacobianClearing
public import FLT.Mazur.ScalarUnitJacobianRigidity
public import FLT.Mazur.ScalarLocalizedJacobianTests

/-!
# Coupled tests with arbitrary coordinates in the full source stalk

The chosen coordinates need not descend to the source ring. Exact coupled
equations and a nonsingular test-residue Jacobian kill the full stalk module.
Finite source differentials spread the result to an original principal open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFullStalkJacobianTests
open ScalarLocalizedSeparableEquations ScalarFullStalkResidue
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)

/-- Exact equations and differential spanning in the unchanged full source stalk. -/
def Condition : Prop :=
  let _ := σ.toAlgebra
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  ∃ hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal,
    ∃ (n : ℕ) (z : Fin n → L) (F : Fin n → MvPolynomial (Fin n) T),
      Submodule.span L (Set.range fun i ↦ KaehlerDifferential.D R L (z i)) = ⊤ ∧
      (∀ i, MvPolynomial.eval₂ (stalkMap M σ φ Q hM) z (F i) = 0) ∧
      Matrix.det (fun i j ↦ MvPolynomial.eval₂ (residueMap M σ φ Q hM)
        (fun k ↦ toResidue φ Q (z k)) (MvPolynomial.pderiv j (F i))) ≠ 0

/-- The previous source-coordinate tests are included with their exact residue Jacobians. -/
theorem of_source_coordinates (h : ScalarLocalizedJacobianTests.Condition (T := T) M σ φ Q) :
    Condition (T := T) M σ φ Q := by
  let _ := σ.toAlgebra
  obtain ⟨hM, n, z, F, hz, hF, hJ⟩ := h
  refine ⟨hM, n, fun i ↦ algebraMap A
    (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) (z i), F, hz, hF, ?_⟩
  simpa only [toResidue_algebraMap] using hJ

/-- Arbitrary full-stalk coordinates yield original-base unramifiedness at the test prime. -/
theorem isUnramifiedAt (h : Condition (T := T) M σ φ Q) :
    let _ := σ.toAlgebra
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal := by
  let _ := σ.toAlgebra
  obtain ⟨hM, n, z, F, hz, hF, hJ⟩ := h
  obtain ⟨P, hP, hdet⟩ :=
    ScalarFullStalkJacobianClearing.exists_equations M σ φ Q hM z F hF hJ
  exact ScalarUnitJacobianRigidity.formallyUnramified z P hz hP hdet

/-- The full-stalk equations construct a source annihilator when source differentials are finite. -/
theorem exists_annihilator
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : Condition (T := T) M σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  let _ := hfg
  have hu : PrimeSpectrum.comap φ Q ∈ Algebra.unramifiedLocus R A :=
    isUnramifiedAt M σ φ Q h
  rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus] at hu
  exact Set.not_subset.mp hu

/-- The constructed neighborhood lies in the original source, despite fractional coordinates. -/
theorem exists_principal
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : Condition (T := T) M σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨a, ha, hQa⟩ := exists_annihilator M σ φ Q hfg h
  exact ⟨a, hQa, ScalarDifferentialPrincipalRigidity.away_formallyUnramified a ha⟩

end FLT.Mazur.ScalarFullStalkJacobianTests
