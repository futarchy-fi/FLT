/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedJacobianTests
public import FLT.Mazur.ScalarUnramifiedBaseDifferentials

/-!
# Coupled equations from a presentation of the full source stalk

The full source stalk need only be generated over the avoiding scalar
localization. Scalar localization contributes no differentials, so these
coordinates span differentials over the exact original scalar ring. Clearing
their coupled equations constructs rigidity without global algebra generators.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedStalkPresentation
open ScalarLocalizedSeparableEquations
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)
  (n : ℕ) (z : Fin n → A) (F : Fin n → MvPolynomial (Fin n) T)
  (hz : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
    Algebra.adjoin T (Set.range fun i ↦
      algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) (z i)) = ⊤)
  (hF : ∀ i, MvPolynomial.eval₂ (stalkMap M σ φ Q hM)
    (fun j ↦ algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (z j)) (F i) = 0)
  (hJ : Matrix.det (fun i j ↦ MvPolynomial.eval₂ (residueMap M σ φ Q hM)
    (fun k ↦ algebraMap B Q.asIdeal.ResidueField (φ (z k)))
    (MvPolynomial.pderiv j (F i))) ≠ 0)

include hz hF hJ in
/-- A localized-scalar presentation of the full stalk constructs the original differential test. -/
theorem condition : ScalarLocalizedJacobianTests.Condition (T := T) M σ φ Q := by
  let _ := σ.toAlgebra
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
  let _ : IsScalarTower R T L :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_comp (T := T) M σ φ Q hM).symm
  let _ : Algebra.FormallyUnramified R T := Algebra.FormallyUnramified.of_isLocalization M
  refine ⟨hM, n, z, F, ?_, hF, hJ⟩
  exact ScalarUnramifiedBaseDifferentials.span_eq_top
    (R := R) (fun i ↦ algebraMap A L (z i)) hz

include hz hF hJ in
/-- The full-stalk presentation proves unramifiedness without source differential finiteness. -/
theorem isUnramifiedAt :
    let _ := σ.toAlgebra
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal :=
  ScalarLocalizedJacobianTests.isUnramifiedAt M σ φ Q
    (condition M σ φ Q hM n z F hz hF hJ)

include hz hF hJ in
/-- Finite source differentials spread the constructed stalk presentation to an original open. -/
theorem exists_principal
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A)) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) :=
  ScalarLocalizedJacobianTests.exists_principal M σ φ Q hfg
    (condition M σ φ Q hM n z F hz hF hJ)

end FLT.Mazur.ScalarLocalizedStalkPresentation
