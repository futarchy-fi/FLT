/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedSeparableTests
public import Mathlib.FieldTheory.Perfect

/-!
# Exact scalar equations at reduced algebraic source stalks

A reduced algebra over a perfect field has squarefree minimal polynomials
for its algebraic elements. Localized scalar coefficients can therefore be
cleared to construct the exact original equations. Reducedness is required
only of the specified full source stalk; it is not inferred from its residue.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarReducedStalkEquations
open ScalarLocalizedSeparableEquations

/-- Algebraic elements of a reduced algebra over a perfect field are separable. -/
theorem isSeparable_of_reduced {K S : Type} [Field K] [PerfectField K]
    [CommRing S] [IsReduced S] [Algebra K S] (z : S) (hz : IsAlgebraic K z) :
    IsSeparable K z :=
  PerfectField.separable_iff_squarefree.mpr
    (IsRadical.squarefree (minpoly.ne_zero hz.isIntegral) (minpoly.isRadical K z))

variable {R T A B : Type} [CommRing R] [Field T] [PerfectField T]
  [CommRing A] [CommRing B] [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)
  [IsReduced (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)]

/-- A reduced full stalk and algebraicity construct an exact original scalar equation. -/
theorem exists_equation (z : A)
    (hz : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      IsAlgebraic T
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)) :
    ∃ F : Polynomial R, ScalarLocalPolynomialTests.Equation σ φ Q z F := by
  apply ScalarLocalizedSeparableEquations.exists_equation (T := T) M σ φ Q hM z
  let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
  exact isSeparable_of_reduced _ hz

/-- Finite relative differentials select exact equations at a reduced algebraic source stalk. -/
theorem test
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (ha : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      ∀ z : A, IsAlgebraic T
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)) :
    ScalarLocalPolynomialTests.Test σ φ Q := by
  apply ScalarLocalPolynomialTests.test_of_finite_differentials σ φ Q hfg
  intro z
  exact exists_equation M σ φ Q hM z (ha z)

/-- A finite reduced source stalk supplies algebraicity, hence the actual polynomial tests. -/
theorem test_of_finite
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (hf : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      Module.Finite T (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)) :
    ScalarLocalPolynomialTests.Test σ φ Q := by
  apply test (T := T) M σ φ Q hM hfg
  let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
  let _ := hf
  dsimp only
  intro z
  exact (Algebra.IsIntegral.isIntegral
    (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)).isAlgebraic

end FLT.Mazur.ScalarReducedStalkEquations
