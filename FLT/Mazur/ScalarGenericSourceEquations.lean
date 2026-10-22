/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarReducedStalkEquations

/-!
# Constructed exact equations over the generic scalar point

At the generic point of a scalar domain, all nonzero scalar denominators
avoid the test prime. This constructs the fraction-field action on the full
source stalk. Reduced algebraic stalks over a perfect scalar fraction field
then have exact scalar equations; finite stalks supply algebraicity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarGenericSourceEquations
open ScalarLocalizedSeparableEquations
variable {R A B : Type} [CommRing R] [IsDomain R] [CommRing A] [CommRing B]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hQ : Ideal.comap (φ.comp σ) Q.asIdeal = ⊥)

include hQ in
/-- A generic scalar contraction constructs avoidance of every fraction-field denominator. -/
theorem denominators_avoid : ∀ m ∈ nonZeroDivisors R, φ (σ m) ∉ Q.asIdeal := by
  intro m hm h
  have hz : m ∈ Ideal.comap (φ.comp σ) Q.asIdeal := h
  rw [hQ] at hz
  exact nonZeroDivisors.ne_zero hm (Ideal.mem_bot.mp hz)

variable [PerfectField (FractionRing R)]
  [IsReduced (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)]

/-- Generic scalar algebraicity constructs an exact polynomial without chosen denominators. -/
theorem exists_equation (z : A)
    (hz : let _ := (stalkMap (T := FractionRing R) (nonZeroDivisors R) σ φ Q
      (denominators_avoid σ φ Q hQ)).toAlgebra
      IsAlgebraic (FractionRing R)
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)) :
    ∃ F : Polynomial R, ScalarLocalPolynomialTests.Equation σ φ Q z F :=
  ScalarReducedStalkEquations.exists_equation (nonZeroDivisors R) σ φ Q
    (denominators_avoid σ φ Q hQ) z hz

/-- A finite reduced generic source stalk constructs all finite exact scalar tests. -/
theorem test_of_finite
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (hf : let _ := (stalkMap (T := FractionRing R) (nonZeroDivisors R) σ φ Q
      (denominators_avoid σ φ Q hQ)).toAlgebra
      Module.Finite (FractionRing R)
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)) :
    ScalarLocalPolynomialTests.Test σ φ Q :=
  ScalarReducedStalkEquations.test_of_finite (nonZeroDivisors R) σ φ Q
    (denominators_avoid σ φ Q hQ) hfg hf

/-- Finite generic stalks give an actual avoiding rigidity open in the unchanged source. -/
theorem exists_principal_of_finite
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (hf : let _ := (stalkMap (T := FractionRing R) (nonZeroDivisors R) σ φ Q
      (denominators_avoid σ φ Q hQ)).toAlgebra
      Module.Finite (FractionRing R)
        (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨a, ha, hQa⟩ := ScalarLocalPolynomialTests.exists_annihilator σ φ Q
    (test_of_finite σ φ Q hQ hfg hf)
  exact ⟨a, hQa, ScalarDifferentialPrincipalRigidity.away_formallyUnramified a ha⟩

end FLT.Mazur.ScalarGenericSourceEquations
