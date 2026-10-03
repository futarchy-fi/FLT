/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Perfection

/-! # The integral tilt of the completed p-adic algebraic closure

Instantiate the inverse-Frobenius construction on the actual integer ring
of C_p. This supplies the coefficient ring for Fontaine's Witt vectors;
the sharp map and the Galois action remain separate constructions.
-/

@[expose] public noncomputable section
open scoped NNReal
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The prime has nontrivial valuation in C_p. -/
theorem valuation_prime_ne_one : Valued.v (p : ℂ_[p]) ≠ 1 := by
  rw [PadicComplex.valuation_p, one_div, inv_ne_one]
  exact_mod_cast (Fact.out : p.Prime).ne_one

/-- The prime is not a unit of the integer ring of C_p. -/
theorem prime_not_isUnit : ¬ IsUnit (p : 𝓞_ℂ_[p]) := by
  intro h
  have hv := (PadicComplexInt.integers p).one_of_isUnit h
  exact valuation_prime_ne_one p (by simpa only [map_natCast] using hv)

instance instFactPrimeNotIsUnit : Fact (¬ IsUnit (p : 𝓞_ℂ_[p])) :=
  ⟨prime_not_isUnit p⟩

/-- The integral tilt, the inverse limit of O_C/(p) under Frobenius. -/
abbrev IntegralTilt := PreTilt 𝓞_ℂ_[p] p

/-- Its characteristic is the original prime. -/
instance instCharPIntegralTilt : CharP (IntegralTilt p) p := inferInstance

/-- Frobenius on the actual integral tilt is bijective. -/
theorem integralTilt_frobenius_bijective :
    Function.Bijective (frobenius (IntegralTilt p) p) :=
  (frobeniusEquiv (IntegralTilt p) p).bijective

/-- The integral tilt has no zero divisors. -/
instance instIsDomainIntegralTilt : IsDomain (IntegralTilt p) :=
  PreTilt.isDomain ℂ_[p] (PadicComplex.valued p).v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p) p

/-- The valuation on the integral tilt induced by C_p. -/
def integralTiltValuation : Valuation (IntegralTilt p) ℝ≥0 :=
  PreTilt.val ℂ_[p] (PadicComplex.valued p).v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p) p

/-- This valuation detects zero. -/
theorem integralTiltValuation_eq_zero (x : IntegralTilt p) :
    integralTiltValuation p x = 0 ↔ x = 0 :=
  PreTilt.map_eq_zero (PadicComplexInt.integers p)

end PadicHodgeTheory
