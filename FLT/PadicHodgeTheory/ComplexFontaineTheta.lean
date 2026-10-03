/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerAdic
public import FLT.PadicHodgeTheory.ComplexIntegerFrobenius
public import FLT.PadicHodgeTheory.FontaineWittVectors
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-! # Sharp and Fontaine theta for the actual completed algebraic closure -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The multiplicative sharp map from the actual integral tilt to O_C. -/
def complexSharp : IntegralTilt p →* 𝓞_ℂ_[p] := PreTilt.untilt

/-- Sharp reduces to the zeroth inverse-Frobenius coordinate. -/
theorem complexSharp_modP (x : IntegralTilt p) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p])}) (complexSharp p x) =
      PreTilt.coeff 0 x :=
  PreTilt.mk_untilt_eq_coeff_zero x

/-- Fontaine's theta map on the Witt vectors of the actual integral tilt. -/
def complexTheta : Ainf p →+* 𝓞_ℂ_[p] := WittVector.fontaineTheta _ p

/-- On Teichmuller representatives, theta is the sharp map. -/
theorem complexTheta_teichmuller (x : IntegralTilt p) :
    complexTheta p (WittVector.teichmuller p x) = complexSharp p x :=
  WittVector.fontaineTheta_teichmuller x

/-- Theta modulo p is evaluation of the zeroth Witt and tilt coordinates. -/
theorem complexTheta_modP (x : Ainf p) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p])}) (complexTheta p x) =
      PreTilt.coeff 0 (x.coeff 0) :=
  WittVector.mk_fontaineTheta x

/-- Surjectivity follows from actual Frobenius surjectivity and p-adic completeness. -/
theorem complexTheta_surjective : Function.Surjective (complexTheta p) :=
  surjective_fontaineTheta (complexInteger_frobenius_surjective p)

end PadicHodgeTheory
