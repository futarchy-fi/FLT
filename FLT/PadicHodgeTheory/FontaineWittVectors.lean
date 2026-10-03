/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicTilt
public import Mathlib.RingTheory.WittVector.Complete

/-! # Fontaine's integral Witt-vector ring

A_inf is constructed from the actual integral tilt of C_p. Its reduction
modulo p is the tilt. This is not the theta map to the characteristic-zero
integer ring of C_p.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Fontaine's A_inf as Witt vectors of the integral tilt. -/
abbrev Ainf := WittVector p (IntegralTilt p)

/-- Reduction modulo p recovers the integral tilt. -/
def ainfModPEquiv : Ainf p ⧸ Ideal.span {(p : Ainf p)} ≃+* IntegralTilt p :=
  WittVector.quotientPEquiv

/-- The reduction is concretely the zeroth Witt coordinate. -/
theorem ainfModPEquiv_mk (x : Ainf p) :
    ainfModPEquiv p (Ideal.Quotient.mk (Ideal.span {(p : Ainf p)}) x) =
      WittVector.constantCoeff x := rfl

/-- Every integral-tilt element is the reduction of a Witt vector. -/
theorem ainf_constantCoeff_surjective :
    Function.Surjective (WittVector.constantCoeff : Ainf p →+* IntegralTilt p) :=
  WittVector.constantCoeff_surjective p

end PadicHodgeTheory
