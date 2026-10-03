/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterConstantBaseChange
public import FLT.GroupScheme.RaynaudUniversalConvolutionAlgebra
public import Mathlib.Algebra.CharP.Quotient

/-!
# Prime divisibility of universal character constants

Reduce the group-algebra computation modulo p and use functoriality.
This proves divisibility in the coefficient ring itself, not merely
vanishing in its residue field. The assertion that the quotient is a
unit requires a further calculation.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]

/-- Every p-fold universal constant is divisible by the characteristic of the scalar field. -/
theorem prime_dvd_constant (p : ℕ) [Fact p.Prime] [CharP F p]
    (χ ψ : Fˣ →* Rˣ) : (p : R) ∣ constant χ ψ p := by
  by_cases hp : IsUnit (p : R)
  · exact hp.dvd
  let I : Ideal R := Ideal.span {(p : R)}
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  let : CharP (R ⧸ I) p := CharP.quotient R p hp
  let : Invertible (Fintype.card Fˣ : R ⧸ I) :=
    (Invertible.map f (Fintype.card Fˣ : R)).copy _ (map_natCast f _).symm
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (constant χ ψ p) = 0
  rw [map_constant, constant_char]

/-- The universal constant has an actual integral quotient by p. -/
theorem exists_constant_eq_prime_mul (p : ℕ) [Fact p.Prime] [CharP F p]
    (χ ψ : Fˣ →* Rˣ) : ∃ u : R, constant χ ψ p = (p : R) * u :=
  prime_dvd_constant p χ ψ

end ThreeAdicPlan.CharacterAverage
