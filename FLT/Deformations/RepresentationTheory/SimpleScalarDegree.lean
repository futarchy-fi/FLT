/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The size of a derived rank-one scalar field

Compare the cardinality of the same finite module over its prime field and
over its derived scalars. No scalar-tower instance is necessary for this
cardinality argument; both actions live on the same additive group.
-/

@[expose] public noncomputable section
namespace Representation

variable {p : ℕ} [Fact p.Prime] {F W : Type*} [Field F]
  [AddCommGroup W] [Module F W] [Module (ZMod p) W] [Finite W]

/-- The scalar field of a finite line has degree equal to the prime-field dimension. -/
theorem scalar_card_eq_prime_pow_finrank (hdim : Module.finrank F W = 1) :
    Nat.card F = p ^ Module.finrank (ZMod p) W := by
  have hF := Module.natCard_eq_pow_finrank (K := F) (V := W)
  have hp := Module.natCard_eq_pow_finrank (K := ZMod p) (V := W)
  simpa [hdim, Nat.card_eq_fintype_card] using hF.symm.trans hp

/-- A rank-one factor has a prime-field-sized scalar field. -/
theorem scalar_card_of_prime_finrank_one (hdim : Module.finrank F W = 1)
    (hW : Module.finrank (ZMod p) W = 1) : Nat.card F = p := by
  rw [scalar_card_eq_prime_pow_finrank (p := p) hdim, hW, pow_one]

/-- A rank-two factor has a quadratic-sized scalar field. -/
theorem scalar_card_of_prime_finrank_two (hdim : Module.finrank F W = 1)
    (hW : Module.finrank (ZMod p) W = 2) : Nat.card F = p * p := by
  rw [scalar_card_eq_prime_pow_finrank (p := p) hdim, hW, pow_two]

end Representation
