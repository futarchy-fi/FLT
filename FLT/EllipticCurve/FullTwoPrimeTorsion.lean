/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Orders extracted from full two-torsion and cyclic torsion

An embedded `(ℤ/2ℤ)² × ℤ/nℤ` supplies points of orders `n` and, when
`n` is coprime to two, `2 * n`. These elementary reductions do not require
an elliptic curve or a bound on its rational torsion.
-/

@[expose] public section

namespace FLT

/-- The last factor of an embedded full-two-times-cyclic group supplies
an element of the specified order. -/
theorem addOrderOf_fullTwoPrime_last {A : Type*} [AddCommGroup A] {n : ℕ}
    (f : ((ZMod 2 × ZMod 2) × ZMod n) →+ A) (hf : Function.Injective f) :
    addOrderOf (f (0, 1)) = n := by
  rw [addOrderOf_injective f hf]
  simp [Prod.addOrderOf, ZMod.addOrderOf_one]

/-- Combining one two-torsion generator with the cyclic generator gives
an element of order `2 * n` when the orders are coprime. -/
theorem addOrderOf_fullTwoPrime_mixed {A : Type*} [AddCommGroup A] {n : ℕ}
    (hn : Nat.Coprime 2 n)
    (f : ((ZMod 2 × ZMod 2) × ZMod n) →+ A) (hf : Function.Injective f) :
    addOrderOf (f ((1, 0), 1)) = 2 * n := by
  rw [addOrderOf_injective f hf]
  simpa [Prod.addOrderOf, ZMod.addOrderOf_one] using hn.lcm_eq_mul

end FLT
