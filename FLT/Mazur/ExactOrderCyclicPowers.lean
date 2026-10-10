/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Powers indexed by a finite cyclic group

An element of exact order n gives an injective homomorphism from the cyclic
group of order n. Natural-number labels evaluate to the original powers.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.ExactOrderCyclicPowers

variable {G : Type*} [Group G] {n : ℕ} [NeZero n] (P : G) (ho : orderOf P = n)

/-- The homomorphism sends a residue-class label to the corresponding power. -/
def powersHom : Multiplicative (ZMod n) →* G where
  toFun i := P ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change P ^ (i.toAdd + j.toAdd).val = P ^ i.toAdd.val * P ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    simpa only [ho] using pow_mod_orderOf P (i.toAdd.val + j.toAdd.val)

/-- Natural-number labels recover every original power, including the generator. -/
theorem powersHom_natCast (k : ℕ) :
    powersHom P ho (Multiplicative.ofAdd (k : ZMod n)) = P ^ k := by
  change P ^ (k : ZMod n).val = P ^ k
  rw [ZMod.val_natCast]
  simpa only [ho] using pow_mod_orderOf P k

/-- Exact order makes the cyclic power homomorphism injective. -/
theorem powersHom_injective : Function.Injective (powersHom P ho) := by
  intro i j h
  have hi : i.toAdd.val < orderOf P := by simpa only [ho] using ZMod.val_lt i.toAdd
  have hj : j.toAdd.val < orderOf P := by simpa only [ho] using ZMod.val_lt j.toAdd
  have he : i.toAdd.val = j.toAdd.val := pow_injOn_Iio_orderOf hi hj h
  exact congrArg Multiplicative.ofAdd (ZMod.val_injective n he)

end FLT.Mazur.ExactOrderCyclicPowers
