/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Reduction of the p-adic cyclotomic character
-/

@[expose] public section

/-- The reduction of the p-adic cyclotomic character is the mod-p cyclotomic character. -/
theorem cyclotomicCharacter.toZMod {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)]
    (hn : Nat.card (rootsOfUnity p L) = p) (g : L ≃+* L) :
    PadicInt.toZMod (cyclotomicCharacter L p g).val =
      modularCyclotomicCharacter L hn g := by
  apply modularCyclotomicCharacter.unique L hn g
  intro t ht
  have ht' : (t : L) ^ p ^ 1 = 1 := by
    simpa only [pow_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val ((mem_rootsOfUnity p t).mp ht)
  simpa only [PadicInt.val_toZModPow_one] using
    cyclotomicCharacter.spec (L := L) p (n := 1) g (t : L) ht'
