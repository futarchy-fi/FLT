/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteParameterCarry
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Rational coordinates of arbitrary characters of a cyclic group

A generator is chosen from cyclicity. Every finite character is then a
natural multiple of the resulting faithful rational-circle character.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (G : Type) [Group G] [Finite G] [IsCyclic G]

/-- A cyclic coordinate constructed from cyclicity, with the actual group order. -/
def cyclicGroupCoordinate : G ≃* Multiplicative (ZMod (Nat.card G)) :=
  (zmodCyclicMulEquiv (inferInstance : IsCyclic G)).symm

variable {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))

/-- Every finite character has a rational scalar coordinate relative to this generator. -/
theorem cyclicCharacter_rational_multiple :
    ∃ m : ℕ, ∀ g : G, zmodToRatCircle n (χ g).toAdd =
      m • zmodToRatCircle (Nat.card G) ((cyclicGroupCoordinate G) g).toAdd := by
  let e := cyclicGroupCoordinate G
  let g := e.symm (Multiplicative.ofAdd 1)
  have ht : Nat.card G • zmodToRatCircle n (χ g).toAdd = 0 := by
    rw [← map_nsmul]
    have hg := congrArg (fun a => (χ a).toAdd) (pow_card_eq_one' (x := g))
    simpa only [map_pow, map_one, toAdd_pow,
      toAdd_one, map_zero] using congrArg (zmodToRatCircle n) hg
  obtain ⟨z, hz⟩ := (mem_range_zmodToRatCircle (Nat.card G) _).mpr ht
  refine ⟨z.val, ?_⟩
  intro a
  obtain ⟨i, hi⟩ := e.symm.surjective a
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective i.toAdd
  have hai : a = g ^ j := by
    apply e.injective
    rw [map_zpow]
    change e a = (e (e.symm (Multiplicative.ofAdd 1))) ^ j
    rw [e.apply_symm_apply, ← hi, e.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    simpa using hj.symm
  rw [hai, map_zpow, toAdd_zpow, map_zsmul]
  change _ = z.val • zmodToRatCircle (Nat.card G) (e (g ^ j)).toAdd
  rw [map_zpow]
  change _ = z.val • zmodToRatCircle (Nat.card G)
    (e (e.symm (Multiplicative.ofAdd 1)) ^ j).toAdd
  rw [e.apply_symm_apply, toAdd_zpow, map_zsmul, ← hz]
  have hzv : zmodToRatCircle (Nat.card G) z =
      z.val • zmodToRatCircle (Nat.card G) 1 := by
    rw [← map_nsmul]
    congr 1
    simp
  rw [hzv, smul_comm]
  rfl

end LocalClassFieldTheory
