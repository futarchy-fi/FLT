/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateInvariantClass
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Cardinality annihilation and valid cancellation in Tate degree zero

The group order kills every norm-quotient class. Multiplication by a number
coprime to that order is therefore injective, without torsion-free assumptions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)

/-- The order of the group annihilates every actual degree-zero Tate class. -/
theorem tateZero_card_nsmul (x : tateCohomology M 0) : Nat.card G • x = 0 := by
  obtain ⟨a, rfl⟩ := tateInvariantClass_surjective M x
  rw [← map_nsmul (tateInvariantClass M).hom]
  apply (tateInvariantClass_eq_zero_iff M _).mpr
  refine ⟨a.val, ?_⟩
  change (∑ g : G, M.ρ g) a.val = Nat.card G • a.val
  have ha (g : G) : M.ρ g a.val = a.val := a.property g
  simp only [LinearMap.sum_apply, ha, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- A class killed by another integer is killed by its gcd with the group order. -/
theorem tateZero_gcd_nsmul (m : ℕ) (x : tateCohomology M 0) (hx : m • x = 0) :
    Nat.gcd m (Nat.card G) • x = 0 := by
  exact (addOrderOf_dvd_iff_nsmul_eq_zero).mp
    (Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hx)
      (addOrderOf_dvd_of_nsmul_eq_zero (tateZero_card_nsmul M x)))

/-- Multiplication by an integer coprime to the group order can be cancelled. -/
theorem tateZero_nsmul_injective (m : ℕ) (hm : m.Coprime (Nat.card G)) :
    Function.Injective (fun x : tateCohomology M 0 => m • x) := by
  intro x y h
  change m • x = m • y at h
  have hd : m • (x - y) = 0 := by rw [smul_sub, h, sub_self]
  have hg := tateZero_gcd_nsmul M m (x - y) hd
  rw [hm.gcd_eq_one, one_smul, sub_eq_zero] at hg
  exact hg

end LocalClassFieldTheory
