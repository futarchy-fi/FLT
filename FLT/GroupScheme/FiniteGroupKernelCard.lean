/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

/-! # Exactness of finite group sequences from maps and their orders -/

@[expose] public noncomputable section
namespace AddMonoidHom
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Finite B] [Finite C]

/-- An injective inclusion and surjective quotient with zero composite are exact
when the middle order is the product of the end orders. -/
theorem exact_of_card_mul (i : A →+ B) (q : B →+ C)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hz : ∀ a, q (i a) = 0) (hc : Nat.card B = Nat.card A * Nat.card C) (b : B) :
    q b = 0 ↔ ∃ a, i a = b := by
  have hle : i.range ≤ q.ker := by
    rintro _ ⟨a, rfl⟩
    exact hz a
  have hr : Nat.card i.range = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective i hi)).symm
  have hk : Nat.card q.ker * Nat.card C = Nat.card B := by
    have h := q.ker.card_mul_index
    rw [AddSubgroup.index_ker, q.range_eq_top.mpr hq, AddSubgroup.card_top] at h
    exact h
  have he : i.range = q.ker := AddSubgroup.eq_of_le_of_card_ge hle (by
    rw [hr]
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos (hk.trans hc)).le)
  change b ∈ q.ker ↔ b ∈ i.range
  rw [he]
end AddMonoidHom
