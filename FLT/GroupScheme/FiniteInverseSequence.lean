/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem

/-! # Coherent choices from nonempty finite inverse sequences -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace ThreeAdicPlan

/-- Finite nonempty fibres admit a simultaneous coherent choice; transition
surjectivity is unnecessary. -/
theorem exists_finite_inverse_sequence (A : ℕ → Type*) [∀ n, Finite (A n)]
    [∀ n, Nonempty (A n)] (r : ∀ {m n : ℕ}, m ≤ n → A n → A m)
    (rid : ∀ n a, r (le_refl n) a = a)
    (rcomp : ∀ {l m n} (h : l ≤ m) (k : m ≤ n) a, r h (r k a) = r (h.trans k) a) :
    ∃ a : ∀ n, A n, ∀ {m n} (h : m ≤ n), r h (a n) = a m := by
  let F : ℕᵒᵖ ⥤ Type _ :=
    { obj n := A n.unop
      map h := ↾(r h.unop.le)
      map_id n := by ext a; exact rid n.unop a
      map_comp f g := by ext a; exact (rcomp g.unop.le f.unop.le a).symm }
  obtain ⟨a, ha⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n ↦ a (op n), fun {m n} h ↦ ?_⟩
  exact ha (Quiver.Hom.op (homOfLE h))
end ThreeAdicPlan
