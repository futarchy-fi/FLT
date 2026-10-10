/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace

/-!
# Constructibility from nonempty open pieces of irreducible closed subsets

Noetherian induction reduces constructibility to a constructible piece on a
nonempty relative open in each irreducible closed subset.
-/

public section
open Topology TopologicalSpace Set
namespace FLT.Mazur.Approximation

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (A : Set X)

/-- Constructible generic pieces on all irreducible closed subsets suffice. -/
theorem isConstructible_of_irreducible_closed_pieces
    (h : ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
      ∃ U : Set X, IsOpen U ∧ ((Z : Set X) ∩ U).Nonempty ∧
        IsConstructible (A ∩ Z ∩ U)) : IsConstructible A := by
  have hall (Z : Closeds X) : IsConstructible (A ∩ Z) := by
    apply wellFounded_lt.induction Z
    intro Z ih
    rcases eq_or_ne Z ⊥ with rfl | hne
    · simpa only [Closeds.coe_bot, inter_empty] using IsConstructible.empty (X := X)
    by_cases hirr : IsPreirreducible (Z : Set X)
    · obtain ⟨U, hU, ⟨x, hxZ, hxU⟩, hpiece⟩ :=
        h Z ⟨Closeds.coe_nonempty.mpr hne, hirr⟩
      let W : Closeds X := ⟨(Z : Set X) ∩ Uᶜ, Z.isClosed.inter hU.isClosed_compl⟩
      have hW : W < Z := by
        apply lt_of_le_of_ne (show W ≤ Z from inter_subset_left)
        intro heq
        have hxW : x ∈ W := by rw [heq]; exact hxZ
        exact hxW.2 hxU
      have hw := ih W hW
      have heq : A ∩ (Z : Set X) = (A ∩ Z ∩ U) ∪ (A ∩ W) := by
        ext y
        change (y ∈ A ∧ y ∈ Z) ↔
          ((y ∈ A ∧ y ∈ Z) ∧ y ∈ U) ∨ (y ∈ A ∧ y ∈ Z ∧ y ∉ U)
        tauto
      rw [heq]
      exact hpiece.union hw
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hirr
      obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hn₁, hn₂⟩ := hirr
      let Z₁ : Closeds X := ⟨z₁, hz₁⟩
      let Z₂ : Closeds X := ⟨z₂, hz₂⟩
      have h₁ := ih (Z ⊓ Z₁) (inf_lt_left.mpr (show ¬ Z ≤ Z₁ from hn₁))
      have h₂ := ih (Z ⊓ Z₂) (inf_lt_left.mpr (show ¬ Z ≤ Z₂ from hn₂))
      have heq : A ∩ (Z : Set X) =
          (A ∩ ((Z ⊓ Z₁ : Closeds X) : Set X)) ∪
            (A ∩ ((Z ⊓ Z₂ : Closeds X) : Set X)) := by
        ext x
        change (x ∈ A ∧ x ∈ Z) ↔
          (x ∈ A ∧ x ∈ Z ∧ x ∈ z₁) ∨ (x ∈ A ∧ x ∈ Z ∧ x ∈ z₂)
        have hc : x ∈ Z → x ∈ z₁ ∨ x ∈ z₂ := fun hx ↦ hcover hx
        tauto
      rw [heq]
      exact h₁.union h₂
  simpa only [Closeds.coe_top, inter_univ] using hall ⊤

end FLT.Mazur.Approximation
