/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sets

/-!
# A bounded common enumeration of two finite injective families

Enumerate the union of the actual values. Both original label sets embed in this
finite enumeration, and together exhaust it. No completeness of either family is
required, and overlapping values are identified rather than duplicated.
-/

@[expose] public noncomputable section
namespace FLT.Mazur

/-- Two finite injective families have a jointly exhaustive bounded common enumeration. -/
theorem finite_joint_frame_enumeration {I J X : Type*} [Fintype I] [Fintype J]
    (a : I → X) (b : J → X) (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ (n : ℕ) (_ : n ≤ Fintype.card I + Fintype.card J)
      (α : I ↪ Fin n) (β : J ↪ Fin n) (t : Fin n ↪ X),
      (∀ i, t (α i) = a i) ∧ (∀ j, t (β j) = b j) ∧
      (∀ k, (∃ i, α i = k) ∨ ∃ j, β j = k) := by
  classical
  let f : I ⊕ J → X := Sum.elim a b
  let U := Set.range f
  let _ : Fintype U := Fintype.ofSurjective (fun x ↦ (⟨f x, ⟨x, rfl⟩⟩ : U)) (by
    rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩)
  let r : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let l : I ↪ U := ⟨fun i ↦ ⟨a i, ⟨Sum.inl i, rfl⟩⟩, fun _ _ h ↦
    ha (congrArg Subtype.val h)⟩
  let s : J ↪ U := ⟨fun j ↦ ⟨b j, ⟨Sum.inr j, rfl⟩⟩, fun _ _ h ↦
    hb (congrArg Subtype.val h)⟩
  let t : Fin (Fintype.card U) ↪ X := r.symm.toEmbedding.trans ⟨Subtype.val,
    Subtype.val_injective⟩
  refine ⟨Fintype.card U, ?_, l.trans r.toEmbedding, s.trans r.toEmbedding, t,
    ?_, ?_, ?_⟩
  · exact (Fintype.card_range_le f).trans (by rw [Fintype.card_sum])
  · intro i
    exact congrArg Subtype.val (r.symm_apply_apply (l i))
  · intro j
    exact congrArg Subtype.val (r.symm_apply_apply (s j))
  · intro k
    obtain ⟨x, hx⟩ := (r.symm k).property
    cases x with
    | inl i =>
      left
      refine ⟨i, ?_⟩
      change r (l i) = k
      rw [← r.apply_symm_apply k]
      exact congrArg r (Subtype.ext hx)
    | inr j =>
      right
      refine ⟨j, ?_⟩
      change r (s j) = k
      rw [← r.apply_symm_apply k]
      exact congrArg r (Subtype.ext hx)

end FLT.Mazur
