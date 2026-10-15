/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Set.Card

/-!
# Counting retained and missing branches of a finite fiber

An injective map over a base partitions every finite target fiber into its
original source fiber and its missing branches. The resulting numerical
criterion needs neither connectedness nor a choice of branch representatives.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteFiberImageCard

universe u v w
variable {Z : Type u} {Y : Type v} {X : Type w}
  (j : Z → Y) (π : Y → X) (q : Z → X) (h : ∀ z, π (j z) = q z)

include h

/-- The retained target fiber is exactly the image of the original source fiber. -/
theorem image_fiber (x : X) :
    j '' (q ⁻¹' {x}) = (π ⁻¹' {x}) ∩ Set.range j := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(h z).trans hz, z, rfl⟩
  · rintro ⟨hy, z, rfl⟩
    exact ⟨z, (h z).symm.trans hy, rfl⟩

variable (hj : Function.Injective j) (x : X) (hx : (π ⁻¹' {x}).Finite)

include hj hx

/-- Finiteness is inherited from the target fiber, without compactness of the source. -/
theorem finite_fiber : (q ⁻¹' {x}).Finite := by
  have he : q ⁻¹' {x} = j ⁻¹' (π ⁻¹' {x}) := by
    ext z
    exact (congrArg (· = x) (h z)).symm.to_iff
  rw [he]
  exact hx.preimage hj.injOn

/-- The original fiber cannot have more points than the independent fiber. -/
theorem fiber_ncard_le : (q ⁻¹' {x}).ncard ≤ (π ⁻¹' {x}).ncard := by
  rw [← Set.ncard_image_of_injective _ hj, image_fiber j π q h x]
  exact Set.ncard_le_ncard Set.inter_subset_left hx

/-- The exact branch deficit is the number of missing points of the actual target fiber. -/
theorem missing_ncard_add :
    ((π ⁻¹' {x}) \ Set.range j).ncard + (q ⁻¹' {x}).ncard =
      (π ⁻¹' {x}).ncard := by
  rw [← Set.ncard_image_of_injective _ hj, image_fiber j π q h x, Nat.add_comm]
  exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ hx

/-- A reverse point-count bound fills every branch, even for disconnected fibers. -/
theorem fiber_subset_range_iff :
    (π ⁻¹' {x}) ⊆ Set.range j ↔ (π ⁻¹' {x}).ncard ≤ (q ⁻¹' {x}).ncard := by
  rw [← Set.ncard_image_of_injective _ hj, image_fiber j π q h x]
  constructor
  · intro hs
    rw [Set.inter_eq_self_of_subset_left hs]
  · intro hc
    have he := Set.eq_of_subset_of_ncard_le Set.inter_subset_left hc hx
    exact fun y hy ↦ (he.symm ▸ hy : y ∈ (π ⁻¹' {x}) ∩ Set.range j).2

/-- Equality of the two independently computed counts detects fullness exactly. -/
theorem fiber_subset_range_iff_eq :
    (π ⁻¹' {x}) ⊆ Set.range j ↔ (q ⁻¹' {x}).ncard = (π ⁻¹' {x}).ncard := by
  rw [fiber_subset_range_iff j π q h hj x hx]
  exact ⟨fun hc ↦ Nat.le_antisymm (fiber_ncard_le j π q h hj x hx) hc,
    fun hc ↦ hc.ge⟩

/-- Enough distinct original points fill a fiber with a known numerical upper bound. -/
theorem fiber_subset_range_of_witnesses {n : ℕ} (s : Fin n → Z)
    (hs : Function.Injective s) (hq : ∀ i, q (s i) = x)
    (hn : (π ⁻¹' {x}).ncard ≤ n) : (π ⁻¹' {x}) ⊆ Set.range j := by
  apply (fiber_subset_range_iff j π q h hj x hx).mpr
  apply hn.trans
  have hr : Set.range s ⊆ q ⁻¹' {x} := by
    rintro _ ⟨i, rfl⟩
    exact hq i
  have hc := Set.ncard_le_ncard hr (finite_fiber j π q h hj x hx)
  simpa only [Set.ncard_range_of_injective hs, Nat.card_fin] using hc

end FLT.Mazur.FiniteFiberImageCard
