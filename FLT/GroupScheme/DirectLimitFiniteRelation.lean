/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Data.Finset.Order

/-! # Finite linear relations in directed module colimits

Neither the representatives nor the transition maps need to be injective.
-/

@[expose] public noncomputable section
namespace Module.DirectLimit
variable {R ι : Type*} [CommRing R] [Preorder ι] [DecidableEq ι]
  [Nonempty ι] [IsDirectedOrder ι] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

/-- A finite tuple has representatives in a single stage. -/
theorem exists_of_finite {κ : Type*} [Finite κ] (x : κ → DirectLimit G f) :
    ∃ (i : ι) (y : κ → G i), ∀ k, of R ι G f i (y k) = x k := by
  classical
  let := Fintype.ofFinite κ
  choose i y hy using fun k ↦ exists_of (x k)
  obtain ⟨j, hj⟩ := (Finset.univ.image i).exists_le
  have hij (k) : i k ≤ j := hj _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  refine ⟨j, fun k ↦ f (i k) j (hij k) (y k), fun k ↦ ?_⟩
  rw [of_f, hy]

variable [DirectedSystem G (f · · ·)]

/-- A finite linear relation in the colimit already holds at a common stage. -/
theorem exists_of_finite_relation {κ : Type*} [Fintype κ]
    (a : κ → R) (x : κ → DirectLimit G f) (h : ∑ k, a k • x k = 0) :
    ∃ (i : ι) (y : κ → G i), (∀ k, of R ι G f i (y k) = x k) ∧
      ∑ k, a k • y k = 0 := by
  obtain ⟨i, y, hy⟩ := exists_of_finite f x
  have hz : of R ι G f i (∑ k, a k • y k) = 0 := by
    simpa only [map_sum, map_smul, hy] using h
  obtain ⟨j, hij, hj⟩ := of.zero_exact hz
  refine ⟨j, fun k ↦ f i j hij (y k), ?_, ?_⟩
  · intro k
    rw [of_f, hy]
  · simpa only [map_sum, map_smul] using hj

end Module.DirectLimit
